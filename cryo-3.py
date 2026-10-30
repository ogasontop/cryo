#!/usr/bin/env python3
"""
Cryo (cryo.py) - cold data finder for ONTAP NAS volumes, with a browser GUI.

Built for air-gapped Linux servers:
  * Python 3.6+ standard library only (no pip, no Flask, no requests)
  * The GUI is one embedded page: no CDN, no web fonts, no external calls
  * Credentials live in memory only and are never written to disk

Run:
    python3 cryo.py                       # http://127.0.0.1:8080
    python3 cryo.py --host 0.0.0.0 --token 'long-random-string' \
        --certfile server.crt --keyfile server.key

Then open the URL in a browser (or tunnel: ssh -L 8080:127.0.0.1:8080 user@server).
Every scan writes two files to ./scans (change with --outdir): a CSV with every cold file, and
a SQLite database with the same rows that the Files tab sorts, filters and pages through.

What can be scanned (the "scope")
---------------------------------
* One volume          the original behaviour, with an optional start folder
* Selected volumes    volumes ticked in a list
* One SVM             every eligible volume of one SVM
* Whole cluster       every eligible volume of the cluster
The files API works one volume at a time, so a multi-volume scan simply scans the volumes one
after another, each from its own root, using the same "Workers" setting. In the SVM and
cluster scopes these volumes are skipped by default: SVM root volumes, volumes that are not
online, FlexGroup constituents, system (MDV_) volumes, and SnapMirror destination (DP)
volumes, whose data is a copy of another volume and would be counted twice. A volume you pick
yourself (one volume or selected volumes) is always scanned.

How this file is organised (top to bottom)
------------------------------------------
 1. Constants ............ what to skip, which fields to ask ONTAP for, the age buckets
 2. ONTAP REST client .... class Ontap - HTTPS, basic authentication, retries, paging
 3. Small helpers ........ path encoding, file type, timestamp parsing, CSV safety
 4. Scan engine .......... class Scan - volumes, work queue, workers, counters, CSV, SQLite
                              class SavedScan - a finished scan reopened from its database
 5. HTTP server .......... class Handler - serves the page and the JSON API
 6. Embedded GUI ......... PAGE: one HTML string holding the CSS and the JavaScript
 7. main() ............... command line options, TLS for the GUI, start-up warnings

How the pieces talk to each other
---------------------------------
    Browser --JSON over HTTP(S)--> Handler --> Scan (threads) --HTTPS GET--> ONTAP

The browser never talks to ONTAP. Only the scan host does, and it only ever sends GET
requests. Only "Test connection", "Load volumes" and "Start scan" cause requests to ONTAP.
Sorting, filtering, paging, charts and CSV downloads read results that are already held in
memory or in the scan's database file, so they never trigger a rescan.

Threads and locking
-------------------
* The HTTP server uses one thread per browser request (ThreadingMixIn).
* A scan runs in one background thread, which starts N worker threads (N = "Workers").
* Everything the threads share (counters, queue accounting, the CSV writer and the database
  connection used for writing) is changed only while holding Scan.lock, in short bursts. The slow work, the REST
  calls to ONTAP, is done OUTSIDE the lock, so a slow cluster never freezes the GUI.
* The Files tab reads the database through its own short-lived connections (the database is in
  WAL mode, so reading never blocks the scan that is writing).
* App.lock only stops two quick clicks from starting two scans at once.

Security summary (the PDF guide lists the full controls and the known gaps)
---------------------------------------------------------------------------
* Read-only: only HTTP GET is ever sent to ONTAP.
* The cluster password lives in memory only, inside the Ontap client held by the current
  Scan. It is never written to disk, never put in the CSV or the database and never sent back
  to the browser. The CSV and database hold file paths, which are sensitive, so both are
  created readable by the owner only (where the operating system supports it).
* Certificates are verified by default. "skip" exists for testing and should not be used in
  production.
* --token protects every API route. Use --certfile/--keyfile or an SSH tunnel so the
  password and the token do not cross the network in clear text.
"""
import argparse
import base64
import csv
import json
import os
import queue
import re
import sqlite3
import ssl
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, HTTPServer
from socketserver import ThreadingMixIn

# Directory entries that are never scanned or counted. "." and ".." appear in ONTAP listings.
# ".snapshot" and "~snapshot" are the snapshot folders: walking them would multiply the work
# by the number of snapshots and would give misleading ages.
SKIP = {".", "..", ".snapshot", "~snapshot"}
# The properties requested for every directory entry. Asking for only these keeps responses
# small. bytes_used is the space really consumed (sparse files, compression); size is the
# logical length. Timestamps are requested explicitly because they are not always returned
# by default.
FIELDS = "name,type,size,bytes_used,accessed_time,modified_time"
# Cold files are no longer held in memory. Each one is written to the scan's SQLite database
# as it is found, so the Files tab has no row limit (and the CSV always has every row too).
# How many failed-folder messages are stored. The total count of errors is always kept.
MAX_ERRORS_KEPT = 500
# Safety limit on distinct (volume, folder) groups kept for the "largest cold folders" views.
# Past this, further new folders are lumped into one "(other)" group per volume. At the default
# folder depth of 2 this limit is never reached.
MAX_DIR_KEYS = 100000
# How many volumes each status answer lists (the ones with the most cold data), and how many
# skipped volumes are listed. The totals are always exact; only these lists are shortened.
MAX_VOLS_IN_STATUS = 100
MAX_SKIPPED_LISTED = 200
# Age buckets for the Summary and Charts tabs: (label, upper limit in days). A file goes into
# the first bucket whose limit is above its age. None means "no upper limit".
BUCKETS = [("under 1 year", 365), ("1-2 years", 730), ("2-3 years", 1095),
           ("3-5 years", 1825), ("over 5 years", None)]


# --------------------------------------------------------------------------
# ONTAP REST client (urllib only)
# --------------------------------------------------------------------------
class ApiError(Exception):
    """An ONTAP request failed.

    `code` is the HTTP status (401 bad login, 403 no permission, 404 not found, ...), or 0 when
    there was no HTTP answer at all (DNS failure, connection refused, timeout, TLS problem).
    """
    def __init__(self, code, msg):
        super().__init__("HTTP %s: %s" % (code, msg) if code else msg)
        self.code = code


class Ontap:
    """Minimal read-only client for the ONTAP REST API, built on urllib (standard library).

    One instance holds the cluster address, the basic-authentication header (which contains the
    password, in memory only) and the TLS settings. It is created from the values typed into the
    GUI and is never written to disk. Every method here issues GET requests only.
    """
    def __init__(self, host, user, password, tls="verify", ca=None, timeout=60):
        host = host.strip().rstrip("/")
        # A bare name such as cluster-mgmt.example.local gets https:// put in front of it.
        if "://" not in host:
            host = "https://" + host
        self.base = host
        # HTTP basic authentication: base64 of "user:password". This is only safe over TLS.
        token = base64.b64encode(("%s:%s" % (user, password)).encode()).decode()
        self.headers = {"Authorization": "Basic " + token, "Accept": "application/json"}
        # TLS modes:
        #   skip   - no certificate or host name checks (testing only, never in production)
        #   ca     - trust only the given CA file (best for a private internal CA)
        #   other  - trust the operating system's CA store (default)
        if tls == "skip":
            ctx = ssl.create_default_context()
            ctx.check_hostname = False
            ctx.verify_mode = ssl.CERT_NONE
        elif tls == "ca" and ca:
            ctx = ssl.create_default_context(cafile=ca)
        else:
            ctx = ssl.create_default_context()
        self.ctx = ctx
        self.timeout = timeout

    def get(self, path, params=None, retries=4):
        """GET a path (or a full URL) and return the parsed JSON.

        Retries up to `retries` times, waiting 1, 2, 4, then 8 seconds, for throttling (429),
        server errors (500, 502, 503, 504) and network errors. Other HTTP errors, such as 401
        (bad login), 403 (no permission) and 404 (no such folder), fail at once because retrying
        would not help. A new HTTPS connection is opened for every request.
        """
        # Absolute URLs pass through. Relative ones, including ONTAP's own next-page links, get the
        # cluster address put in front.
        url = path if path.startswith("http") else self.base + path
        # Add the query parameters, using & when the URL already contains a ? (next-page links do).
        if params:
            url += ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
        # Retry loop: one first attempt plus up to `retries` more, doubling the wait each time.
        delay = 1.0
        for attempt in range(retries + 1):
            try:
                req = urllib.request.Request(url, headers=self.headers)
                with urllib.request.urlopen(req, timeout=self.timeout, context=self.ctx) as r:
                    # errors="replace" means an odd byte in a file name can never crash the JSON parser.
                    return json.loads(r.read().decode("utf-8", "replace"))
            # The cluster answered with an error status.
            except urllib.error.HTTPError as e:
                if e.code in (429, 500, 502, 503, 504) and attempt < retries:
                    time.sleep(delay)
                    delay *= 2
                    continue
                raise ApiError(e.code, self._error_text(e))
            # No answer at all (DNS failure, refused connection, timeout, TLS problem).
            except (urllib.error.URLError, OSError) as e:
                if attempt < retries:
                    time.sleep(delay)
                    delay *= 2
                    continue
                raise ApiError(0, str(getattr(e, "reason", e)))

    @staticmethod
    def _error_text(e):
        """Pull the human-readable message out of an ONTAP error body, or fall back to the HTTP reason."""
        try:
            body = json.loads(e.read().decode("utf-8", "replace"))
            return body.get("error", {}).get("message") or str(e.reason)
        except Exception:
            return str(e.reason)

    def paged(self, path, params):
        """Yield every record of a list request, following all the pages.

        ONTAP returns long lists in pages. If more records exist, the response carries
        _links.next.href: a ready-made relative URL for the next page. It is followed exactly
        as given, and the original query parameters are NOT sent again because the href
        already contains them. The loop ends when no next link is present.
        """
        url, p = path, params
        while url:
            body = self.get(url, p)
            for rec in body.get("records", []):
                yield rec
            nxt = body.get("_links", {}).get("next", {}).get("href")
            url, p = (nxt if nxt else None), None   # href already carries the query

    def cluster_info(self):
        """Cluster name and ONTAP version. Used by "Test connection"."""
        return self.get("/api/cluster", {"fields": "name,version"})

    def volumes(self):
        """List every volume of the cluster, sorted by SVM then name.

        Each entry has: uuid, name, svm, state (online/offline/...), type (rw/dp/ls), style
        (flexvol/flexgroup/flexgroup_constituent), root (True for an SVM root volume) and skip
        (None, or the reason the SVM and cluster scopes skip it by default; see skip_reason).
        The UUID is what every files request uses, so the GUI keeps it as the volume's value.
        """
        base = "name,uuid,svm.name,state,type,style"
        try:
            recs = list(self.paged("/api/storage/volumes",
                                   {"fields": base + ",is_svm_root,nas.path", "max_records": 500}))
        except ApiError as e:
            # An older ONTAP may not know is_svm_root or nas.path and answers 400 for an unknown
            # field. Ask again for the basic fields only; SVM root volumes then cannot be
            # recognised (they are small and normally empty, so scanning them is harmless).
            if e.code != 400:
                raise
            recs = list(self.paged("/api/storage/volumes", {"fields": base, "max_records": 500}))
        out = []
        for v in recs:
            d = {"uuid": v.get("uuid"), "name": v.get("name") or "",
                 "svm": (v.get("svm") or {}).get("name", ""),
                 "state": v.get("state", ""), "type": v.get("type", ""), "style": v.get("style", ""),
                 # An SVM root volume is flagged by is_svm_root, or is the one mounted at "/".
                 "root": bool(v.get("is_svm_root")) or (v.get("nas") or {}).get("path") == "/"}
            d["skip"] = skip_reason(d)
            out.append(d)
        out.sort(key=lambda v: (v["svm"], v["name"]))
        return out

    def dir_url(self, vol, rel, root_style):
        """Build the REST path that lists one folder of one volume.

        `rel` is relative to the volume (not an SMB share path or an NFS export path) and is
        percent-encoded as ONE path parameter. An empty `rel` means the volume root, which is spelled
        the way _probe_root found to work on this ONTAP version.
        """
        seg = quote_path(rel) if rel else root_style
        return "/api/storage/volumes/%s/files/%s" % (vol, seg)

    def list_dir(self, vol, rel, root_style):
        """Yield the entries of one folder, 1000 per page, following every page (see paged())."""
        return self.paged(self.dir_url(vol, rel, root_style),
                          {"fields": FIELDS, "max_records": 1000})


def quote_path(rel):
    """Percent-encode a volume-relative path for use as the {path} part of a files request."""
    # The {path} segment is ONE path parameter: slashes must be sent as %2F.
    return urllib.parse.quote(rel.strip("/"), safe="")


def file_ext(path):
    """The "file type" of a path for the By file type chart.

    The ending after the last dot, in lower case. .tar.gz, .tar.bz2 and .tar.xz count as one type.
    A name with no dot, or only a leading dot such as .bashrc, is "(none)".
    """
    name = path.rsplit("/", 1)[-1].lower()
    for multi in (".tar.gz", ".tar.bz2", ".tar.xz"):
        if name.endswith(multi):
            return multi
    dot = name.rfind(".")
    return name[dot:] if 0 < dot < len(name) - 1 else "(none)"


_TS_FRAC = re.compile(r"\.\d+")
_TS_TZ = re.compile(r"([+-]\d\d):(\d\d)$")


def parse_ts(s):
    """Turn an ONTAP timestamp into a timezone-aware datetime, or None if it cannot be read.

    ONTAP returns ISO 8601 text such as 2021-05-05T10:00:00+00:00 or ...Z, sometimes with
    fractions of a second. strptime on older Python 3 versions cannot read "Z", "+00:00" or
    fractions, so the text is normalised first. A missing zone is treated as UTC.
    """
    if not s:
        return None
    try:
        # Drop fractions of a second.
        s = _TS_FRAC.sub("", s)
        # "Z" means UTC. Then turn +hh:mm into +hhmm, which %z understands on every Python 3 version.
        s = s.replace("Z", "+0000")
        s = _TS_TZ.sub(r"\1\2", s)
        # No zone at all: assume UTC.
        if not re.search(r"[+-]\d{4}$", s):
            s += "+0000"
        return datetime.strptime(s, "%Y-%m-%dT%H:%M:%S%z")
    except ValueError:
        return None


def csv_safe(text):
    """Guard against spreadsheet formula injection in the CSV.

    A file name that starts with =, +, - or @ could be run as a formula when the CSV is opened in
    a spreadsheet, so such paths get a leading apostrophe. (Our paths start with "/", so this is
    a safety net for anything that changes that.)
    """
    return "'" + text if text[:1] in ("=", "+", "-", "@") else text


def vol_key(svm, name):
    """The label used for a volume everywhere (tables, charts, filters): "svm:volume"."""
    return "%s:%s" % (svm, name) if svm else name


def skip_reason(v):
    """Why the SVM and cluster scopes skip this volume by default, or None to scan it.

    Order matters (the first match wins):
      system       - ONTAP's own metadata volumes (names starting MDV_)
      svm_root     - an SVM's root volume (holds the namespace, not user data)
      constituent  - a piece of a FlexGroup; the FlexGroup itself is scanned instead
      offline      - not online (offline, restricted, mixed), so its files cannot be read
      dp           - a SnapMirror/SnapVault destination (type dp) or load-sharing mirror (ls).
                     It is a copy of another volume, so scanning it would count the same data
                     twice. The "Include DP volumes" option turns this one rule off.
    A volume you tick or pick yourself is scanned regardless of these rules.
    """
    if v["name"].startswith("MDV_"):
        return "system"
    if v.get("root"):
        return "svm_root"
    if v.get("style") == "flexgroup_constituent":
        return "constituent"
    if v.get("state") not in ("online", "", None):
        return "offline"
    if v.get("type") in ("dp", "ls"):
        return "dp"
    return None


def private(path):
    """Make a result file readable by its owner only (best effort; not every OS honours this)."""
    try:
        os.chmod(path, 0o600)
    except OSError:
        pass


def like_escape(text):
    """Escape the characters that mean something inside a SQL LIKE pattern (% _ and backslash)."""
    return text.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")


# Sort keys the GUI may ask for, mapped to database columns. Only these names are ever put into
# the SQL text, so a hostile "sort" parameter cannot inject anything.
SORT_COLUMNS = {"path": "path", "size": "size", "atime": "atime", "mtime": "mtime",
                "age": "age", "volume": "vol"}


def query_db(db_path, q, sorts, offset, limit, flt=None):
    """Filter, sort and slice the cold files stored in a scan's database for the Files tab.

    q       - text that must appear in the path (not case sensitive)
    sorts   - list of (column, descending?) pairs, first = most important
    flt     - optional filters: vol (text in "svm:volume", or =svm:volume for exactly one), min/max size in bytes, mod/acc =
              at least this many days since modified/accessed, ext = list of file endings
    Returns the number of matching files, their total size and one page of rows. Every value
    goes in as a bound parameter, never into the SQL text. This never calls ONTAP.
    """
    f = flt or {}
    where, params = [], []
    if q:
        where.append("path LIKE ? ESCAPE '\\'")
        params.append("%" + like_escape(q) + "%")
    if f.get("vol"):
        if f["vol"].startswith("="):
            # A leading "=" means exactly this volume (used by clicks on the volume charts).
            where.append("vol = ?")
            params.append(f["vol"][1:])
        else:
            where.append("vol LIKE ? ESCAPE '\\'")
            params.append("%" + like_escape(f["vol"]) + "%")
    if f.get("min") is not None:
        where.append("size >= ?")
        params.append(f["min"])
    if f.get("max") is not None:
        where.append("size <= ?")
        params.append(f["max"])
    if f.get("mod") is not None:
        where.append("mod_age >= ?")
        params.append(f["mod"])
    if f.get("acc") is not None:
        where.append("acc_age >= ?")
        params.append(f["acc"])
    if f.get("ext"):
        # "ends with": LIKE '%.vmdk'. SQLite's LIKE ignores case for ASCII letters.
        where.append("(" + " OR ".join(["path LIKE ? ESCAPE '\\'"] * len(f["ext"])) + ")")
        params.extend("%" + like_escape(e) for e in f["ext"])
    clause = (" WHERE " + " AND ".join(where)) if where else ""
    # Multi-level sort in one ORDER BY. The final "id" keeps the order stable between pages.
    order = ", ".join("%s %s" % (SORT_COLUMNS[k], "DESC" if desc else "ASC")
                      for k, desc in sorts if k in SORT_COLUMNS)
    order = (order + ", id") if order else "id"
    empty = {"total": 0, "total_bytes": 0, "rows": []}
    if not os.path.isfile(db_path):
        return empty                      # the scan has not created its database yet
    con = sqlite3.connect(db_path, timeout=10)
    try:
        con.execute("PRAGMA query_only=ON")      # this connection can only read
        total, total_bytes = con.execute(
            "SELECT COUNT(*), COALESCE(SUM(size), 0) FROM files" + clause, params).fetchone()
        cur = con.execute(
            "SELECT path, size, atime, mtime, age, mod_age, acc_age, vol FROM files" + clause +
            " ORDER BY " + order + " LIMIT ? OFFSET ?", params + [limit, offset])
        return {"total": total, "total_bytes": total_bytes, "rows": [list(r) for r in cur.fetchall()]}
    except sqlite3.OperationalError:
        return empty                      # the table does not exist yet
    finally:
        con.close()


# --------------------------------------------------------------------------
# Scan engine: volumes, shared work queue, bounded worker pool, SQLite results
# --------------------------------------------------------------------------
class Scan:
    """One scan: its settings, live counters, results and worker threads.

    A scan covers one or more volumes (cfg["scope"]). The volumes are scanned one after another;
    for each volume a fresh pool of worker threads reads its folders in parallel. Results go to
    a CSV file and to a SQLite database as they are found.

    Life cycle:  start() -> _run():
        _plan()               list the cluster's volumes and decide which to scan
        _open_outputs()       create the CSV and the database
        _scan_volume() x N    probe the volume root, then run the workers over its folders
        _finish_outputs()     commit and build the search index
        _close_outputs()      save a summary for reopening, close the files
    `state` is one of: starting, running, done, stopped, failed.

    Locking rule: anything that more than one thread touches (counters, queue accounting, the
    CSV writer, the database connection used for writing) is changed only while holding
    self.lock, in short bursts. The slow work, the REST calls, is always done outside the lock.
    """
    def __init__(self, cfg, client, outdir):
        # cfg    = the validated settings from the GUI (see Handler._start)
        # client = the Ontap object. It holds the password in memory only.
        self.cfg, self.client = cfg, client
        # lock     - guards all shared state below
        # q        - work waiting to be read: (volume record, folder path relative to the volume)
        # pending  - folders of the CURRENT volume that are queued OR being read. A volume is
        #            finished only when this reaches 0; an empty queue alone is not enough
        #            (see _worker)
        # stop_ev  - set by the Stop button; workers check it between entries
        self.lock = threading.Lock()
        self.q = queue.Queue()
        self.pending = 0
        self.stop_ev = threading.Event()
        # Status shown in the header pill, and timing for the tiles.
        self.state = "starting"
        self.message = ""
        self.started = time.time()
        self.finished = None
        # Running totals shown in the tiles and the Summary tab, across all volumes. files and
        # total_bytes count what was checked (excluded file types are kept apart in excl_*).
        # unknown_ts counts files whose needed timestamp was missing or unreadable.
        self.dirs = self.files = self.cold_files = 0
        self.cold_bytes = self.total_bytes = self.unknown_ts = 0
        self.excl_files = self.excl_bytes = 0
        # Cold files and bytes per age bucket (same order as BUCKETS).
        self.bucket_files = [0] * len(BUCKETS)
        self.bucket_bytes = [0] * len(BUCKETS)
        # Cold-data totals, each key -> [cold files, cold bytes]:
        #   by_dir  - (volume label, folder cut to the "folder depth" setting)
        #   by_ext  - file type, e.g. .vmdk   (Charts tab)
        #   by_year - year last modified      (Charts tab)
        self.by_dir = {}
        self.by_ext = {}
        self.by_year = {}
        # errors - the first MAX_ERRORS_KEPT folder or volume errors (shown on the Errors tab)
        self.errors, self.error_count = [], 0
        # Volumes: vols = the volumes being scanned, in order, each with its own counters;
        # skipped = volumes left out and why; vol_done / vol_ok = volumes finished / finished
        # without a volume-level failure; cur_vol = the volume being read right now.
        self.vols, self.skipped, self.skip_counts = [], [], {}
        self.vol_done = self.vol_ok = 0
        self.cur_vol = None
        # Output files. The database is written through one connection (used only under
        # self.lock); readers open their own. A name carries the scan's label and start time.
        self.csv_file = self.csv_writer = self.db = None
        self._last_commit = 0.0
        stamp = time.strftime("%Y%m%d-%H%M%S")
        label = re.sub(r"[^A-Za-z0-9_.-]", "_", cfg["label"] or "scan")
        self.csv_name = "cryo_%s_%s.csv" % (label, stamp)
        self.csv_path = os.path.join(outdir, self.csv_name)
        self.db_path = os.path.join(outdir, self.csv_name[:-4] + ".db")
        # One fixed "now" for the whole scan, so every file's age is measured from the same moment.
        self.now = datetime.now(timezone.utc)
        self.cutoff_days = cfg["days"]

    # -- lifecycle ---------------------------------------------------------
    def start(self):
        """Run the scan in a background thread so the HTTP request that started it can return at once."""
        threading.Thread(target=self._run, daemon=True).start()

    def stop(self):
        """Ask the scan to stop. Workers notice between entries and exit; what was found is kept."""
        self.stop_ev.set()

    def _run(self):
        """The scan's main thread: plan, set up the outputs, scan each volume, clean up."""
        final = "done"
        try:
            targets = self._plan()
            self._open_outputs()
            self.state = "running"
            for vol in targets:
                if self.stop_ev.is_set():
                    break
                self._scan_volume(vol)
            if self.stop_ev.is_set():
                final = "stopped"
            elif self.vol_ok == 0:
                # Not one volume could be scanned (bad volume, no permission, ...).
                final = "failed"
                first = next((v["error"] for v in targets if v["error"]), "")
                self.message = first if len(targets) == 1 else \
                    "No volume could be scanned. See the Errors tab."
            self._finish_outputs()
            self.state = final
        except Exception as e:  # noqa
            # Setup failed (bad login, no such SVM, cannot write the files, ...). The message is
            # shown in the header. Folder-level errors do not end up here; see _worker.
            self.state, self.message = "failed", str(e)
        finally:
            self.finished = time.time()
            self._close_outputs()

    def _plan(self):
        """Decide which volumes to scan. Costs one request to ONTAP (the volume list).

        Returns the list of per-volume records, in scan order. Each record carries the volume's
        identity plus its own counters, so the GUI can show a breakdown by volume.
        """
        cfg, scope = self.cfg, self.cfg["scope"]
        vols = self.client.volumes()
        by_uuid = {v["uuid"]: v for v in vols}
        chosen = []
        if scope == "volume":
            # The one volume picked in the GUI. If the list does not show it (a partial list, or
            # a permission limit), still try it by its UUID.
            chosen = [by_uuid.get(cfg["volume"]) or
                      {"uuid": cfg["volume"], "name": cfg["volume_name"] or cfg["volume"],
                       "svm": "", "state": "", "type": "", "style": "", "root": False, "skip": None}]
        elif scope == "selected":
            # Volumes the user ticked. Explicit picks are scanned even if the default rules would
            # have skipped them. A UUID the cluster no longer lists is reported as skipped.
            seen = set()
            for u in cfg["volumes"]:
                if u in seen:
                    continue
                seen.add(u)
                if u in by_uuid:
                    chosen.append(by_uuid[u])
                else:
                    self._skip({"svm": "", "name": u}, "not_found")
        else:
            # "svm" and "cluster": every volume that passes the default rules (skip_reason).
            pool = vols
            if scope == "svm":
                pool = [v for v in vols if v["svm"].lower() == cfg["svm"].lower()]
                if not pool:
                    raise ValueError("No volumes found in SVM %s." % cfg["svm"])
            for v in pool:
                if v["skip"] is None or (v["skip"] == "dp" and cfg["include_dp"]):
                    chosen.append(v)
                else:
                    self._skip(v, v["skip"])
        if not chosen:
            raise ValueError("No volumes to scan (%d left out: skipped by the default rules or not found)." % len(self.skipped))
        self.vols = [{"uuid": v["uuid"], "name": v["name"], "svm": v["svm"],
                      "key": vol_key(v["svm"], v["name"]), "state": "waiting", "error": "",
                      "root_style": "", "dirs": 0, "files": 0, "total_bytes": 0,
                      "cold_files": 0, "cold_bytes": 0} for v in chosen]
        return self.vols

    def _skip(self, v, reason):
        """Remember a volume that was left out and why (counted exactly, listed up to a limit)."""
        self.skip_counts[reason] = self.skip_counts.get(reason, 0) + 1
        if len(self.skipped) < MAX_SKIPPED_LISTED:
            self.skipped.append({"svm": v["svm"], "name": v["name"], "reason": reason})

    def _open_outputs(self):
        """Create the CSV and the SQLite database for this scan."""
        # CSV: one row per cold file, with the SVM and volume in the first two columns.
        self.csv_file = open(self.csv_path, "w", newline="", encoding="utf-8")
        private(self.csv_path)
        self.csv_writer = csv.writer(self.csv_file)
        self.csv_writer.writerow(["svm", "volume", "path", "bytes_used", "accessed_time",
                                  "modified_time", "age_days"])
        # Database: WAL mode lets the GUI read while the scan writes. synchronous=NORMAL is safe
        # in WAL mode and avoids a disk flush on every commit. check_same_thread=False because
        # worker threads write through this connection (always while holding self.lock).
        self.db = sqlite3.connect(self.db_path, check_same_thread=False)
        private(self.db_path)
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.execute("PRAGMA synchronous=NORMAL")
        # files: one row per cold file. vol is "svm:volume"; path is relative to the volume;
        # atime/mtime are ISO text (which sorts correctly); mod_age/acc_age are whole days since
        # modified/accessed (-1 if unknown), kept so the "not modified for N days" filters need
        # no recalculation. meta: the scan's summary, saved at the end so the scan can be reopened.
        self.db.execute("CREATE TABLE files (id INTEGER PRIMARY KEY, vol TEXT, path TEXT, "
                        "size INTEGER, atime TEXT, mtime TEXT, age INTEGER, "
                        "mod_age INTEGER, acc_age INTEGER)")
        self.db.execute("CREATE TABLE meta (k TEXT PRIMARY KEY, v TEXT)")
        self.db.commit()
        self._last_commit = time.time()

    def _scan_volume(self, vol):
        """Scan one volume: probe its root, then run a pool of workers over its folders."""
        with self.lock:
            vol["state"] = "running"
            self.cur_vol = vol
        try:
            vol["root_style"] = self._probe_root(vol)
        except Exception as e:
            self._vol_failed(vol, str(e))
            return
        # The start folder only applies to a one-volume scan; other scopes start at each root.
        root = self.cfg["root"].strip("/") if self.cfg["scope"] == "volume" else ""
        with self.lock:
            self.pending = 1          # the one queued folder: the start folder
        self.q.put((vol, root))
        # Start the worker threads, then wait for every one to finish. They finish when nothing
        # is queued or in progress, or when Stop is pressed.
        workers = [threading.Thread(target=self._worker, daemon=True)
                   for _ in range(self.cfg["workers"])]
        for w in workers:
            w.start()
        for w in workers:
            w.join()
        while True:                   # after Stop, discard whatever was still queued
            try:
                self.q.get_nowait()
            except queue.Empty:
                break
        with self.lock:
            vol["state"] = "stopped" if self.stop_ev.is_set() else "done"
            self.vol_done += 1
            self.vol_ok += 1
            self.pending = 0

    def _vol_failed(self, vol, msg):
        """A whole volume could not be scanned (probe failed). Log it and let the scan move on."""
        with self.lock:
            vol["state"], vol["error"] = "failed", msg
            self.vol_done += 1
            self.error_count += 1
            if len(self.errors) < MAX_ERRORS_KEPT:
                self.errors.append({"path": vol["key"] if self.cfg["scope"] != "volume" else "/",
                                    "error": msg})

    def _probe_root(self, vol):
        """Ask for one entry of the volume root, trying each spelling of the root path in turn.

        Different ONTAP versions accept different spellings for the volume root: an empty path
        or %2F. Returns the one that worked. This also proves the login and the volume UUID
        before any file is read.
        """
        last = None
        for style in ("", "%2F"):
            try:
                url = "/api/storage/volumes/%s/files/%s" % (vol["uuid"], style)
                self.client.get(url, {"fields": "name", "max_records": 1})
                return style
            except ApiError as e:
                last = e
                if e.code in (401, 403):
                    break
        raise last

    def _worker(self):
        """Worker thread: keep taking a folder from the queue and processing it until the volume is done.

        Why "done" is not simply "queue empty": another worker may be reading a folder right now
        and be about to add its subfolders. So the scan keeps `pending`, the number of folders that
        are queued or in progress, and a worker exits only when that is 0.
        """
        while not self.stop_ev.is_set():
            try:
                # Wait up to half a second for work, so Stop and the finish check are noticed promptly.
                vol, rel = self.q.get(timeout=0.5)
            except queue.Empty:
                with self.lock:
                    # Queue empty AND nothing in progress: the whole volume has been read.
                    if self.pending <= 0:
                        return
                continue
            try:
                self._process(vol, rel)
            # A failed folder (permission denied, removed during the scan, ...) is logged on the Errors
            # tab and the scan carries on with the others.
            except Exception as e:  # keep scanning after a bad directory
                self._error(vol, rel, str(e))
            # This folder is finished, successfully or not. Its subfolders were already added to
            # `pending` inside _process, before this line runs, so `pending` can never reach 0 too early.
            finally:
                with self.lock:
                    self.pending -= 1

    def _error(self, vol, rel, msg):
        """Record a folder-level error. The total is always counted; only the first MAX_ERRORS_KEPT are stored."""
        with self.lock:
            self.error_count += 1
            if len(self.errors) < MAX_ERRORS_KEPT:
                where = "/" + rel
                if self.cfg["scope"] != "volume":
                    where = vol["key"] + ":" + where       # say which volume the folder is in
                self.errors.append({"path": where, "error": msg})

    # -- per-directory work -------------------------------------------------
    def _process(self, vol, rel):
        """Read one folder of one volume: judge its files, collect its subfolders, then commit the results.

        Everything is gathered into local variables first (no lock needed, and the slow REST calls
        happen here). The shared totals are then updated in one short locked step at the end.

        For each entry:
          directory -> queued for later (symlinks and other types are ignored, never followed)
          file      -> excluded by file type?  counted apart, never judged
                       otherwise judged cold or not by the chosen timestamp rule
        """
        cfg, mode = self.cfg, self.cfg["mode"]
        # sub_dirs = subfolders to queue; hits = cold files found in this folder;
        # n_* = checked files, bytes and files without a usable timestamp; x_* = excluded files, bytes.
        sub_dirs, hits = [], []
        n_files = n_bytes = n_unknown = x_files = x_bytes = 0
        excl = tuple(cfg["exclude"])
        for rec in self.client.list_dir(vol["uuid"], rel, vol["root_style"]):
            # Check the Stop flag for every entry, so Stop reacts quickly even inside a huge folder.
            if self.stop_ev.is_set():
                return
            name = rec.get("name")
            if not name or name in SKIP:
                continue
            # Path of this entry relative to the volume, without a leading slash.
            child = (rel + "/" + name) if rel else name
            # Only "directory" is walked into and only "file" is judged.
            kind = rec.get("type")
            if kind == "directory":
                sub_dirs.append(child)
            elif kind == "file":
                # Size = space actually used (bytes_used); fall back to the logical size if it is missing.
                size = rec.get("bytes_used")
                if size is None:
                    size = rec.get("size") or 0
                if excl and name.lower().endswith(excl):
                    x_files += 1          # excluded by file type: counted apart, never scanned for age
                    x_bytes += size
                    continue
                n_files += 1
                n_bytes += size
                a, m = parse_ts(rec.get("accessed_time")), parse_ts(rec.get("modified_time"))
                # Which timestamps decide, from the "Counts as cold when" setting:
                #   both  - accessed AND modified (the safer default, because backup or antivirus tools
                #           can touch access times and make cold data look warm)
                #   atime - accessed only         mtime - modified only
                used = {"both": [a, m], "atime": [a], "mtime": [m]}[mode]
                if any(t is None for t in used):
                    n_unknown += 1
                    continue
                # Age in whole days. max() picks the MORE RECENT of the timestamps in use, so with
                # "both" a file is cold only if both of its times are old enough.
                age = (self.now - max(used)).days
                if age >= self.cutoff_days:
                    hits.append((child, size, a, m, age))
        # Work out everything the commit needs for each cold file (still outside the lock).
        prepared = []
        for path, size, a, m, age in hits:
            # A lone surrogate in a file name would make the database and CSV writers fail; replace it.
            path = path.encode("utf-8", "replace").decode("utf-8")
            # Which age bucket this file belongs in.
            b = next(i for i, (_, lim) in enumerate(BUCKETS) if lim is None or age < lim)
            # Group by the first N folder names (N = "folder depth"). With depth 2, the file
            # projects/archive_2022/budgets/a.xlsx is counted under /projects/archive_2022.
            folder = "/" + "/".join(path.split("/")[:-1][:cfg["depth"]])
            # Extra ages kept with each row so the Files tab filters "not modified for N days"
            # and "not accessed for N days" can run later without asking ONTAP again. -1 = unknown.
            m_age = (self.now - m).days if m else -1
            a_age = (self.now - a).days if a else -1
            prepared.append(("/" + path, size, a.isoformat() if a else "", m.isoformat() if m else "",
                             age, m_age, a_age, b, folder, file_ext(path),
                             str(m.year) if m else "unknown"))
        # Commit this folder's results in one short locked step. Writing the CSV and the database
        # here too means rows from different workers can never interleave.
        with self.lock:
            # Database first: if it fails (disk full), nothing below has been counted yet.
            if prepared:
                self.db.executemany(
                    "INSERT INTO files (vol, path, size, atime, mtime, age, mod_age, acc_age) "
                    "VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                    [(vol["key"], p[0], p[1], p[2], p[3], p[4], p[5], p[6]) for p in prepared])
                # Make rows visible to the Files tab about once a second (committing after every
                # folder would be slow on a big scan).
                if time.time() - self._last_commit >= 1.0:
                    self.db.commit()
                    self._last_commit = time.time()
            self.dirs += 1
            self.files += n_files
            self.total_bytes += n_bytes
            self.unknown_ts += n_unknown
            self.excl_files += x_files
            self.excl_bytes += x_bytes
            # The same figures per volume, for the "By volume" views.
            vol["dirs"] += 1
            vol["files"] += n_files
            vol["total_bytes"] += n_bytes
            for p in prepared:
                size = p[1]
                self.cold_files += 1
                self.cold_bytes += size
                vol["cold_files"] += 1
                vol["cold_bytes"] += size
                self.bucket_files[p[7]] += 1
                self.bucket_bytes[p[7]] += size
                dk = (vol["key"], p[8])
                if dk not in self.by_dir and len(self.by_dir) >= MAX_DIR_KEYS:
                    dk = (vol["key"], "(other)")      # safety limit; see MAX_DIR_KEYS
                d = self.by_dir.setdefault(dk, [0, 0])
                d[0] += 1
                d[1] += size
                xt = self.by_ext.setdefault(p[9], [0, 0])
                xt[0] += 1
                xt[1] += size
                yr = self.by_year.setdefault(p[10], [0, 0])
                yr[0] += 1
                yr[1] += size
                # CSV row: svm, volume, path, bytes, accessed, modified, age. Text fields are made
                # safe against spreadsheet formula injection.
                self.csv_writer.writerow([csv_safe(vol["svm"]), csv_safe(vol["name"]),
                                          csv_safe(p[0]), size, p[2], p[3], p[4]])
            # Count the new subfolders as pending BEFORE this folder is marked finished (see _worker).
            self.pending += len(sub_dirs)
        # Queue the subfolders outside the lock; any idle worker will pick them up.
        for d in sub_dirs:
            self.q.put((vol, d))

    # -- finishing ----------------------------------------------------------
    def _finish_outputs(self):
        """Commit the last rows and build the indexes that make sorting fast on big scans."""
        keep = self.message
        self.message = "Building the search index..."
        try:
            with self.lock:
                self.db.commit()
            for col in ("size", "mtime", "atime", "age"):
                self.db.execute("CREATE INDEX IF NOT EXISTS ix_%s ON files(%s)" % (col, col))
            self.db.commit()
        except Exception:
            pass        # without indexes the Files tab still works, just more slowly
        self.message = keep

    def _close_outputs(self):
        """Close the CSV, then save the summary into the database and close it.

        A scan that failed before finding anything leaves no files behind. Otherwise the final
        status is stored in the database (table meta) so the scan can be reopened later from the
        Saved scans tab, and the database is switched back to a single plain file.
        """
        try:
            if self.csv_file:
                self.csv_file.close()
        except Exception:
            pass
        db = self.db
        if db is None:
            return
        try:
            if self.state == "failed" and self.cold_files == 0:
                db.close()
                self.db = None
                for p in (self.csv_path, self.db_path, self.db_path + "-wal", self.db_path + "-shm"):
                    try:
                        os.remove(p)
                    except OSError:
                        pass
                return
            db.execute("INSERT OR REPLACE INTO meta (k, v) VALUES ('status', ?)",
                       (json.dumps(self.status()),))
            db.commit()
            try:
                db.execute("PRAGMA wal_checkpoint(TRUNCATE)")
                db.execute("PRAGMA journal_mode=DELETE")
            except sqlite3.Error:
                pass    # a reader may be connected right now; WAL mode is fine to leave
        except Exception:
            pass
        finally:
            try:
                db.close()
            except Exception:
                pass
            self.db = None

    # -- views for the GUI --------------------------------------------------
    def status(self):
        """Everything the GUI needs for the tiles, Summary and Charts tabs, copied under the lock.

        This is what /api/status returns. It never includes the password.
        """
        with self.lock:
            end = self.finished or time.time()
            el = max(end - self.started, 0.001)
            # Top 30 folders and top 12 file types by cold size; years in calendar order; the
            # volumes with the most cold data first.
            top = sorted(self.by_dir.items(), key=lambda kv: kv[1][1], reverse=True)[:30]
            types = sorted(self.by_ext.items(), key=lambda kv: kv[1][1], reverse=True)[:12]
            years = sorted(self.by_year.items())
            vols = sorted(self.vols, key=lambda v: (-v["cold_bytes"], v["key"]))[:MAX_VOLS_IN_STATUS]
            running = self.state in ("starting", "running")
            return {
                "state": self.state, "message": self.message, "elapsed": el,
                "dirs": self.dirs, "files": self.files, "cold_files": self.cold_files,
                "cold_bytes": self.cold_bytes, "total_bytes": self.total_bytes,
                "unknown_ts": self.unknown_ts, "queued": max(self.pending - 1, 0),
                "excl_files": self.excl_files, "excl_bytes": self.excl_bytes,
                "dirs_per_sec": self.dirs / el,
                "buckets": [{"label": BUCKETS[i][0], "files": self.bucket_files[i],
                             "bytes": self.bucket_bytes[i]} for i in range(len(BUCKETS))],
                "top_dirs": [{"volume": k[0], "path": k[1], "files": v[0], "bytes": v[1]}
                             for k, v in top],
                "types": [{"ext": k, "files": v[0], "bytes": v[1]} for k, v in types],
                "years": [{"year": k, "files": v[0], "bytes": v[1]} for k, v in years],
                # Volume progress and breakdown. "multi" tells the GUI to show volume columns.
                "multi": self.cfg["scope"] != "volume",
                "vol_total": len(self.vols), "vol_done": self.vol_done,
                "vol_current": self.cur_vol["key"] if (running and self.cur_vol) else "",
                "volumes": [{"key": v["key"], "svm": v["svm"], "name": v["name"], "state": v["state"],
                             "files": v["files"], "cold_files": v["cold_files"],
                             "cold_bytes": v["cold_bytes"], "total_bytes": v["total_bytes"],
                             "error": v["error"]} for v in vols],
                "skipped": list(self.skipped), "skip_counts": dict(self.skip_counts),
                "errors": self.errors[-100:], "error_count": self.error_count,
                "csv": self.csv_name,
                # The settings, minus the (possibly long) list of ticked volume UUIDs.
                "config": {k: v for k, v in self.cfg.items() if k != "volumes"},
            }

    def query_rows(self, q, sorts, offset, limit, flt=None):
        """One page of the Files tab, read from the scan's database (see query_db)."""
        return query_db(self.db_path, q, sorts, offset, limit, flt)


class SavedScan:
    """A finished scan reopened from its database, for the Saved scans tab.

    It answers the same calls as Scan (status, query_rows, stop, state) so the GUI treats it
    the same way: the summary comes from the status saved at the end of the scan, and the Files
    tab reads the database. It cannot scan anything and never contacts ONTAP.
    """
    def __init__(self, csv_name, outdir):
        self.csv_name = csv_name
        self.db_path = os.path.join(outdir, csv_name[:-4] + ".db")
        con = sqlite3.connect(self.db_path, timeout=10)
        try:
            row = con.execute("SELECT v FROM meta WHERE k = 'status'").fetchone()
        except sqlite3.Error:
            row = None
        finally:
            con.close()
        if not row:
            raise ValueError("That saved scan has no summary (it was probably interrupted).")
        self.snapshot = json.loads(row[0])
        # A scan can only have been saved in a final state, but never report "running" for a file.
        state = self.snapshot.get("state", "done")
        self.state = state if state not in ("starting", "running") else "done"

    def status(self):
        s = dict(self.snapshot)
        s.update({"state": self.state, "queued": 0, "csv": self.csv_name,
                  "message": "Opened saved scan %s." % self.csv_name})
        return s

    def query_rows(self, q, sorts, offset, limit, flt=None):
        return query_db(self.db_path, q, sorts, offset, limit, flt)

    def stop(self):
        pass        # nothing is running


# --------------------------------------------------------------------------
# HTTP server
# --------------------------------------------------------------------------
class Server(ThreadingMixIn, HTTPServer):
    """HTTP server with one thread per request, so the GUI stays responsive during a scan.

    daemon_threads lets the program exit without waiting for open requests.
    allow_reuse_address lets you restart straight away on the same port.
    """
    daemon_threads = True
    allow_reuse_address = True


class App:
    """Process-wide settings and state shared by every request.

    scan   - the current (or most recent) Scan or reopened SavedScan, or None before the first one
    token  - the access token from --token / CRYO_TOKEN, or None for no token
    outdir - folder where the CSV and database results are saved
    lock   - held while a new scan is started, so two quick clicks cannot start two scans
    """
    scan = None
    token = None
    outdir = "scans"
    lock = threading.Lock()


def client_from(body):
    """Build an Ontap client from the connection fields the GUI sent (address, user, password, TLS)."""
    return Ontap(body.get("cluster", ""), body.get("user", ""), body.get("password", ""),
                 tls=body.get("tls", "verify"), ca=(body.get("ca") or "").strip() or None)


def clamp(v, lo, hi, default):
    """Turn browser input into an integer limited to lo..hi, or `default` if it is not a number."""
    try:
        return max(lo, min(hi, int(v)))
    except (TypeError, ValueError):
        return default


class Handler(BaseHTTPRequestHandler):
    """Serves the GUI page and the JSON API. Each browser request runs in its own thread.

    GET  /                  the page (no token needed; it contains no data)
    GET  /api/status        counters, buckets, folders, types, years, errors
    GET  /api/results       one page of the Files table with sort, search and filters
    GET  /api/history       list of saved scans (CSV files, and whether each can be reopened)
    GET  /api/file?name=    download one saved CSV
    POST /api/test          cluster name and version            (1 request to ONTAP)
    POST /api/volumes       volume list                         (1 or a few requests to ONTAP)
    POST /api/scan/start    validate the settings, start a scan (many requests to ONTAP)
    POST /api/scan/stop     ask the running scan to stop
    POST /api/scan/open     reopen a saved scan from its database (no requests to ONTAP)
    """
    server_version = "Cryo/1.0"

    # Every request is logged to the terminal. The page polls /api/status every 1.5 seconds, so
    # many "GET /api/status ... 200" lines are normal.
    def log_message(self, fmt, *args):
        sys.stderr.write("%s %s\n" % (self.address_string(), fmt % args))

    # helpers
    # Send one response: bytes as they are, anything else as JSON. no-store stops browsers from
    # caching results; nosniff stops browsers from guessing a different content type.
    def _send(self, code, payload, ctype="application/json", extra=None):
        data = payload if isinstance(payload, bytes) else json.dumps(payload).encode()
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(data)

    def _authed(self):
        """True if no token is configured, or the request supplies the right one.

        The page sends it in an X-Token header. Download links (plain <a href>) cannot set headers,
        so a ?token= parameter is accepted too.
        Known gaps: this is an ordinary string comparison (hmac.compare_digest would be better),
        there is no limit on wrong guesses, and a token in a link can appear in the access log.
        """
        if not App.token:
            return True
        supplied = self.headers.get("X-Token") or urllib.parse.parse_qs(
            urllib.parse.urlparse(self.path).query).get("token", [""])[0]
        return supplied == App.token

    def _body(self):
        """Read and parse the JSON body of a POST request. An empty body means {}."""
        n = int(self.headers.get("Content-Length") or 0)
        return json.loads(self.rfile.read(n).decode() or "{}") if n else {}

    def _file(self, name):
        # Download safety: keep only the bare file name (this removes any ../ tricks), require a .csv
        # ending, and only read from inside the scans folder.
        name = os.path.basename(name)
        path = os.path.join(App.outdir, name)
        if not name.endswith(".csv") or not os.path.isfile(path):
            return self._send(404, {"error": "File not found"})
        with open(path, "rb") as f:
            data = f.read()
        self._send(200, data, "text/csv; charset=utf-8",
                   {"Content-Disposition": 'attachment; filename="%s"' % name})

    # routes
    def do_GET(self):
        url = urllib.parse.urlparse(self.path)
        qs = urllib.parse.parse_qs(url.query)
        # The page needs no token. The page asks for the token itself when its first API call gets a 401.
        if url.path == "/":
            return self._send(200, PAGE.encode(), "text/html; charset=utf-8")
        # Everything below this line needs the token (if one is set).
        if not self._authed():
            return self._send(401, {"error": "Access token required"})
        if url.path == "/api/status":
            s = App.scan
            return self._send(200, s.status() if s else {"state": "idle"})
        # Files tab. Query parameters: q, sort, offset, limit and the filters vol, fmin, fmax, mod,
        # acc, ext. Answered from the scan's database, with no request to ONTAP.
        if url.path == "/api/results":
            s = App.scan
            if not s:
                return self._send(200, {"total": 0, "rows": []})
            g = lambda k, d="": qs.get(k, [d])[0]
            # sort looks like "mtime:asc,size:desc": up to 4 levels, unknown column names are ignored.
            sorts = []
            for part in g("sort", "size:desc").split(",")[:4]:
                key, _, direction = part.partition(":")
                if key in SORT_COLUMNS:
                    sorts.append((key, direction != "asc"))
            # Read an optional number from the query string; blank or invalid means "no filter".
            def num(k):
                try:
                    return float(g(k)) if g(k) != "" else None
                except ValueError:
                    return None
            # The filters, with file types normalised to lower case with a leading dot (.vmdk).
            flt = {"vol": g("vol").strip(), "min": num("fmin"), "max": num("fmax"),
                   "mod": num("mod"), "acc": num("acc"),
                   "ext": [("." + t.lstrip("*.")).lower()
                           for t in re.split(r"[,\s;]+", g("ext")) if t.strip("*.")]}
            return self._send(200, s.query_rows(
                g("q"), sorts or [("size", True)],
                clamp(g("offset", "0"), 0, 10**9, 0), clamp(g("limit", "100"), 1, 1000, 100),
                flt=flt))
        # Saved scans tab: list the .csv files in the scans folder, newest name first. A scan can
        # be reopened if its database file is still next to the CSV.
        if url.path == "/api/history":
            os.makedirs(App.outdir, exist_ok=True)
            items = []
            for n in sorted(os.listdir(App.outdir), reverse=True):
                if n.endswith(".csv"):
                    st = os.stat(os.path.join(App.outdir, n))
                    items.append({"name": n, "bytes": st.st_size,
                                  "can_open": os.path.isfile(os.path.join(App.outdir, n[:-4] + ".db")),
                                  "modified": time.strftime("%Y-%m-%d %H:%M", time.localtime(st.st_mtime))})
            return self._send(200, {"files": items})
        # Download one saved CSV (see _file for the safety checks).
        if url.path == "/api/file":
            return self._file(qs.get("name", [""])[0])
        self._send(404, {"error": "Not found"})

    def do_POST(self):
        if not self._authed():
            return self._send(401, {"error": "Access token required"})
        # Error mapping: ApiError (an ONTAP problem) -> 502, ValueError (bad input) -> 400,
        # anything else -> 500. The message is shown in the GUI.
        try:
            body = self._body()
            path = urllib.parse.urlparse(self.path).path
            # Test connection: build a client from the form and ask for the cluster name and version.
            if path == "/api/test":
                info = client_from(body).cluster_info()
                return self._send(200, {"name": info.get("name"),
                                        "version": (info.get("version") or {}).get("full")})
            if path == "/api/volumes":
                return self._send(200, {"volumes": client_from(body).volumes()})
            if path == "/api/scan/start":
                return self._start(body)
            if path == "/api/scan/stop":
                if App.scan:
                    App.scan.stop()
                return self._send(200, {"ok": True})
            if path == "/api/scan/open":
                return self._open(body)
            self._send(404, {"error": "Not found"})
        except ApiError as e:
            self._send(502, {"error": str(e)})
        except ValueError as e:
            self._send(400, {"error": str(e)})
        except Exception as e:  # noqa
            self._send(500, {"error": "%s: %s" % (type(e).__name__, e)})

    def _start(self, b):
        """Validate the Scan form and start a scan. Every value from the browser is checked or clamped."""
        # Hold the lock so two quick clicks cannot start two scans at once.
        with App.lock:
            if App.scan and App.scan.state in ("starting", "running"):
                return self._send(409, {"error": "A scan is already running. Stop it first."})
            # What to scan. Volumes are identified by UUID (hex digits and dashes), which also
            # keeps odd characters out of the REST path.
            scope = b.get("scope", "volume")
            if scope not in ("volume", "selected", "svm", "cluster"):
                raise ValueError("Unknown scan scope")
            uuid_ok = re.compile(r"[0-9a-fA-F-]{36}")
            vol, vols, svm = "", [], ""
            if scope == "volume":
                vol = (b.get("volume") or "").strip()
                if not uuid_ok.fullmatch(vol):
                    raise ValueError("Volume must be a UUID. Use Load volumes to pick one.")
            elif scope == "selected":
                raw = b.get("volumes")
                vols = [str(u).strip() for u in raw[:5000]] if isinstance(raw, list) else []
                if not vols or not all(uuid_ok.fullmatch(u) for u in vols):
                    raise ValueError("Tick at least one volume. Use Load volumes first.")
            elif scope == "svm":
                svm = (b.get("svm") or "").strip()
                if not re.fullmatch(r"[A-Za-z0-9_.-]{1,64}", svm):
                    raise ValueError("Enter the SVM name.")
            mode = b.get("mode", "both")
            if mode not in ("both", "atime", "mtime"):
                raise ValueError("Unknown criteria")
            # Exclude file types: accept "iso", ".iso" or "*.ISO", separated by commas, spaces or
            # semicolons. Normalise to lower case with a leading dot, remove duplicates, keep at most 50.
            tokens = [t for t in re.split(r"[,\s;]+", b.get("exclude") or "") if t.strip("*.")]
            excl = sorted({("." + t.lstrip("*.")).lower() for t in tokens})[:50]
            # label names the result files: the volume, the SVM, "selected" or "cluster".
            vname = (b.get("volume_name") or "").strip()
            label = {"volume": vname or vol, "selected": "selected", "svm": svm,
                     "cluster": "cluster"}[scope]
            # The settings for this scan, with limits: age 1..36500 days, workers 1..16, folder depth 1..10.
            cfg = {"cluster": b.get("cluster", ""), "scope": scope, "volume": vol,
                   "volume_name": vname, "volumes": vols, "svm": svm,
                   "include_dp": bool(b.get("include_dp")), "label": label,
                   "root": (b.get("root") or "").strip(), "mode": mode,
                   "days": clamp(b.get("days"), 1, 36500, 180),
                   "workers": clamp(b.get("workers"), 1, 16, 6),
                   "depth": clamp(b.get("depth"), 1, 10, 2),
                   "exclude": excl}
            os.makedirs(App.outdir, exist_ok=True)
            # Replaces the previous scan. Its counters are discarded; its CSV and database stay on disk.
            App.scan = Scan(cfg, client_from(b), App.outdir)
            App.scan.start()
        self._send(200, {"ok": True})

    def _open(self, b):
        """Reopen a saved scan from its database. Nothing is sent to ONTAP."""
        # Keep only the bare file name (no ../ tricks) and require a .csv name; the database is
        # the file with the same name and a .db ending, inside the scans folder.
        name = os.path.basename(str(b.get("name") or ""))
        if not name.endswith(".csv"):
            raise ValueError("Pick a saved scan from the list.")
        with App.lock:
            if App.scan and App.scan.state in ("starting", "running"):
                return self._send(409, {"error": "A scan is running. Stop it before opening a saved scan."})
            if not os.path.isfile(os.path.join(App.outdir, name[:-4] + ".db")):
                return self._send(404, {"error": "That scan has no results database, so it can only be downloaded."})
            App.scan = SavedScan(name, App.outdir)
        self._send(200, {"ok": True})


# --------------------------------------------------------------------------
# Embedded GUI (no external resources)
# --------------------------------------------------------------------------
PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Cryo</title>
<style>
/* All colours are variables, so the light and dark themes only change these values. */
:root{--bg:#eef2f4;--panel:#fff;--ink:#15262e;--mute:#5b6e77;--line:#d3dde2;--ice:#1f6f99;--ice-soft:#dbeaf3;--warn:#a85a00;--bad:#b3261e;--ok:#1d7a4a}
/* Dark theme: used automatically when the browser or operating system prefers dark. */
@media (prefers-color-scheme:dark){:root{--bg:#10191e;--panel:#172329;--ink:#e3edf1;--mute:#8fa4ae;--line:#2a3b44;--ice:#6bb6dd;--ice-soft:#1c3340;--warn:#e0a050;--bad:#f2867e;--ok:#6fcf9b}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.45 system-ui,-apple-system,"Segoe UI",Roboto,"Helvetica Neue",Arial,sans-serif}
header{display:flex;align-items:center;gap:14px;padding:14px 22px;border-bottom:1px solid var(--line);background:var(--panel)}
h1{font-size:18px;margin:0;font-weight:650}
.pill{padding:2px 10px;border-radius:99px;background:var(--ice-soft);color:var(--ice);font-size:13px;font-weight:600}
.pill.running{background:var(--ice);color:var(--panel)} .pill.failed{background:var(--bad);color:var(--panel)} .pill.done{background:var(--ok);color:var(--panel)}
/* Page layout: settings column on the left, results on the right. On narrow screens (phones) the two columns stack. */
main{display:grid;grid-template-columns:340px 1fr;gap:18px;padding:18px 22px;max-width:1500px;margin:0 auto}
@media(max-width:900px){main{grid-template-columns:1fr}}
.panel{background:var(--panel);border:1px solid var(--line);border-radius:6px;padding:16px;margin-bottom:16px}
.panel h2{font-size:15px;margin:0 0 12px;font-weight:650}
label{display:block;font-size:13px;color:var(--mute);margin:10px 0 3px}
input,select{width:100%;padding:7px 9px;border:1px solid var(--line);border-radius:4px;background:var(--bg);color:var(--ink);font:inherit}
input:focus,select:focus,button:focus-visible{outline:2px solid var(--ice);outline-offset:1px}
.row{display:flex;gap:8px}.row>*{flex:1}
button{padding:7px 13px;border:1px solid var(--line);border-radius:4px;background:var(--panel);color:var(--ink);font:inherit;cursor:pointer}
button.primary{background:var(--ice);border-color:var(--ice);color:var(--panel);font-weight:600}
button.danger{border-color:var(--bad);color:var(--bad)}
button:disabled{opacity:.5;cursor:default}
.msg{font-size:13px;margin-top:8px;min-height:18px;color:var(--mute)} .msg.bad{color:var(--bad)} .msg.ok{color:var(--ok)}
/* The row of tiles: folders, files, cold files, cold size, speed and time. */
.tiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:12px;margin-bottom:16px}
.tile{background:var(--panel);border:1px solid var(--line);border-radius:6px;padding:12px 14px}
.tile b{display:block;font-size:22px;font-weight:650;font-variant-numeric:tabular-nums}
.tile span{font-size:13px;color:var(--mute)}
.tile.hot b{color:var(--ice)}
/* Tabs: Summary, Charts, Files, Errors and Saved scans. */
.tabs{display:flex;gap:4px;border-bottom:1px solid var(--line);margin-bottom:14px}
.tabs button{border:0;border-bottom:3px solid transparent;border-radius:0;background:none;color:var(--mute)}
.tabs button.on{color:var(--ink);border-color:var(--ice);font-weight:600}
table{width:100%;border-collapse:collapse;font-size:14px}
th,td{text-align:left;padding:6px 8px;border-bottom:1px solid var(--line);vertical-align:top}
th{color:var(--mute);font-weight:600;cursor:default} th.s{cursor:pointer}
td.n,th.n{text-align:right;font-variant-numeric:tabular-nums;white-space:nowrap}
td.p{word-break:break-all;font-family:ui-monospace,Menlo,Consolas,monospace;font-size:13px}
.bar{height:10px;background:var(--ice);border-radius:2px;min-width:1px}
.hint{color:var(--mute);font-size:13px;margin:8px 0}
.empty{color:var(--mute);padding:18px 4px}
.tbl{overflow-x:auto}
.presets{display:flex;flex-wrap:wrap;gap:6px;align-items:center;margin-bottom:10px}.presets button{padding:4px 10px;font-size:13px}
.sortrow{display:flex;gap:8px;margin-bottom:6px;align-items:center}.sortrow span{width:58px;color:var(--mute);font-size:13px}.sortrow select{flex:1}
/* Files tab filter boxes. They wrap onto more rows when the panel is narrow. */
.filters{display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:2px 10px;margin-bottom:12px}.filters label{margin:6px 0 3px}
/* Charts tab: charts sit in a responsive grid. The charts are SVG and take their colours from the theme variables above. */
.cgrid{display:grid;grid-template-columns:repeat(auto-fit,minmax(340px,1fr));gap:20px}.cgrid h2{margin:0 0 6px}.cwide{grid-column:1/-1}
.ch{width:100%;height:auto;display:block}.ch text{fill:var(--ink);font-size:12px}.ch .m{fill:var(--mute);font-size:11px}.ch .tt{fill:var(--panel);font-weight:600}
/* Scan scope: the volume checklist and the small checkbox rows. */
.vlist{max-height:210px;overflow:auto;border:1px solid var(--line);border-radius:6px;padding:4px 8px;margin-top:6px}
.vlist label,.chk{display:flex;align-items:center;gap:8px;margin:4px 0;font-size:13px;color:var(--ink)}
.vlist input,.chk input{width:auto;margin:0}.vlist .tag{color:var(--mute);font-size:11px;margin-left:auto}
.mini{padding:3px 9px;font-size:12px}
.pager{display:flex;gap:10px;align-items:center;margin-top:10px;color:var(--mute);font-size:13px}
</style></head><body>
<!-- Header: tool name, scan state pill (idle, running, done, stopped, failed) and any setup message. -->
<header><h1>Cryo</h1><span class="hint" style="margin:0">Cold data finder</span><span id="pill" class="pill">idle</span><span id="hdrmsg" class="hint" style="margin:0"></span></header>
<!-- Two columns. LEFT: Cluster and Scan settings. RIGHT: live tiles and the result tabs. -->
<main>
<div>
<!-- Cluster panel: where to connect and how to log in. These values are sent to this script only; the script talks to ONTAP. The password is never stored on disk. -->
  <div class="panel"><h2>Cluster</h2>
    <label for="cluster">Management address</label><input id="cluster" placeholder="cluster-mgmt.example.local" autocomplete="off">
    <div class="row"><div><label for="user">User</label><input id="user" autocomplete="off"></div>
    <div><label for="password">Password</label><input id="password" type="password" autocomplete="off"></div></div>
    <label for="tls">Certificate check</label>
    <select id="tls"><option value="verify">Verify with system CA store</option><option value="ca">Verify with CA file</option><option value="skip">Skip verification</option></select>
    <div id="cawrap" style="display:none"><label for="ca">CA file path on this server</label><input id="ca" placeholder="/etc/pki/ca-trust/source/anchors/internal-ca.pem"></div>
    <div class="row" style="margin-top:12px"><button id="btnTest">Test connection</button><button id="btnVols">Load volumes</button></div>
    <div id="connmsg" class="msg"></div>
  </div>
<!-- Scan panel: what to scan and what counts as cold. These settings are applied while the scan runs, so changing one needs a new scan. -->
  <div class="panel"><h2>Scan</h2>
<!-- Scope: what to scan. The volumes are scanned one after another, each from its own root, with the Workers setting below. -->
    <label for="scope">What to scan</label>
    <select id="scope"><option value="volume">One volume</option><option value="selected">Selected volumes</option><option value="svm">One SVM (all its volumes)</option><option value="cluster">Whole cluster</option></select>
    <div id="sc_volume">
      <label for="volume">Volume</label><input id="volume" list="vols" placeholder="Pick from list or paste UUID" autocomplete="off"><datalist id="vols"></datalist>
      <label for="root">Start folder (volume-relative, blank for root)</label><input id="root" placeholder="projects/archive_2022">
    </div>
    <div id="sc_selected" style="display:none">
      <label for="vfilter">Volumes to scan</label><input id="vfilter" placeholder="Filter the list" autocomplete="off">
      <div class="row" style="margin-top:6px"><button id="vElig" class="mini">Tick all eligible</button><button id="vNone" class="mini">Untick all</button></div>
      <div id="vlist" class="vlist"><span class="hint" style="margin:0">Click Load volumes first.</span></div>
    </div>
    <div id="sc_svm" style="display:none">
      <label for="svm">SVM name</label><input id="svm" list="svms" placeholder="svm_prod" autocomplete="off"><datalist id="svms"></datalist>
    </div>
    <div id="sc_dp" style="display:none"><label class="chk"><input id="incdp" type="checkbox">Include SnapMirror destination (DP) volumes</label></div>
    <div id="preview" class="hint" style="margin:6px 0 0"></div>
    <div class="row"><div><label for="days">Older than (days)</label><input id="days" type="number" min="1" value="180"></div>
    <div><label for="workers">Workers</label><input id="workers" type="number" min="1" max="16" value="6"></div></div>
    <label for="mode">Counts as cold when</label>
    <select id="mode"><option value="both">Both modified and accessed are older</option><option value="mtime">Modified time is older</option><option value="atime">Accessed time is older</option></select>
    <label for="depth">Group results by folder depth</label><input id="depth" type="number" min="1" max="10" value="2">
    <label for="exclude">Exclude file types (optional)</label><input id="exclude" placeholder=".iso, .vmdk, .bak, .tar.gz" autocomplete="off">
    <div class="hint" style="margin:4px 0 0">Matches the end of the file name, any case. Files with no extension are never excluded.</div>
    <div class="row" style="margin-top:14px"><button id="btnStart" class="primary">Start scan</button><button id="btnStop" class="danger" disabled>Stop</button></div>
    <div id="scanmsg" class="msg"></div>
  </div>
</div>
<div>
<!-- Live tiles, refreshed every 1.5 seconds from /api/status. No requests go to ONTAP for this. -->
  <div class="tiles">
    <div class="tile"><b id="t_dirs">0</b><span>folders scanned</span></div>
    <div class="tile"><b id="t_files">0</b><span>files checked</span></div>
    <div class="tile hot"><b id="t_cold">0</b><span id="t_cold_s">cold files</span></div>
    <div class="tile hot"><b id="t_coldb">0 B</b><span id="t_pct">cold size</span></div>
    <div class="tile"><b id="t_rate">0</b><span>folders per second</span></div>
    <div class="tile"><b id="t_time">0:00</b><span id="t_queue">elapsed</span></div>
  </div>
  <div id="volprog" class="hint" style="margin:0 0 8px"></div>
  <div class="panel">
<!-- Result tabs. Everything shown here comes from results already held on the scan host. -->
    <div class="tabs" id="tabs">
      <button data-t="summary" class="on">Summary</button><button data-t="charts">Charts</button><button data-t="files">Files</button>
      <button data-t="errors">Errors <span id="errc"></span></button><button data-t="history">Saved scans</button>
    </div>
    <div id="tab_summary">
      <div id="exnote" class="hint" style="margin-top:0"></div>
      <h2>Cold data by age</h2><div class="tbl"><table id="buckets"></table></div>
      <div id="volsec" style="display:none">
        <h2 style="margin-top:20px">By volume</h2><div class="tbl"><table id="voltbl"></table></div>
        <div id="skipnote" class="hint"></div>
      </div>
      <h2 style="margin-top:20px">Largest cold folders</h2><div class="tbl"><table id="topdirs"></table></div>
    </div>
<!-- Charts tab: filled in by drawCharts() in the script below. -->
    <div id="tab_charts" style="display:none"><div id="charts"></div></div>
    <div id="tab_files" style="display:none">
      <input id="fq" placeholder="Filter by path" style="margin-bottom:6px">
<!-- Files tab filters. They only narrow the rows already collected; they never rescan. -->
      <div class="filters">
        <div><label for="fmin">Size at least</label><div class="row"><input id="fmin" type="number" min="0" step="any" placeholder="0"><select id="fminu" aria-label="Minimum size unit"><option value="1024">KiB</option><option value="1048576">MiB</option><option value="1073741824" selected>GiB</option></select></div></div>
        <div><label for="fmax">Size at most</label><div class="row"><input id="fmax" type="number" min="0" step="any" placeholder="no limit"><select id="fmaxu" aria-label="Maximum size unit"><option value="1024">KiB</option><option value="1048576">MiB</option><option value="1073741824" selected>GiB</option></select></div></div>
        <div><label for="fmod">Not modified for (days)</label><input id="fmod" type="number" min="0" placeholder="e.g. 730"></div>
        <div><label for="facc">Not accessed for (days)</label><input id="facc" type="number" min="0" placeholder="e.g. 730"></div>
        <div id="fvolwrap" style="display:none"><label for="fvol">Volume contains</label><input id="fvol" placeholder="svm1:vol (start with = for exact)"></div>
        <div><label for="fext">Only these file types</label><input id="fext" placeholder=".vmdk, .iso"></div>
        <div style="align-self:end"><button id="fclear">Clear filters</button></div>
      </div>
<!-- Quick sorts: each button fills in the three sort levels below with a common combination. -->
      <div class="presets"><span class="hint" style="margin:0">Quick sorts</span><button data-p="size:desc">Largest files</button><button data-p="mtime:asc,size:desc">Longest unmodified</button><button data-p="atime:asc,size:desc">Least recently accessed</button><button data-p="mtime:asc,atime:asc,size:desc">Coldest, then largest</button></div>
      <div id="sorts"></div>
      <div class="tbl"><table id="files"></table></div>
      <div class="pager"><button id="prev">Previous</button><button id="next">Next</button><span id="pginfo"></span><span style="flex:1"></span><a id="dl" href="#"><button>Download CSV</button></a></div>
      <div id="trunc" class="hint"></div>
    </div>
    <div id="tab_errors" style="display:none"><div class="tbl"><table id="errs"></table></div></div>
    <div id="tab_history" style="display:none"><div class="tbl"><table id="hist"></table></div></div>
  </div>
</div>
</main>
<script>
// Helpers.  $(id) = find an element by id.
const $=id=>document.getElementById(id);
// Escape text before putting it into HTML. File names and error messages come from ONTAP, so
// they are treated as untrusted: a hostile file name must never be able to run script.
const esc=s=>String(s).replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
// Bytes to a readable size (KiB, MiB, GiB, ... using 1024).
const fmtB=n=>{const u=["B","KiB","MiB","GiB","TiB","PiB"];let i=0;n=Number(n)||0;while(n>=1024&&i<u.length-1){n/=1024;i++}return (i?n.toFixed(n<10?2:1):n)+" "+u[i]};
// Number with thousands separators.
const fmtN=n=>Number(n||0).toLocaleString();
// Seconds to m:ss or h:mm:ss.
const fmtT=s=>{s=Math.floor(s);const h=Math.floor(s/3600),m=Math.floor(s%3600/60),x=s%60;return (h?h+":"+String(m).padStart(2,"0"):m)+":"+String(x).padStart(2,"0")};
// Page state:
//   token     - access token, kept for this browser tab only (sessionStorage)
//   page      - current page of the Files table, starting at 0
//   tab       - the tab being shown
//   lastState - previous scan state, used to refresh the Files tab once a scan finishes
let token=sessionStorage.getItem("tok")||"", page=0, tab="summary", lastState="idle";
// One function for every call to this script. GET by default; POST with a JSON body if `body`
// is given. Adds the token header. On a 401 it asks for the token once and retries. A failed
// call throws an Error carrying the message the server sent.
async function api(path,body){
  const opt={headers:{"X-Token":token}};
  if(body!==undefined){opt.method="POST";opt.headers["Content-Type"]="application/json";opt.body=JSON.stringify(body)}
  let r=await fetch(path,opt);
  if(r.status===401){token=prompt("Access token for this server:")||"";sessionStorage.setItem("tok",token);
    opt.headers["X-Token"]=token;r=await fetch(path,opt)}
  let j={};try{j=await r.json()}catch(e){}
  if(!r.ok)throw new Error(j.error||("HTTP "+r.status));
  return j;
}
// The connection fields of the Cluster panel, as the API expects them.
const conn=()=>({cluster:$("cluster").value,user:$("user").value,password:$("password").value,tls:$("tls").value,ca:$("ca").value});
// Show a short message under a panel. cls is "ok" (green) or "bad" (red).
function say(id,text,cls){const e=$(id);e.textContent=text;e.className="msg "+(cls||"")}
// Show the CA file box only when "Verify with CA file" is chosen.
$("tls").onchange=()=>{$("cawrap").style.display=$("tls").value==="ca"?"block":"none"};
// Test connection: asks the script, which asks ONTAP for the cluster name and version.
$("btnTest").onclick=async()=>{say("connmsg","Connecting...");
  try{const r=await api("/api/test",conn());say("connmsg","Connected to "+r.name+" ("+r.version+")","ok")}catch(e){say("connmsg",e.message,"bad")}};
// Volume list: fills the picker. volMap remembers uuid -> name, so the scan and its CSV can use the readable name.
// VOLS keeps the whole list for the checklist and for the scan preview.
let volMap={}, VOLS=[], TICK={};
const SKIPWORD={system:"system volume",svm_root:"SVM root",constituent:"FlexGroup constituent",offline:"not online",dp:"DP (SnapMirror destination)",not_found:"no longer on the cluster"};
$("btnVols").onclick=async()=>{say("connmsg","Loading volumes...");
  try{const r=await api("/api/volumes",conn());volMap={};VOLS=r.volumes;TICK={};
    $("vols").innerHTML=r.volumes.map(v=>{volMap[v.uuid]=v.name;return `<option value="${esc(v.uuid)}">${esc(v.svm)}:${esc(v.name)} (${esc(v.type||v.state)})</option>`}).join("");
    $("svms").innerHTML=[...new Set(r.volumes.map(v=>v.svm))].map(n=>`<option value="${esc(n)}">`).join("");
    drawVlist();updatePreview();
    say("connmsg",r.volumes.length+" volumes loaded.","ok")}catch(e){say("connmsg",e.message,"bad")}};
// Scope selector: show only the inputs the chosen scope needs.
function scopeUI(){const sc=$("scope").value;
  $("sc_volume").style.display=sc==="volume"?"block":"none";$("sc_selected").style.display=sc==="selected"?"block":"none";
  $("sc_svm").style.display=sc==="svm"?"block":"none";$("sc_dp").style.display=(sc==="svm"||sc==="cluster")?"block":"none";updatePreview()}
$("scope").onchange=scopeUI;$("svm").oninput=updatePreview;$("incdp").onchange=updatePreview;
// Checklist of volumes for "Selected volumes". The filter box narrows the visible rows; ticks are remembered by UUID.
function drawVlist(){const f=$("vfilter").value.trim().toLowerCase();
  const rows=VOLS.filter(v=>(v.svm+":"+v.name).toLowerCase().includes(f));
  $("vlist").innerHTML=rows.length?rows.map(v=>`<label><input type="checkbox" data-u="${esc(v.uuid)}"${TICK[v.uuid]?" checked":""}>${esc(v.svm)}:${esc(v.name)}<span class="tag">${esc(v.type||v.state)}${v.skip?" · "+esc(SKIPWORD[v.skip]||v.skip):""}</span></label>`).join(""):'<span class="hint" style="margin:0">'+(VOLS.length?"No match.":"Click Load volumes first.")+'</span>'}
$("vfilter").oninput=drawVlist;
$("vlist").onchange=e=>{const u=e.target.dataset.u;if(u){TICK[u]=e.target.checked;updatePreview()}};
$("vElig").onclick=()=>{VOLS.forEach(v=>{if(!v.skip)TICK[v.uuid]=true});drawVlist();updatePreview()};
$("vNone").onclick=()=>{TICK={};drawVlist();updatePreview()};
// One-line preview of what the scan will cover, worked out from the loaded volume list (no request to ONTAP).
function updatePreview(){const sc=$("scope").value,el=$("preview");
  if(sc==="volume"){el.textContent="";return}
  if(!VOLS.length){el.textContent="Load volumes to see how many will be scanned.";return}
  if(sc==="selected"){const n=Object.values(TICK).filter(Boolean).length;el.textContent=n+" volume"+(n===1?"":"s")+" ticked. Ticked volumes are always scanned.";return}
  let pool=VOLS;if(sc==="svm"){const n=$("svm").value.trim().toLowerCase();pool=VOLS.filter(v=>v.svm.toLowerCase()===n)}
  const dp=$("incdp").checked,go=pool.filter(v=>!v.skip||(v.skip==="dp"&&dp)),cnt={};
  pool.forEach(v=>{if(v.skip&&!(v.skip==="dp"&&dp))cnt[v.skip]=(cnt[v.skip]||0)+1});
  el.textContent=go.length+" volume"+(go.length===1?"":"s")+" will be scanned"+(Object.keys(cnt).length?"; skipped: "+Object.entries(cnt).map(([k,n])=>n+" "+(SKIPWORD[k]||k)).join(", "):"")+"."}
// Start scan: sends the Cluster fields and the Scan settings. Only this button (and Test and Load volumes) leads to requests to ONTAP.
$("btnStart").onclick=async()=>{
  const b=Object.assign(conn(),{scope:$("scope").value,volume:$("volume").value.trim(),volume_name:volMap[$("volume").value.trim()]||"",root:$("root").value,
    volumes:Object.keys(TICK).filter(u=>TICK[u]),svm:$("svm").value.trim(),include_dp:$("incdp").checked,
    days:$("days").value,workers:$("workers").value,mode:$("mode").value,depth:$("depth").value,exclude:$("exclude").value});
  say("scanmsg","Starting...");
  try{await api("/api/scan/start",b);say("scanmsg","");page=0;poll()}catch(e){say("scanmsg",e.message,"bad")}};
// Stop: sets the stop flag on the scan. Workers stop between entries; what was found so far is kept.
$("btnStop").onclick=async()=>{try{await api("/api/scan/stop",{});say("scanmsg","Stopping after the current folders finish...")}catch(e){say("scanmsg",e.message,"bad")}};
// Tab switching: show one tab, hide the others, and load the data that tab needs.
document.querySelectorAll("#tabs button").forEach(b=>b.onclick=()=>{tab=b.dataset.t;
  document.querySelectorAll("#tabs button").forEach(x=>x.classList.toggle("on",x===b));
  ["summary","charts","files","errors","history"].forEach(t=>$("tab_"+t).style.display=t===tab?"block":"none");
  if(tab==="files")loadFiles();if(tab==="history")loadHistory();if(tab==="charts")drawCharts(LAST)});
// The most recent /api/status answer. The Charts tab draws from it, so charts update as the scan runs.
let LAST=null;
// Treemap layout. `items` must be sorted largest first. The list is split into two groups whose
// totals are as close to half each as possible, the rectangle is cut across its longer side in
// that proportion, and each half is laid out the same way. The result is a list of boxes whose
// area is proportional to the value (cold size).
function treemap(items,x,y,w,h,out){
  if(!items.length)return;
  if(items.length===1){out.push(Object.assign({},items[0],{x:x,y:y,w:w,h:h}));return}
  const tot=items.reduce((a,i)=>a+i.v,0);let k=1,acc=items[0].v;
  while(k<items.length-1&&acc<tot/2){acc+=items[k].v;k++}
  const A=items.slice(0,k),B=items.slice(k);
  if(w>=h){const wa=w*acc/tot;treemap(A,x,y,wa,h,out);treemap(B,x+wa,y,w-wa,h,out)}
  else{const ha=h*acc/tot;treemap(A,x,y,w,ha,out);treemap(B,x,y+ha,w,h-ha,out)}
}
// Vertical bar chart (used for age and for year). Bars are scaled to the biggest value; hovering a bar shows exact numbers.
function vbars(items,label){
  if(!items.length)return '<div class="empty">No data yet.</div>';
  const n=items.length,W=Math.max(420,n*46),H=210,top=22,bot=30,step=(W-20)/n,bw=Math.min(44,step-8),mx=Math.max(1,...items.map(i=>i.v));
  return `<svg class="ch" viewBox="0 0 ${W} ${H}" role="img" aria-label="${esc(label)}">`+items.map((it,i)=>{
    const h=(H-top-bot)*it.v/mx,x=10+i*step+(step-bw)/2,y=H-bot-h;
    return `<g><title>${esc(it.t)}</title><rect x="${x}" y="${y}" width="${bw}" height="${Math.max(h,1)}" rx="2" fill="var(--ice)"/>`+
      (step>=60?`<text x="${x+bw/2}" y="${y-5}" text-anchor="middle" class="m">${fmtB(it.v)}</text>`:"")+
      `<text x="${x+bw/2}" y="${H-12}" text-anchor="middle">${esc(it.l)}</text></g>`}).join("")+"</svg>";
}
// Horizontal bar chart (used for file types). Bars for real file types are clickable: they open the Files tab filtered to that type.
function hbars(items,lw){
  lw=lw||78;const mx=Math.max(1,...items.map(i=>i.v)),rh=26,W=lw>100?lw+480:560,rw=150;
  return `<svg class="ch" viewBox="0 0 ${W} ${items.length*rh+4}" role="img" aria-label="Cold size by ${lw>100?"volume":"file type"}">`+items.map((it,i)=>{
    const y=i*rh+2,bw=(W-lw-rw)*it.v/mx;
    const attr=it.vol?` data-vol="${esc(it.vol)}" style="cursor:pointer"`:(it.ext&&it.ext.charAt(0)==="."?` data-ext="${esc(it.ext)}" style="cursor:pointer"`:"");
    return `<g${attr}><title>${esc(it.t)}</title><text x="0" y="${y+16}">${esc(it.l)}</text><rect x="${lw}" y="${y+4}" width="${Math.max(bw,1)}" height="14" rx="2" fill="var(--ice)"/><text x="${lw+bw+6}" y="${y+16}" class="m">${fmtB(it.v)} · ${fmtN(it.f)} files</text></g>`}).join("")+"</svg>";
}
// Jump to the Files tab with a path filter and/or file type filter already filled in (used by clicks on chart boxes and bars).
function goFiles(path,ext,vol){$("fq").value=path;$("fext").value=ext;$("fvol").value=vol||"";page=0;document.querySelector('#tabs button[data-t="files"]').click()}
// Build all five charts from one status answer (s):
//   donut   - cold versus not cold, by size
//   age     - cold size per age bucket
//   tree    - cold size per folder (top 30 plus one grey "all other" box)
//   types   - top 10 file types plus an "other" bar
//   years   - cold size per year last modified
// The charts are plain SVG strings, so no chart library is needed.
function drawCharts(s){
  const el=$("charts");
  if(!s||!s.buckets||!s.files){el.innerHTML='<div class="empty">Start a scan to see charts.</div>';return}
  const tot=s.total_bytes||0,cold=s.cold_bytes||0,pct=tot?cold/tot:0,C=2*Math.PI*70;
  const donut=`<svg class="ch" viewBox="0 0 260 190" role="img" aria-label="Cold share of scanned data"><circle cx="95" cy="95" r="70" fill="none" stroke="var(--line)" stroke-width="24"/><circle cx="95" cy="95" r="70" fill="none" stroke="var(--ice)" stroke-width="24" stroke-dasharray="${pct*C} ${C}" transform="rotate(-90 95 95)"/><text x="95" y="93" text-anchor="middle" style="font-size:24px;font-weight:650">${(pct*100).toFixed(1)}%</text><text x="95" y="113" text-anchor="middle" class="m">cold by size</text><rect x="182" y="70" width="10" height="10" rx="2" fill="var(--ice)"/><text x="198" y="79">Cold</text><text x="198" y="94" class="m">${fmtB(cold)}</text><rect x="182" y="112" width="10" height="10" rx="2" fill="var(--line)"/><text x="198" y="121">Not cold</text><text x="198" y="136" class="m">${fmtB(Math.max(0,tot-cold))}</text></svg>`;
  const age=vbars(s.buckets.map(b=>({l:b.label,v:b.bytes,t:b.label+": "+fmtB(b.bytes)+", "+fmtN(b.files)+" files"})),"Cold size by age");
  const yrs=vbars((s.years||[]).map(y=>({l:y.year,v:y.bytes,t:y.year+": "+fmtB(y.bytes)+", "+fmtN(y.files)+" files"})),"Cold size by year last modified");
  const dirs=(s.top_dirs||[]).filter(d=>d.bytes>0).map(d=>({v:d.bytes,path:d.path,files:d.files,vol:s.multi?d.volume:""}));
  const rest=cold-dirs.reduce((a,d)=>a+d.v,0);
  if(rest>cold*0.005)dirs.push({v:rest,path:"",files:0,other:1});
  dirs.sort((a,b)=>b.v-a.v);dirs.forEach((d,i)=>{d.rank=i});
  const out=[];treemap(dirs,0,0,700,300,out);
  const tree=dirs.length?`<svg class="ch" viewBox="0 0 700 300" role="img" aria-label="Cold size by folder">`+out.map(t=>{
    const name=t.other?"All other folders":(t.vol?t.vol+" "+t.path:t.path),mc=Math.floor((t.w-14)/7),lab=name.length>mc?"…"+name.slice(-(mc-1)):name;
    const fill=t.other?'fill="var(--line)"':`fill="var(--ice)" fill-opacity="${(0.7+0.3*(1-t.rank/Math.max(1,dirs.length-1))).toFixed(2)}"`;
    const tcls=t.other?"":' class="tt"';
    const attr=t.other?"":` data-path="${esc(t.path)}"${t.vol?` data-vol="${esc(t.vol)}"`:""} style="cursor:pointer"`;
    return `<g${attr}><title>${esc(name)}\n${fmtB(t.v)}${t.files?", "+fmtN(t.files)+" files":""}</title><rect x="${t.x}" y="${t.y}" width="${t.w}" height="${t.h}" ${fill} stroke="var(--panel)" stroke-width="2"/>`+
      (t.w>60&&t.h>36&&mc>3?`<text x="${t.x+8}" y="${t.y+18}"${tcls}>${esc(lab)}</text><text x="${t.x+8}" y="${t.y+34}"${tcls} style="font-weight:400">${fmtB(t.v)}</text>`:"")+"</g>"}).join("")+"</svg>":'<div class="empty">No cold files found yet.</div>';
  const ty=(s.types||[]).slice(0,10).map(t=>({l:t.ext,ext:t.ext,v:t.bytes,f:t.files,t:t.ext+": "+fmtB(t.bytes)+", "+fmtN(t.files)+" files"}));
  const trest=cold-ty.reduce((a,t)=>a+t.v,0),frest=(s.cold_files||0)-ty.reduce((a,t)=>a+t.f,0);
  if(trest>cold*0.005)ty.push({l:"other",v:trest,f:Math.max(frest,0),t:"All other file types"});
  const types=ty.length?hbars(ty):'<div class="empty">No data yet.</div>';
  let byvol="";
  if(s.multi&&(s.volumes||[]).length){const vv=s.volumes.filter(v=>v.cold_bytes>0).slice(0,15).map(v=>({l:v.key.length>26?"…"+v.key.slice(-25):v.key,vol:v.key,v:v.cold_bytes,f:v.cold_files,t:v.key+": "+fmtB(v.cold_bytes)+", "+fmtN(v.cold_files)+" files"}));
    if(vv.length)byvol=`<div class="cwide"><h2>By volume</h2><div class="hint" style="margin:0 0 6px">Cold size per volume (top ${vv.length}). Click a bar to list its files.</div>${hbars(vv,170)}</div>`}
  el.innerHTML=`<div class="cgrid"><div><h2>Cold versus the rest</h2>${donut}</div><div><h2>Cold data by age</h2>${age}</div>`+
    `<div class="cwide"><h2>Where the cold data is</h2><div class="hint" style="margin:0 0 6px">Box size is cold size. Click a box to list its files.</div>${tree}</div>`+
    `<div><h2>By file type</h2><div class="hint" style="margin:0 0 6px">Click a bar to list those files.</div>${types}</div><div><h2>By year last modified</h2>${yrs}</div>${byvol}</div>`;
}
// One click handler for the whole Charts tab: any box or bar carrying data-path or data-ext jumps to the Files tab.
$("charts").onclick=e=>{const g=e.target.closest("[data-path],[data-ext]");if(g)goFiles(g.dataset.path||"",g.dataset.ext||"",g.dataset.vol?"="+g.dataset.vol:"")};
// A table row that spans all columns, for "nothing to show yet" messages.
function emptyRow(cols,text){return `<tr><td colspan="${cols}" class="empty">${text}</td></tr>`}
// Draw everything that depends on one /api/status answer: header pill, buttons, tiles, age
// table, folder table, notes, errors and the download link. No requests to ONTAP happen here.
function render(s){
  const run=s.state==="running"||s.state==="starting";
  $("pill").textContent=s.state;$("pill").className="pill "+s.state;
  $("btnStart").disabled=run;$("btnStop").disabled=!run;
  $("hdrmsg").textContent=s.message||"";
  if(s.state==="idle")return;
  LAST=s;if(tab==="charts")drawCharts(s);
  $("t_dirs").textContent=fmtN(s.dirs);$("t_files").textContent=fmtN(s.files);
  $("t_cold").textContent=fmtN(s.cold_files);$("t_coldb").textContent=fmtB(s.cold_bytes);
  $("t_pct").textContent=s.total_bytes?("cold size, "+(100*s.cold_bytes/s.total_bytes).toFixed(1)+"% of "+fmtB(s.total_bytes)):"cold size";
  $("t_rate").textContent=s.dirs_per_sec.toFixed(1);$("t_time").textContent=fmtT(s.elapsed);
  $("t_queue").textContent=run?("elapsed, "+fmtN(s.queued)+" folders waiting"):"elapsed";
  const mx=Math.max(1,...s.buckets.map(b=>b.bytes));
  $("buckets").innerHTML="<tr><th>Age</th><th class='n'>Files</th><th class='n'>Size</th><th style='width:40%'></th></tr>"+
    s.buckets.map(b=>`<tr><td>${esc(b.label)}</td><td class="n">${fmtN(b.files)}</td><td class="n">${fmtB(b.bytes)}</td><td><div class="bar" style="width:${100*b.bytes/mx}%"></div></td></tr>`).join("");
  setMulti(!!s.multi);
  const vc=s.multi?1:0;
  $("topdirs").innerHTML="<tr>"+(vc?"<th>Volume</th>":"")+"<th>Folder</th><th class='n'>Cold files</th><th class='n'>Cold size</th></tr>"+
    (s.top_dirs.length?s.top_dirs.map(d=>`<tr>${vc?`<td class="p">${esc(d.volume)}</td>`:""}<td class="p">${esc(d.path)}</td><td class="n">${fmtN(d.files)}</td><td class="n">${fmtB(d.bytes)}</td></tr>`).join(""):emptyRow(3+vc,"No cold files found yet."));
  // Multi-volume scans: progress line, per-volume table and the list of volumes that were skipped.
  $("volsec").style.display=s.multi?"block":"none";
  $("volprog").textContent=s.multi?("Volume "+Math.min(s.vol_done+(run?1:0),s.vol_total)+" of "+s.vol_total+(run&&s.vol_current?": "+s.vol_current:"")+" · "+s.vol_done+" finished"):"";
  if(s.multi){
    $("voltbl").innerHTML="<tr><th>Volume</th><th>State</th><th class='n'>Files checked</th><th class='n'>Cold files</th><th class='n'>Cold size</th><th class='n'>Cold %</th></tr>"+
      s.volumes.map(v=>`<tr><td class="p"><a href="#" data-vol="${esc(v.key)}">${esc(v.key)}</a></td><td>${esc(v.state)}${v.error?" – "+esc(v.error):""}</td><td class="n">${fmtN(v.files)}</td><td class="n">${fmtN(v.cold_files)}</td><td class="n">${fmtB(v.cold_bytes)}</td><td class="n">${v.total_bytes?(100*v.cold_bytes/v.total_bytes).toFixed(1)+"%":""}</td></tr>`).join("");
    const sc=s.skip_counts||{},tot=Object.values(sc).reduce((a,b)=>a+b,0);
    $("skipnote").textContent=tot?("Skipped "+tot+" volume"+(tot===1?"":"s")+": "+Object.entries(sc).map(([k,n])=>n+" "+(SKIPWORD[k]||k)).join(", ")+(s.volumes.length<s.vol_total?". Only the "+s.volumes.length+" volumes with the most cold data are listed above.":"")+"."):(s.volumes.length<s.vol_total?"Only the "+s.volumes.length+" volumes with the most cold data are listed.":"")}
  $("exnote").textContent=s.excl_files?("Excluded by file type: "+fmtN(s.excl_files)+" files, "+fmtB(s.excl_bytes)+". They are not counted in the totals.") :"";
  $("errc").textContent=s.error_count?"("+fmtN(s.error_count)+")":"";
  $("errs").innerHTML="<tr><th>Where</th><th>Error</th></tr>"+(s.errors.length?s.errors.map(e=>`<tr><td class="p">${esc(e.path)}</td><td>${esc(e.error)}</td></tr>`).join(""):emptyRow(2,"No folder errors."));
  $("trunc").textContent=s.unknown_ts?fmtN(s.unknown_ts)+" files had no usable timestamp and were not counted.":"";
  $("dl").href="/api/file?name="+encodeURIComponent(s.csv)+(token?"&token="+encodeURIComponent(token):"");
  if(!run&&lastState==="running"&&tab==="files")loadFiles();
  lastState=s.state;
}
// Fetch one page (100 rows) of the Files table from /api/results with the current search, sort
// levels and filters. The script answers from rows already in memory, so this never rescans.
async function loadFiles(){
  try{const q=encodeURIComponent($("fq").value),sort=encodeURIComponent(sortSpec());
    const r=await api(`/api/results?q=${q}&sort=${sort}&offset=${page*100}&limit=100${filterQS()}`);
    $("files").innerHTML=hdr()+
      (r.rows.length?r.rows.map(x=>`<tr>${MULTI?`<td class="p">${esc(x[7]||"")}</td>`:""}<td class="p">${esc(x[0])}</td><td class="n">${fmtB(x[1])}</td><td class="n">${fmtN(x[4])}</td><td>${esc(x[3].slice(0,10))}</td><td>${esc(x[2].slice(0,10))}</td></tr>`).join(""):emptyRow(5+(MULTI?1:0),"No cold files to show yet."));
    document.querySelectorAll("#files th[data-k]").forEach(h=>h.onclick=()=>headSort(h.dataset.k));
    $("pginfo").textContent=r.total?`${page*100+1}-${Math.min(r.total,page*100+100)} of ${fmtN(r.total)} files, ${fmtB(r.total_bytes||0)}`:"";
    $("prev").disabled=page===0;$("next").disabled=(page+1)*100>=r.total;
  }catch(e){}
}
// Paging, search box and filter boxes: any change goes back to page 1 and reloads the table.
$("prev").onclick=()=>{page=Math.max(0,page-1);loadFiles()};$("next").onclick=()=>{page++;loadFiles()};
$("fq").oninput=()=>{page=0;loadFiles()};
// Turn the filter boxes into query parameters. Sizes are converted to bytes using the unit
// drop-downs. Blank boxes add nothing.
function filterQS(){const p=[],v=id=>$(id).value.trim();
  if(v("fmin")!=="")p.push("fmin="+Math.round(Number(v("fmin"))*Number($("fminu").value)));
  if(v("fmax")!=="")p.push("fmax="+Math.round(Number(v("fmax"))*Number($("fmaxu").value)));
  if(v("fmod")!=="")p.push("mod="+encodeURIComponent(v("fmod")));
  if(v("facc")!=="")p.push("acc="+encodeURIComponent(v("facc")));
  if(v("fext")!=="")p.push("ext="+encodeURIComponent(v("fext")));
  if(v("fvol")!=="")p.push("vol="+encodeURIComponent(v("fvol")));
  return p.length?"&"+p.join("&"):""}
["fmin","fminu","fmax","fmaxu","fmod","facc","fext","fvol"].forEach(id=>$(id).oninput=()=>{page=0;loadFiles()});
$("fclear").onclick=()=>{["fmin","fmax","fmod","facc","fext","fq","fvol"].forEach(id=>$(id).value="");page=0;loadFiles()};
// Sorting model. SORTS holds up to three levels, each {k: column, d: "asc" or "desc"}.
// Level 1 is the main sort and each later level only breaks ties. KEYS lists the columns,
// DEFDIR the natural first direction for each, DIRLBL the direction wording shown per column.
let KEYS=[["size","Size"],["age","Cold age (days)"],["mtime","Modified date"],["atime","Accessed date"],["path","Path"]];
const DEFDIR={size:"desc",age:"desc",path:"asc",mtime:"asc",atime:"asc",volume:"asc"};
const DIRLBL={size:["Largest first","Smallest first"],age:["Longest first","Shortest first"],mtime:["Newest first","Oldest first"],atime:["Newest first","Oldest first"],path:["Z to A","A to Z"],volume:["Z to A","A to Z"]};
// MULTI is true while the shown scan covers several volumes: then the Files tab gets a Volume
// column, a Volume filter and a Volume sort option. setMulti() switches them when it changes.
let MULTI=false;
function setMulti(m){if(m===MULTI)return;MULTI=m;
  KEYS=KEYS.filter(k=>k[0]!=="volume");if(m)KEYS.push(["volume","Volume"]);
  $("fvolwrap").style.display=m?"block":"none";
  if(!m){$("fvol").value="";SORTS=SORTS.map(x=>x.k==="volume"?{k:"",d:"desc"}:x)}
  drawSorts();if(tab==="files")loadFiles()}
let SORTS=[{k:"size",d:"desc"},{k:"",d:"desc"},{k:"",d:"desc"}];
// The current levels as the text the API expects, for example "mtime:asc,size:desc".
function sortSpec(){return SORTS.filter(s=>s.k).map(s=>s.k+":"+s.d).join(",")||"size:desc"}
// Table header row. Clicking a column header calls headSort(); an arrow marks the main sort.
function hdr(){const h=(k,l,c)=>`<th class="s ${c}" data-k="${k}">${l}${SORTS[0].k===k?(SORTS[0].d==="asc"?" ↑":" ↓"):""}</th>`;
  return "<tr>"+(MULTI?h("volume","Volume",""):"")+h("path","Path","")+h("size","Size","n")+h("age","Age (days)","n")+h("mtime","Modified","")+h("atime","Accessed","")+"</tr>"}
// Draw the three sort-level rows (column drop-down and direction drop-down) and react to changes.
function drawSorts(){
  $("sorts").innerHTML=SORTS.map((s,i)=>{const l=DIRLBL[s.k||"size"];
    return `<div class="sortrow"><span>${i?"then by":"Sort by"}</span><select aria-label="Sort level ${i+1}" data-i="${i}" data-f="k">${i?'<option value="">(none)</option>':""}${KEYS.map(k=>`<option value="${k[0]}"${s.k===k[0]?" selected":""}>${k[1]}</option>`).join("")}</select>`+
    `<select aria-label="Direction ${i+1}" data-i="${i}" data-f="d"${s.k?"":" disabled"}><option value="desc"${s.d==="desc"?" selected":""}>${l[0]}</option><option value="asc"${s.d==="asc"?" selected":""}>${l[1]}</option></select></div>`}).join("");
  $("sorts").querySelectorAll("select").forEach(el=>el.onchange=()=>{const i=+el.dataset.i;
    if(el.dataset.f==="k"){SORTS[i].k=el.value;SORTS[i].d=el.value?DEFDIR[el.value]:"desc"}else SORTS[i].d=el.value;
    drawSorts();page=0;loadFiles()});
}
// Header click: make column k the main sort (click again to reverse it); the other levels shift down.
function headSort(k){const cur=SORTS[0];
  if(cur.k===k)cur.d=cur.d==="asc"?"desc":"asc";else{SORTS=SORTS.filter((s,i)=>i>0&&s.k!==k);SORTS.unshift({k,d:DEFDIR[k]});while(SORTS.length<3)SORTS.push({k:"",d:"desc"});SORTS=SORTS.slice(0,3)}
  drawSorts();page=0;loadFiles()}
// Quick sort buttons: replace the sort levels with the preset stored in the button (data-p).
document.querySelectorAll(".presets button").forEach(b=>b.onclick=()=>{
  SORTS=b.dataset.p.split(",").map(x=>{const [k,d]=x.split(":");return{k,d}});while(SORTS.length<3)SORTS.push({k:"",d:"desc"});
  drawSorts();page=0;loadFiles()});
// Saved scans tab: list the CSV files on the scan host with download links.
async function loadHistory(){
  try{const r=await api("/api/history");
    $("hist").innerHTML="<tr><th>File</th><th>Saved</th><th class='n'>Size</th><th></th></tr>"+(r.files.length?r.files.map(f=>
      `<tr><td class="p">${esc(f.name)}</td><td>${esc(f.modified)}</td><td class="n">${fmtB(f.bytes)}</td><td><a href="/api/file?name=${encodeURIComponent(f.name)}${token?"&token="+encodeURIComponent(token):""}">Download CSV</a>${f.can_open?` · <a href="#" data-open="${esc(f.name)}">Open</a>`:""}</td></tr>`).join(""):emptyRow(4,"No saved scans yet. Each scan saves a CSV on the server."));
  }catch(e){}
}
// Saved scans tab: "Open" loads a finished scan from its database file, so its summary, charts
// and Files tab can be used again after a restart. Nothing is sent to ONTAP.
$("hist").onclick=async e=>{const a=e.target.closest("[data-open]");if(!a)return;e.preventDefault();
  try{await api("/api/scan/open",{name:a.dataset.open});page=0;await poll();document.querySelector('#tabs button[data-t="summary"]').click()}catch(err){alert(err.message)}};
// In the By volume table, a volume name opens the Files tab filtered to that volume.
$("voltbl").onclick=e=>{const a=e.target.closest("[data-vol]");if(a){e.preventDefault();goFiles("","","="+a.dataset.vol)}};
// Fetch the status and redraw. While a scan runs and the Files tab is open, its table is refreshed too.
async function poll(){
  try{const s=await api("/api/status");render(s);if(tab==="files"&&(s.state==="running"))loadFiles()}catch(e){$("hdrmsg").textContent=e.message}
}
// Start-up: draw the sort rows, fetch the status once, then refresh every 1.5 seconds.
drawSorts();poll();setInterval(poll,1500);
</script></body></html>
"""


def main():
    """Read the command line, set up the server (with TLS if asked) and run until Ctrl+C."""
    ap = argparse.ArgumentParser(description="Cryo: cold data finder for ONTAP NAS volumes (stdlib only)")
    ap.add_argument("--host", default="127.0.0.1", help="bind address (default 127.0.0.1)")
    ap.add_argument("--port", type=int, default=8080)
    ap.add_argument("--outdir", default="scans", help="where CSV results are saved")
    ap.add_argument("--token", default=os.environ.get("CRYO_TOKEN"),
                    help="require this access token for the GUI/API (or set CRYO_TOKEN)")
    ap.add_argument("--certfile")
    ap.add_argument("--keyfile")
    args = ap.parse_args()

    # Store the settings where the request handlers can see them.
    App.token, App.outdir = args.token, args.outdir
    os.makedirs(App.outdir, exist_ok=True)
    # Create the HTTP server. 127.0.0.1 (the default) means only this computer can connect;
    # use --host with an address, plus --token and TLS, to let other computers reach the GUI.
    srv = Server((args.host, args.port), Handler)
    scheme = "http"
    # HTTPS for the GUI: wrap the listening socket in TLS using the certificate and key given.
    if args.certfile:
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        ctx.load_cert_chain(args.certfile, args.keyfile)
        srv.socket = ctx.wrap_socket(srv.socket, server_side=True)
        scheme = "https"
    # Start-up warnings, printed when the GUI is reachable from other computers without protection.
    if args.host not in ("127.0.0.1", "localhost") and not args.token:
        print("WARNING: listening on %s without --token. Anyone who can reach this port "
              "can start scans using credentials they type in." % args.host, file=sys.stderr)
    if args.host not in ("127.0.0.1", "localhost") and scheme == "http":
        print("WARNING: plain HTTP. Cluster passwords typed in the GUI cross the network "
              "unencrypted. Use --certfile/--keyfile or an SSH tunnel.", file=sys.stderr)
    print("Cryo: %s://%s:%d  (results in %s)" % (scheme, args.host, args.port,
                                                           os.path.abspath(App.outdir)))
    # Serve requests until Ctrl+C. A running scan is stopped when the program exits.
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
