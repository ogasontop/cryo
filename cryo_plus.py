#!/usr/bin/env python3
"""
Cryo (cryo.py) - cold data finder for ONTAP NAS volumes, with a browser GUI.

NEW IN 2.0: a Compliance tab next to the cold-data tabs. It runs read-only backup and storage
checks on one or more clusters, using the same cluster login. Its benchmark values are LOCKED:
they come only from the file given with --check-config (write a sample with
--init-check-config). The browser can only switch a benchmark on or off for one run. Reports
(HTML, JSON, CSV) go to --check-out. Written from the ontap_check.py checker; see its notes
on what was and was not tested.

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
import fnmatch
import html
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
# The name shown in the browser tab, the page header and the start-up line. Change it in one place.
APP_NAME = "Cryo"
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
        if not re.match(r"^https?://", host):      # never let urllib open file:// or ftp://
            raise ValueError("Cluster address must be http or https: %s" % host[:60])
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
# Compliance checks (second tab). Read-only: GET requests only.
# --------------------------------------------------------------------------

def ontap_records(client, path, fields=None, fallback=None, params=None):
    """All records of a collection, following ONTAP's next-page links (GET only).

    If the field list is refused with HTTP 400 and a shorter fallback is given, the request is
    repeated with the fallback. Returns (records, note); note says if the fallback was used."""
    note = None
    p = dict(params or {})
    p["max_records"] = 500
    tries = [fields, fallback] if fallback else [fields]
    data = None
    for i, f in enumerate(tries):
        q = dict(p)
        if f:
            q["fields"] = f
        try:
            data = client.get(path, q)
            if i == 1:
                note = "reduced field list used for %s (full list refused)" % path
            break
        except ApiError as e:
            if e.code == 400 and i + 1 < len(tries):
                continue
            raise
    out = []
    while data is not None:
        out.extend(data.get("records") or [])
        nxt = ((data.get("_links") or {}).get("next") or {}).get("href")
        data = client.get(nxt) if nxt else None
    return out, note

VERSION = "1.0"
ORDER = ["FAIL", "UNKNOWN", "NEEDS_INPUT", "PASS", "NA"]
# Words shown to people. The internal keys stay as they are.
LABEL = {"FAIL": "Not met", "UNKNOWN": "Unknown", "NEEDS_INPUT": "Needs input", "PASS": "Met", "NA": "N/A"}

# --------------------------------------------------------------------------- configuration
DEFAULT_CONFIG = {
    "_help": "null means 'not decided yet': the check shows NEEDS_INPUT instead of guessing.",
    "exempt": {
        "_help": "Patterns (* and ? allowed). volumes match 'svm:volume'; svms match the SVM name.",
        "volumes": [],
        "svms": [],
    },
    "capacity": {"aggregate_used_pct_max": None, "volume_used_pct_max": None},
    "volume_baseline": {
        "_help": "Set either key to turn STO-VOL on. state is for example 'online'.",
        "state": None,
        "snapshot_policies": None,
    },
    "sites": {"_help": "Map cluster name to a site label for BKP-003, for example {\"cluster1\": \"Site A\"}."},
    "dr": {
        "allowed_policies": None,
        "allowed_schedules": None,
        "lag_limit_minutes": None,
    },
    "ndmp_allowed_svms": [],
    "exposure": {
        "_help": "Proposed defaults. Change them to match your own definition of exposed.",
        "nfs_open_clients": ["0.0.0.0/0", "::/0", "0.0.0.0", "*"],
        "smb_principals": ["Everyone"],
        "smb_permissions": ["full_control", "change"],
    },
    "plans": {"_help": "Optional remediation notes: a list of {id, owner_role, status, target, note}. Use roles, not names."},
    "severity": {
        "BKP-001": "Critical", "BKP-003": "Critical",
        "BKP-004": "High",
        "BKP-008": "High", "BKP-009": "High", "BKP-010": "High",
        "STO-DNS": "Unrated", "STO-CIFS": "Unrated", "STO-NFS": "Unrated", "STO-SMB": "Unrated",
        "STO-AUD": "Unrated", "STO-VOL": "Unrated", "STO-CAP": "Unrated",
    },
    "tig_links": {"_help": "Map a check id to its TIG web link, for example {\"STO-DNS\": \"https://...\"}."},
    "max_rows_in_html": 200,
}

TITLES = {
    "BKP-001": "No backup capability",
    "BKP-003": "Backup and production co-located", "BKP-004": "NDMP enabled (tape dependency)",
    "BKP-008": "Capacity planning",
    "BKP-009": "DNS, audit and volume protection", "BKP-010": "Inconsistent DR architecture",
    "STO-DNS": "DNS not configured", "STO-CIFS": "CIFS not joined to a domain",
    "STO-NFS": "Exposed NFS exports", "STO-SMB": "Exposed CIFS shares", "STO-AUD": "Audit logging off",
    "STO-VOL": "Volume settings differ from baseline", "STO-CAP": "Capacity over threshold",
}

# Fix text is shown, never run. Labels in <angle brackets> are fill-in placeholders.
FIXES = {
    "BKP-001": ["volume modify -vserver <SVM A> -volume <Volume 1> -snapshot-policy <Policy 1>",
                "snapmirror create -source-path <SVM A>:<Volume 1> -destination-path <SVM B>:<Volume 2> -policy <Policy 1>"],
    "BKP-003": ["snapmirror show -destination-path <SVM B>:<Volume 2>",
                "Move the destination to a cluster at another site, then update the site map."],
    "BKP-004": ["vserver services ndmp off -vserver <SVM A>"],
    "BKP-008": ["storage aggregate show -aggregate <Aggregate 1>",
                "volume show-space -vserver <SVM A> -volume <Volume 1>"],
    "BKP-009": ["Fix the DNS, audit and unprotected-volume items listed."],
    "BKP-010": ["snapmirror show -fields policy,schedule,lag-time,healthy",
                "snapmirror modify -destination-path <SVM B>:<Volume 2> -policy <Policy 1> -schedule <Schedule 1>"],
    "STO-DNS": ["vserver services name-service dns create -vserver <SVM A> -domains <Domain 1> -name-servers <Server 1>"],
    "STO-CIFS": ["vserver cifs show -vserver <SVM A>"],
    "STO-NFS": ["vserver export-policy rule show -vserver <SVM A> -policyname <Policy 1>",
                "vserver export-policy rule modify -vserver <SVM A> -policyname <Policy 1> -ruleindex <Index 1> -clientmatch <Clients 1>"],
    "STO-SMB": ["vserver cifs share access-control show -vserver <SVM A> -share <Share 1>"],
    "STO-AUD": ["vserver audit show -vserver <SVM A>", "vserver audit enable -vserver <SVM A>"],
    "STO-VOL": ["volume modify -vserver <SVM A> -volume <Volume 1> -snapshot-policy <Policy 1>"],
    "STO-CAP": ["storage aggregate show -aggregate <Aggregate 1>", "volume show-space -vserver <SVM A> -volume <Volume 1>"],
}


def deep_merge(base, over):
    out = dict(base)
    for k, v in (over or {}).items():
        if isinstance(v, dict) and isinstance(out.get(k), dict):
            out[k] = deep_merge(out[k], v)
        else:
            out[k] = v
    return out


def load_json(path, what):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError) as e:
        sys.exit("Cannot read %s file %s: %s" % (what, path, e))


# --------------------------------------------------------------------------- data collection
def g(d, *keys, default=None):
    for k in keys:
        if not isinstance(d, dict):
            return default
        d = d.get(k)
        if d is None:
            return default
    return d


def collect_cluster(client, label):
    """Read everything the checks need from one cluster. Each read is independent: one refused
    endpoint becomes an error message, not a crash."""
    d = {"label": label, "name": label, "version": "", "errors": {}, "notes": []}
    try:
        c = client.get("/api/cluster", {"fields": "name,version"})
        d["name"] = c.get("name") or label
        d["version"] = g(c, "version", "full", default="")
    except ApiError as e:
        d["errors"]["cluster"] = str(e)

    def read(key, path, fields, fallback=None, params=None):
        try:
            recs, note = ontap_records(client, path, fields, fallback, params)
            d[key] = recs
            if note:
                d["notes"].append(note)
        except ApiError as e:
            d[key] = None
            d["errors"][key] = str(e)

    read("svms", "/api/svm/svms", "name,uuid,state,subtype")
    read("volumes", "/api/storage/volumes",
         "name,uuid,svm.name,state,type,style,is_svm_root,is_constituent,snapshot_policy.name,"
         "space.size,space.used,nas.export_policy.name",
         "name,uuid,svm.name,state,type,style,is_svm_root")
    read("aggregates", "/api/storage/aggregates",
         "name,node.name,space.block_storage.size,space.block_storage.used", "name")
    read("dns", "/api/name-services/dns", "svm.name,domains,servers")
    read("cifs", "/api/protocols/cifs/services", "svm.name,enabled,ad_domain.fqdn", "svm.name,enabled")
    read("shares", "/api/protocols/cifs/shares", "svm.name,name,path,acls", "svm.name,name,path")
    read("audit", "/api/protocols/audit", "svm.name,enabled")
    read("ndmp", "/api/protocols/ndmp/svms", "svm.name,enabled")
    read("exports", "/api/protocols/nfs/export-policies", "svm.name,name,rules", "svm.name,name")
    sm_fields = ("uuid,source.path,source.cluster.name,destination.path,destination.cluster.name,"
                 "policy.name,policy.type,transfer_schedule.name,state,healthy,lag_time,unhealthy_reason")
    sm_fallback = "uuid,source.path,destination.path,policy.name,state,healthy,lag_time"
    read("snap", "/api/snapmirror/relationships", sm_fields, sm_fallback)
    # On a source cluster, relationships are listed only with list_destinations_only.
    try:
        more, _ = ontap_records(client, "/api/snapmirror/relationships", sm_fields, params={"list_destinations_only": "true"})
        d["snap"] = (d["snap"] or []) + more
    except ApiError as e:
        if d.get("snap") is not None:
            d["notes"].append("source-side SnapMirror list not available (%s)" % e)
    return d


# --------------------------------------------------------------------------- check engine
class Check:
    def __init__(self, cid, cfg):
        self.id = cid
        self.title = TITLES[cid]
        self.severity = cfg["severity"].get(cid, "Unrated")
        self.findings = []
        self.notes = []

    def add(self, status, cluster, svm, obj, detail):
        self.findings.append({"status": status, "cluster": cluster, "svm": svm or "",
                              "object": obj or "", "detail": detail})

    @property
    def status(self):
        st = {f["status"] for f in self.findings}
        for s in ORDER:
            if s in st:
                return s
        return "NA"

    def counts(self):
        c = {s: 0 for s in ORDER}
        for f in self.findings:
            c[f["status"]] += 1
        return c


def matches(patterns, value):
    return any(fnmatch.fnmatch(value, p) for p in (patterns or []))


def parse_duration(s):
    if not s:
        return None
    m = re.match(r"^P(?:(\d+)D)?(?:T(?:(\d+)H)?(?:(\d+)M)?(?:(\d+(?:\.\d+)?)S)?)?$", str(s))
    if not m:
        return None
    dd, hh, mm, ss = [float(x) if x else 0 for x in m.groups()]
    return dd * 86400 + hh * 3600 + mm * 60 + ss


def in_scope_volume(v):
    n = v.get("name", "")
    return not (v.get("is_svm_root") or v.get("is_constituent") or n.startswith("MDV_")
                or g(v, "type") in ("dp", "ls"))


def relationships(data):
    """De-duplicated SnapMirror relationships across all clusters, with cluster names resolved."""
    seen, out = set(), []
    for cname, d in data.items():
        for r in d.get("snap") or []:
            sp, dp = g(r, "source", "path", default=""), g(r, "destination", "path", default="")
            sc = g(r, "source", "cluster", "name") or cname
            dc = g(r, "destination", "cluster", "name") or cname
            key = (sc, sp, dc, dp)
            if key in seen:
                continue
            seen.add(key)
            out.append({"sc": sc, "sp": sp, "dc": dc, "dp": dp, "raw": r, "seen_from": cname})
    return out


def split_path(p):
    svm, _, vol = (p or "").partition(":")
    return svm, vol


def run_checks(data, cfg):
    checks = {cid: Check(cid, cfg) for cid in TITLES}
    ex_vol, ex_svm = cfg["exempt"]["volumes"], cfg["exempt"]["svms"]
    rels = relationships(data)
    snap_known = all(d.get("snap") is not None for d in data.values())

    # ---- BKP-001 (also reused by BKP-009)
    src = {(r["sc"],) + split_path(r["sp"]) for r in rels}
    ck = checks["BKP-001"]
    ck.notes.append("ONTAP sees snapshots and SnapMirror only. Backup made by other software is not visible here.")
    for cname, d in data.items():
        if d.get("volumes") is None:
            ck.add("UNKNOWN", cname, "", "", "volume list not readable: %s" % d["errors"].get("volumes"))
            continue
        for v in d["volumes"]:
            if not in_scope_volume(v):
                continue
            svm, name = g(v, "svm", "name", default=""), v.get("name", "")
            if matches(ex_vol, "%s:%s" % (svm, name)) or matches(ex_svm, svm):
                continue
            pol = g(v, "snapshot_policy", "name")
            protected = (cname, svm, name) in src or (cname, svm, "") in src
            if pol not in (None, "", "none") or protected:
                continue
            if snap_known:
                ck.add("FAIL", cname, svm, name, "snapshot policy: none; no SnapMirror relationship found")
            else:
                ck.add("UNKNOWN", cname, svm, name, "snapshot policy: none; SnapMirror data could not be read")
    if not ck.findings:
        ck.add("PASS", "", "", "", "every volume in scope has a snapshot policy or a SnapMirror relationship")

    # ---- BKP-003
    ck = checks["BKP-003"]
    sites = {k: v for k, v in cfg["sites"].items() if not k.startswith("_")}
    missing_map = set()
    for r in rels:
        if r["sc"] == r["dc"]:
            ck.add("FAIL", r["sc"], split_path(r["sp"])[0], r["sp"], "destination %s is on the same cluster" % r["dp"])
            continue
        s1, s2 = sites.get(r["sc"]), sites.get(r["dc"])
        if s1 is None or s2 is None:
            missing_map.update(c for c in (r["sc"], r["dc"]) if c not in sites)
        elif s1 == s2:
            ck.add("FAIL", r["sc"], split_path(r["sp"])[0], r["sp"],
                   "destination %s (cluster %s) is at the same site (%s)" % (r["dp"], r["dc"], s1))
    if missing_map:
        ck.add("NEEDS_INPUT", "", "", "", "site not set for cluster(s): %s. Add them under \"sites\" in the config."
               % ", ".join(sorted(missing_map)))
    if not snap_known:
        ck.add("UNKNOWN", "", "", "", "SnapMirror data could not be read on every cluster")
    if not ck.findings:
        ck.add("NA" if not rels else "PASS", "", "", "",
               "no SnapMirror relationships found" if not rels else "no destination shares a cluster or site with its source")

    # ---- BKP-010
    ck = checks["BKP-010"]
    pols, scheds = {}, {}
    lag_limit = cfg["dr"]["lag_limit_minutes"]
    for r in rels:
        raw = r["raw"]
        obj = "%s -> %s" % (r["sp"], r["dp"])
        pol, sch = g(raw, "policy", "name"), g(raw, "transfer_schedule", "name")
        pols.setdefault(pol, []).append(obj)
        scheds.setdefault(sch, []).append(obj)
        if raw.get("healthy") is False:
            ck.add("FAIL", r["dc"], split_path(r["dp"])[0], obj, "unhealthy: %s" % (raw.get("unhealthy_reason") or "no reason given"))
        lag = parse_duration(raw.get("lag_time"))
        if lag_limit is not None and lag is not None and lag > lag_limit * 60:
            ck.add("FAIL", r["dc"], split_path(r["dp"])[0], obj, "lag %.0f min is over the %s min limit" % (lag / 60, lag_limit))
        for val, allowed, what in ((pol, cfg["dr"]["allowed_policies"], "policy"), (sch, cfg["dr"]["allowed_schedules"], "schedule")):
            if allowed is not None and val not in allowed:
                ck.add("FAIL", r["dc"], split_path(r["dp"])[0], obj, "%s %s is not in the allowed list" % (what, val))
    for what, found, allowed in (("policy", pols, cfg["dr"]["allowed_policies"]), ("schedule", scheds, cfg["dr"]["allowed_schedules"])):
        if allowed is None and len(found) > 1:
            ck.add("NEEDS_INPUT", "", "", "", "%d different %s values in use (%s). Set dr.allowed_%ss to say which are correct."
                   % (len(found), what, ", ".join(str(k) for k in sorted(found, key=str)), what))
    if lag_limit is None and rels:
        ck.notes.append("Lag is not checked: set dr.lag_limit_minutes.")
    if not snap_known:
        ck.add("UNKNOWN", "", "", "", "SnapMirror data could not be read on every cluster")
    if not ck.findings:
        ck.add("NA" if not rels else "PASS", "", "", "", "no SnapMirror relationships found" if not rels else "all relationships healthy and consistent")

    # ---- BKP-004
    ck = checks["BKP-004"]
    ck.notes.append("ONTAP shows whether NDMP is on. It cannot show whether tape or legacy software is still used.")
    for cname, d in data.items():
        if d.get("ndmp") is None:
            ck.add("UNKNOWN", cname, "", "", "NDMP settings not readable: %s" % d["errors"].get("ndmp"))
            continue
        for n in d["ndmp"]:
            svm = g(n, "svm", "name", default="")
            if n.get("enabled") and svm not in cfg["ndmp_allowed_svms"] and not matches(ex_svm, svm):
                ck.add("FAIL", cname, svm, "", "NDMP is enabled (add the SVM to ndmp_allowed_svms if this is expected)")

    # ---- STO-DNS
    ck = checks["STO-DNS"]
    for cname, d in data.items():
        if d.get("dns") is None or d.get("svms") is None and d.get("volumes") is None:
            ck.add("UNKNOWN", cname, "", "", "DNS or SVM list not readable: %s" % (d["errors"].get("dns") or d["errors"].get("svms")))
            continue
        have = {g(x, "svm", "name"): x for x in d["dns"]}
        for svm in svm_names(d):
            if matches(ex_svm, svm):
                continue
            x = have.get(svm)
            if not x or not x.get("servers") or not x.get("domains"):
                ck.add("FAIL", cname, svm, "", "no DNS %s configured" % ("at all" if not x else
                       "servers" if not x.get("servers") else "domains"))
    if not ck.findings:
        ck.add("PASS", "", "", "", "every SVM has DNS servers and domains")

    # ---- STO-CIFS
    ck = checks["STO-CIFS"]
    for cname, d in data.items():
        if d.get("cifs") is None:
            ck.add("UNKNOWN", cname, "", "", "CIFS services not readable: %s" % d["errors"].get("cifs"))
            continue
        for s in d["cifs"]:
            svm = g(s, "svm", "name", default="")
            if s.get("enabled") is not False and not g(s, "ad_domain", "fqdn") and not matches(ex_svm, svm):
                ck.add("FAIL", cname, svm, "", "CIFS service is not joined to a domain (workgroup mode)")
    if not ck.findings:
        ck.add("NA" if not any(d.get("cifs") for d in data.values()) else "PASS", "", "", "",
               "no CIFS services found" if not any(d.get("cifs") for d in data.values()) else "all CIFS services are in a domain")

    # ---- STO-AUD
    ck = checks["STO-AUD"]
    for cname, d in data.items():
        if d.get("audit") is None:
            ck.add("UNKNOWN", cname, "", "", "audit settings not readable: %s" % d["errors"].get("audit"))
            continue
        have = {g(x, "svm", "name"): x for x in d["audit"]}
        for svm in svm_names(d):
            if matches(ex_svm, svm):
                continue
            if not (have.get(svm) or {}).get("enabled"):
                ck.add("FAIL", cname, svm, "", "auditing is not enabled")
    if not ck.findings:
        ck.add("PASS", "", "", "", "auditing is enabled on every SVM")

    # ---- STO-NFS
    ck = checks["STO-NFS"]
    open_clients = set(cfg["exposure"]["nfs_open_clients"])
    for cname, d in data.items():
        if d.get("exports") is None:
            ck.add("UNKNOWN", cname, "", "", "export policies not readable: %s" % d["errors"].get("exports"))
            continue
        used = {}
        for v in d.get("volumes") or []:
            p = g(v, "nas", "export_policy", "name")
            if p:
                used[(g(v, "svm", "name"), p)] = used.get((g(v, "svm", "name"), p), 0) + 1
        for pol in d["exports"]:
            svm = g(pol, "svm", "name", default="")
            if matches(ex_svm, svm):
                continue
            for i, rule in enumerate(pol.get("rules") or [], 1):
                clients = [str(c.get("match", "")).strip() for c in rule.get("clients") or []]
                hit = [c for c in clients if c in open_clients]
                if not hit:
                    continue
                ro, rw, su = rule.get("ro_rule") or [], rule.get("rw_rule") or [], rule.get("superuser") or []
                ck.add("FAIL", cname, svm, "policy %s rule %s" % (pol.get("name"), rule.get("index", i)),
                       "matches %s; ro=%s rw=%s superuser=%s; used by %d volume(s)"
                       % (", ".join(hit), ",".join(ro) or "-", ",".join(rw) or "-", ",".join(su) or "-",
                          used.get((svm, pol.get("name")), 0)))
        if (d["exports"] and d["exports"][0].get("rules") is None):
            ck.add("UNKNOWN", cname, "", "", "export rules were not returned (reduced field list)")
    if not ck.findings:
        ck.add("PASS", "", "", "", "no export rule matches the open-client list")

    # ---- STO-SMB
    ck = checks["STO-SMB"]
    bad_p = {p.lower() for p in cfg["exposure"]["smb_principals"]}
    bad_perm = {p.lower() for p in cfg["exposure"]["smb_permissions"]}
    for cname, d in data.items():
        if d.get("shares") is None:
            ck.add("UNKNOWN", cname, "", "", "CIFS shares not readable: %s" % d["errors"].get("shares"))
            continue
        for s in d["shares"]:
            nm, svm = s.get("name", ""), g(s, "svm", "name", default="")
            if nm.endswith("$") or matches(ex_svm, svm):
                continue
            if "acls" not in s:
                ck.add("UNKNOWN", cname, svm, nm, "share permissions were not returned (reduced field list)")
                continue
            for a in s.get("acls") or []:
                if str(a.get("user_or_group", "")).lower() in bad_p and str(a.get("permission", "")).lower() in bad_perm:
                    ck.add("FAIL", cname, svm, nm, "%s has %s on %s" % (a.get("user_or_group"), a.get("permission"), s.get("path", "")))
    if not ck.findings:
        ck.add("PASS", "", "", "", "no share gives a listed principal a listed permission")

    # ---- STO-VOL
    ck = checks["STO-VOL"]
    base = cfg["volume_baseline"]
    if base.get("state") is None and base.get("snapshot_policies") is None:
        ck.add("NEEDS_INPUT", "", "", "", "no baseline set. Fill volume_baseline in the config (state, snapshot_policies).")
    else:
        for cname, d in data.items():
            if d.get("volumes") is None:
                ck.add("UNKNOWN", cname, "", "", "volume list not readable")
                continue
            for v in d["volumes"]:
                if not in_scope_volume(v):
                    continue
                svm, name = g(v, "svm", "name", default=""), v.get("name", "")
                if matches(ex_vol, "%s:%s" % (svm, name)) or matches(ex_svm, svm):
                    continue
                why = []
                if base.get("state") is not None and v.get("state") != base["state"]:
                    why.append("state %s (baseline %s)" % (v.get("state"), base["state"]))
                if base.get("snapshot_policies") is not None and g(v, "snapshot_policy", "name") not in base["snapshot_policies"]:
                    why.append("snapshot policy %s (allowed: %s)" % (g(v, "snapshot_policy", "name"), ", ".join(base["snapshot_policies"])))
                if why:
                    ck.add("FAIL", cname, svm, name, "; ".join(why))
        if not ck.findings:
            ck.add("PASS", "", "", "", "every volume in scope matches the baseline")

    # ---- STO-CAP (BKP-008 reuses it)
    ck = checks["STO-CAP"]
    cap = cfg["capacity"]
    if cap["aggregate_used_pct_max"] is None and cap["volume_used_pct_max"] is None:
        ck.add("NEEDS_INPUT", "", "", "", "no threshold set. Fill capacity in the config.")
    else:
        ck.notes.append("This version keeps no history, so it cannot show a growth trend.")
        for cname, d in data.items():
            if cap["aggregate_used_pct_max"] is not None:
                if d.get("aggregates") is None:
                    ck.add("UNKNOWN", cname, "", "", "aggregates not readable: %s" % d["errors"].get("aggregates"))
                for a in d.get("aggregates") or []:
                    size, used = g(a, "space", "block_storage", "size"), g(a, "space", "block_storage", "used")
                    if size and used is not None and 100.0 * used / size > cap["aggregate_used_pct_max"]:
                        ck.add("FAIL", cname, "", "aggregate " + a.get("name", ""),
                               "%.1f%% used (limit %s%%)" % (100.0 * used / size, cap["aggregate_used_pct_max"]))
            if cap["volume_used_pct_max"] is not None and d.get("volumes") is not None:
                for v in d["volumes"]:
                    if not in_scope_volume(v):
                        continue
                    svm, name = g(v, "svm", "name", default=""), v.get("name", "")
                    if matches(ex_vol, "%s:%s" % (svm, name)) or matches(ex_svm, svm):
                        continue
                    size, used = g(v, "space", "size"), g(v, "space", "used")
                    if size and used is not None and 100.0 * used / size > cap["volume_used_pct_max"]:
                        ck.add("FAIL", cname, svm, name, "%.1f%% used (limit %s%%)" % (100.0 * used / size, cap["volume_used_pct_max"]))
        if not ck.findings:
            ck.add("PASS", "", "", "", "nothing over the thresholds")
    c8 = checks["BKP-008"]
    c8.notes = list(ck.notes)
    c8.findings = [dict(f) for f in ck.findings]

    # BKP-009: copied from the DNS, audit and BKP-001 results
    ck = checks["BKP-009"]
    for src_id, tag in (("STO-DNS", "DNS"), ("STO-AUD", "audit"), ("BKP-001", "protection")):
        for f in checks[src_id].findings:
            if f["status"] in ("FAIL", "UNKNOWN"):
                f = dict(f)
                f["detail"] = "[%s] %s" % (tag, f["detail"])
                ck.findings.append(f)
    ck.notes.append("DNS, audit and volume protection come from ONTAP. AD, VM and database protection are not checked.")

    # attach remediation plans
    plans = [p for p in cfg["plans"] if isinstance(p, dict)] if isinstance(cfg["plans"], list) else []
    for cid, ck in checks.items():
        ck.plans = [p for p in plans if p.get("id") == cid]
    return checks


def svm_names(d):
    if d.get("svms") is not None:
        return [s["name"] for s in d["svms"] if s.get("state") in (None, "running") and s.get("subtype") in (None, "default")]
    return sorted({g(v, "svm", "name") for v in d.get("volumes") or [] if g(v, "svm", "name")})


# --------------------------------------------------------------------------- output
def write_private(path, text=None, writer=None):
    flags = os.O_WRONLY | os.O_CREAT | os.O_TRUNC
    fd = os.open(path, flags, 0o600)
    with os.fdopen(fd, "w", encoding="utf-8", newline="") as f:
        if writer:
            writer(f)
        else:
            f.write(text)


def check_summary_line(ck):
    c = ck.counts()
    bits = ["%d %s" % (c[s], LABEL[s].lower()) for s in ORDER if c[s]]
    return ", ".join(bits)


def build_check_json(data, checks, cfg, started):
    return {
        "tool": "ontap_check", "version": VERSION, "generated": started,
        "clusters": [{"name": d["name"], "version": d["version"], "errors": d["errors"], "notes": d["notes"]} for d in data.values()],
        "checks": [{"id": c.id, "title": c.title, "severity": c.severity, "status": LABEL[c.status], "counts": {LABEL[k]: v for k, v in c.counts().items()},
                    "notes": c.notes, "findings": [dict(f, status=LABEL[f["status"]]) for f in c.findings], "plans": getattr(c, "plans", []),
                    "fix_templates": FIXES.get(c.id, []), "tig": cfg["tig_links"].get(c.id, "")} for c in checks.values()],
    }


def build_check_html(data, checks, cfg, started):
    e = html.escape
    glyph = {"FAIL": "&#10007;", "UNKNOWN": "?", "NEEDS_INPUT": "&#9998;", "PASS": "&#10003;", "NA": "&ndash;"}
    label = LABEL
    tally = {s: 0 for s in ORDER}
    for c in checks.values():
        tally[c.status] += 1
    total = len(checks)
    bar = "".join('<span class="seg s-%s" style="flex:%d" title="%s: %d"></span>' % (s, tally[s], label[s], tally[s])
                  for s in ORDER if tally[s])
    tiles = "".join('<div class="tile"><div class="n t-%s">%d</div><div class="l"><span class="pill p-%s">%s %s</span></div></div>'
                    % (s, tally[s], s, glyph[s], label[s]) for s in ORDER)
    rows, details = [], []
    maxrows = cfg["max_rows_in_html"]
    for c in checks.values():
        rows.append('<tr><td><a href="#%s">%s</a></td><td>%s</td><td>%s</td><td><span class="pill p-%s">%s %s</span></td><td>%s</td></tr>'
                    % (c.id, c.id, e(c.title), e(c.severity), c.status, glyph[c.status], label[c.status], e(check_summary_line(c))))
        f_rows = "".join("<tr><td><span class='pill p-%s'>%s</span></td><td>%s</td><td>%s</td><td>%s</td><td>%s</td></tr>"
                         % (f["status"], label[f["status"]], e(f["cluster"]), e(f["svm"]), e(f["object"]), e(f["detail"]))
                         for f in sorted(c.findings, key=lambda f: ORDER.index(f["status"]))[:maxrows])
        more = len(c.findings) - maxrows
        fixes = "".join("<code>%s</code>" % e(x) for x in FIXES.get(c.id, []))
        tig = cfg["tig_links"].get(c.id)
        tig_html = '<a href="%s">TIG</a>' % e(tig, quote=True) if tig and re.match(r"^https?://", tig) else "<span class='muted'>TIG link not set</span>"
        plans = "".join("<li>%s &middot; %s &middot; target %s &middot; %s</li>"
                        % (e(p.get("owner_role", "")), e(p.get("status", "")), e(p.get("target", "")), e(p.get("note", "")))
                        for p in getattr(c, "plans", []))
        notes = "".join("<p class='muted'>%s</p>" % e(n) for n in c.notes)
        details.append(
            '<details id="%s" %s><summary><b>%s</b> %s <span class="pill p-%s">%s %s</span> <span class="muted">%s</span></summary>'
            '%s<table class="f"><tr><th>Status</th><th>Cluster</th><th>SVM</th><th>Object</th><th>Detail</th></tr>%s</table>%s'
            '<div class="fix"><b>Suggested fix (shown, never run)</b>%s<div>%s</div></div>%s</details>'
            % (c.id, "open" if c.status == "FAIL" else "", c.id, e(c.title), c.status, glyph[c.status], label[c.status],
               e(c.severity), notes, f_rows, ("<p class='muted'>%d more rows are in the CSV and JSON.</p>" % more) if more > 0 else "",
               fixes, tig_html, ("<div class='fix'><b>Remediation plans</b><ul>%s</ul></div>" % plans) if plans else ""))
    cl = "".join("<li>%s <span class='muted'>%s</span>%s</li>" % (
        e(d["name"]), e(d["version"]),
        ("<ul>" + "".join("<li>%s: %s</li>" % (e(k), e(v)) for k, v in d["errors"].items()) + "</ul>") if d["errors"] else "")
        for d in data.values())
    notes_all = "".join("<li>%s: %s</li>" % (e(d["name"]), e(n)) for d in data.values() for n in d["notes"])
    return REPORT_PAGE % {"when": e(started), "tiles": tiles, "bar": bar, "total": total, "rows": "".join(rows),
                   "details": "".join(details), "clusters": cl, "notes": ("<ul>%s</ul>" % notes_all) if notes_all else ""}


REPORT_PAGE = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8"><title>ONTAP compliance report</title>
<meta name="viewport" content="width=device-width,initial-scale=1">
<style>
:root{--ink:#1f2328;--mut:#59636e;--line:#d1d9e0;--bg:#fff;--card:#f6f8fa}
*{box-sizing:border-box}body{font:14px/1.45 system-ui,Segoe UI,Arial,sans-serif;color:var(--ink);background:var(--bg);margin:0;padding:24px;max-width:1200px;margin:auto}
h1{font-size:22px;margin:0 0 4px}h2{font-size:16px;margin:28px 0 8px}.muted{color:var(--mut);font-size:12px}
.tiles{display:grid;grid-template-columns:repeat(5,1fr);gap:8px;margin:16px 0}
.tile{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:10px}.n{font-size:28px;font-weight:600}
.bar{display:flex;gap:2px;height:14px;margin:8px 0}.seg{border-radius:3px}
.s-FAIL{background:#c62828}.s-UNKNOWN{background:#6e7781}.s-NEEDS_INPUT{background:#d4a017}.s-PASS{background:#2e7d32}.s-NA{background:#b8c0c8}
.pill{display:inline-block;padding:1px 8px;border-radius:10px;font-size:12px;border:1px solid;white-space:nowrap}
.p-FAIL{color:#8f1d1d;background:#fdecec;border-color:#e8a3a3}.p-UNKNOWN{color:#444c55;background:#eef0f2;border-color:#b8c0c8}
.p-NEEDS_INPUT{color:#6b4e00;background:#fff6d6;border-color:#e3c76a}
.p-PASS{color:#1b5e20;background:#e6f4e7;border-color:#9fcfa2}.p-NA{color:#59636e;background:#f3f5f7;border-color:#cfd6dd}
table{border-collapse:collapse;width:100%%}th,td{text-align:left;padding:6px 8px;border-bottom:1px solid var(--line);vertical-align:top}
th{font-size:12px;color:var(--mut)}details{border:1px solid var(--line);border-radius:8px;margin:8px 0;padding:8px 12px}
summary{cursor:pointer}.fix{background:var(--card);border-radius:6px;padding:8px 10px;margin-top:8px}
code{display:block;font:12px ui-monospace,Menlo,Consolas,monospace;margin:4px 0;white-space:pre-wrap;word-break:break-all}
a{color:#0b5cad}button{font:inherit;padding:6px 12px;border:1px solid var(--line);border-radius:6px;background:var(--card);cursor:pointer}
@media print{body{padding:0}button{display:none}details{break-inside:avoid}}
</style></head><body>
<h1>ONTAP backup and storage compliance report</h1>
<div class="muted">Generated %(when)s &middot; read-only: no setting was changed on any cluster &middot; fix commands are templates to check against your ONTAP version</div>
<p><button onclick="window.print()">Print / save as PDF</button></p>
<div class="tiles">%(tiles)s</div>
<div class="muted">%(total)s checks by status</div><div class="bar">%(bar)s</div>
<h2>Checks</h2>
<table><tr><th>ID</th><th>Check</th><th>Severity</th><th>Status</th><th>Findings</th></tr>%(rows)s</table>
<h2>Details and suggested fixes</h2>%(details)s
<h2>Clusters read</h2><ul>%(clusters)s</ul>%(notes)s
<script>window.addEventListener("beforeprint",function(){document.querySelectorAll("details").forEach(function(d){d.open=true})});</script>
</body></html>"""


# --------------------------------------------------------------------------- running a scan
def run_scan(hosts, user, pw, tls, ca, timeout, cfg, enabled=None, say=None):
    """Read every cluster and run the checks. `enabled` limits which checks are reported
    (None means all). `say` receives short progress messages. Returns (data, checks, started)."""
    say = say or (lambda m: None)
    started = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    data = {}
    for host in hosts:
        say("Reading %s" % host)
        d = collect_cluster(Ontap(host, user, pw, tls, ca, timeout), host)
        if d["name"] in data:
            d["name"] = host
        data[d["name"]] = d
        for k, v in d["errors"].items():
            say("  %s: %s" % (k, v))
    say("Running checks")
    checks = run_checks(data, cfg)
    if enabled is not None:
        # BKP-009 borrows findings from STO-DNS, STO-AUD and BKP-001: drop the ones switched off.
        ck = checks["BKP-009"]
        off = [t for t, cid in (("[DNS]", "STO-DNS"), ("[audit]", "STO-AUD"), ("[protection]", "BKP-001")) if cid not in enabled]
        ck.findings = [f for f in ck.findings if not any(f["detail"].startswith(t) for t in off)]
        if not ck.findings:
            ck.add("PASS", "", "", "", "nothing found in the parts that are switched on")
        checks = {k: v for k, v in checks.items() if k in enabled}
    return data, checks, started


def write_check_outputs(outdir, data, checks, cfg, started):
    os.makedirs(outdir, exist_ok=True)
    base = os.path.join(outdir, "report_" + datetime.now().strftime("%Y%m%d_%H%M%S"))
    write_private(base + ".html", build_check_html(data, checks, cfg, started))
    write_private(base + ".json", json.dumps(build_check_json(data, checks, cfg, started), indent=2))

    def w(f):
        cw = csv.writer(f)
        cw.writerow(["check_id", "check", "severity", "status", "cluster", "svm", "object", "detail"])
        for c in checks.values():
            for x in c.findings:
                cw.writerow([c.id, c.title, c.severity, LABEL[x["status"]]] + [csv_safe(x[k]) for k in ("cluster", "svm", "object", "detail")])
    write_private(base + ".csv", writer=w)
    return base


# --------------------------------------------------------------------------- benchmarks (read-only)
def benchmark_rules(cfg):
    """One plain sentence per check saying what 'met' means, taken from the config.
    The GUI shows these locked. Only the config file, owned by whoever runs the server, sets them."""
    def lst(x):
        return ", ".join(x) if x else "none set"
    cap, dr, base = cfg["capacity"], cfg["dr"], cfg["volume_baseline"]
    unset = "Not set in the config (shows Needs input)"
    sites = {k: v for k, v in cfg["sites"].items() if not k.startswith("_")}
    return {
        "BKP-001": "Every volume has a snapshot policy or a SnapMirror relationship",
        "BKP-003": "No SnapMirror destination on the same cluster or site as its source. Sites mapped: %d cluster(s)" % len(sites),
        "BKP-004": "NDMP is off, except SVMs allowed in the config: " + lst(cfg["ndmp_allowed_svms"]),
        "BKP-008": ("Aggregates at most %s%% used, volumes at most %s%% used" % (cap["aggregate_used_pct_max"], cap["volume_used_pct_max"]))
                   if cap["aggregate_used_pct_max"] is not None or cap["volume_used_pct_max"] is not None else unset,
        "BKP-009": "DNS and auditing are on for every SVM and every volume is protected",
        "BKP-010": "Relationships healthy; allowed policies: %s; allowed schedules: %s; lag limit: %s" % (
            lst(dr["allowed_policies"]) if dr["allowed_policies"] is not None else "not set",
            lst(dr["allowed_schedules"]) if dr["allowed_schedules"] is not None else "not set",
            ("%s min" % dr["lag_limit_minutes"]) if dr["lag_limit_minutes"] is not None else "not set"),
        "STO-DNS": "Every SVM has DNS servers and domains",
        "STO-CIFS": "Every CIFS service is joined to a domain",
        "STO-NFS": "No export rule matches: " + lst(cfg["exposure"]["nfs_open_clients"]),
        "STO-SMB": "No share gives %s the permission %s" % (lst(cfg["exposure"]["smb_principals"]), lst(cfg["exposure"]["smb_permissions"])),
        "STO-AUD": "Auditing is enabled on every SVM",
        "STO-VOL": ("Volume state: %s; snapshot policies: %s" % (base["state"] or "any", lst(base["snapshot_policies"])))
                   if base["state"] is not None or base["snapshot_policies"] is not None else unset,
        "STO-CAP": ("Aggregates at most %s%% used, volumes at most %s%% used" % (cap["aggregate_used_pct_max"], cap["volume_used_pct_max"]))
                   if cap["aggregate_used_pct_max"] is not None or cap["volume_used_pct_max"] is not None else unset,
    }



# --------------------------------------------------------------------------
# Compliance tab: state, request checking and run thread
# --------------------------------------------------------------------------
class CheckApp:
    """State of the compliance tab. cfg holds the LOCKED benchmarks: it is read once from the
    --check-config file at start-up. Nothing the browser sends can change it."""
    cfg = None
    outdir = "reports"
    lock = threading.Lock()
    state = {"state": "idle", "log": [], "base": None, "html": None, "error": None}


def parse_check_request(body):
    """Validate a compliance run request. Benchmark VALUES are never read from the browser, only
    the list of check ids to switch on."""
    hosts = []
    first = str(body.get("cluster", "")).strip()
    for line in ([first] if first else []) + str(body.get("clusters_extra", "")).replace(",", "\n").splitlines():
        line = line.strip()
        if line and line not in hosts:
            hosts.append(line)
    if not hosts or len(hosts) > 20:
        raise ValueError("Give between 1 and 20 cluster addresses")
    for h in hosts:
        if len(h) > 200 or re.search(r"\s", h) or ("://" in h and not re.match(r"^https?://", h)):
            raise ValueError("Bad cluster address: %s" % h[:60])
    user, pw = str(body.get("user", "")).strip(), str(body.get("password", ""))
    if not user or not pw or len(user) > 100 or len(pw) > 500:
        raise ValueError("Enter the user and password")
    tls = body.get("tls", "verify")
    if tls not in ("verify", "ca", "skip"):
        raise ValueError("Bad certificate mode")
    ca = str(body.get("ca", "")).strip() or None
    if tls == "ca" and (not ca or not os.path.isfile(ca)):
        raise ValueError("The CA file was not found on this server")
    enabled = body.get("enabled")
    if not isinstance(enabled, list) or not all(isinstance(x, str) and x in TITLES for x in enabled):
        raise ValueError("Bad benchmark list")
    if not enabled:
        raise ValueError("Switch at least one benchmark on")
    return hosts, user, pw, tls, ca, set(enabled)


def check_thread(hosts, user, pw, tls, ca, enabled):
    st = CheckApp.state

    def say(m):
        with CheckApp.lock:
            st["log"].append(m)
    try:
        data, checks, started = run_scan(hosts, user, pw, tls, ca, 60, CheckApp.cfg, enabled, say)
        base = write_check_outputs(CheckApp.outdir, data, checks, CheckApp.cfg, started)
        page = build_check_html(data, checks, CheckApp.cfg, started)
        with CheckApp.lock:
            st.update(state="done", base=base, html=page, error=None)
            st["log"].append("Done. Files written to %s.*" % base)
    except Exception as e:          # the password is never put in a message
        with CheckApp.lock:
            st.update(state="error", error=str(e).replace(pw, "***") if pw else str(e))

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
    server_version = "Cryo/2.0"

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

    # ---- compliance tab routes (read-only: they only ever cause GET requests to ONTAP)
    def _check_get(self, url, qs):
        if url.path == "/api/check/benchmarks":
            rules = benchmark_rules(CheckApp.cfg)
            ex = CheckApp.cfg["exempt"]
            return self._send(200, {"locked": True,
                                    "checks": [{"id": c, "title": TITLES[c], "severity": CheckApp.cfg["severity"].get(c, "Unrated"),
                                                "rule": rules.get(c, "")} for c in TITLES],
                                    "exempt": {"volumes": ex["volumes"], "svms": ex["svms"]}})
        if url.path == "/api/check/status":
            with CheckApp.lock:
                st = CheckApp.state
                return self._send(200, {"state": st["state"], "log": st["log"][-200:], "error": st["error"],
                                        "html": st["html"] if st["state"] == "done" else None})
        if url.path == "/api/check/download":
            fmt = (qs.get("fmt") or [""])[0]
            with CheckApp.lock:
                base = CheckApp.state["base"]
            if fmt not in ("html", "json", "csv") or not base:
                return self._send(404, {"error": "Nothing to download"})
            with open(base + "." + fmt, "rb") as f:
                body = f.read()
            ctype = {"html": "text/html", "json": "application/json", "csv": "text/csv"}[fmt]
            return self._send(200, body, ctype + "; charset=utf-8",
                              {"Content-Disposition": 'attachment; filename="%s.%s"' % (os.path.basename(base), fmt)})
        self._send(404, {"error": "Not found"})

    def _check_run(self, body):
        hosts, user, pw, tls, ca, enabled = parse_check_request(body)
        with CheckApp.lock:
            if CheckApp.state["state"] == "running":
                return self._send(409, {"error": "A compliance run is already in progress"})
            CheckApp.state.update(state="running", log=["Started"], base=None, html=None, error=None)
        threading.Thread(target=check_thread, args=(hosts, user, pw, tls, ca, enabled), daemon=True).start()
        self._send(200, {"ok": True})

    # routes
    def do_GET(self):
        url = urllib.parse.urlparse(self.path)
        qs = urllib.parse.parse_qs(url.query)
        # The page needs no token. The page asks for the token itself when its first API call gets a 401.
        if url.path == "/":
            return self._send(200, PAGE.replace("{{APP}}", APP_NAME).encode(), "text/html; charset=utf-8")
        # Everything below this line needs the token (if one is set).
        if not self._authed():
            return self._send(401, {"error": "Access token required"})
        if url.path.startswith("/api/check/"):
            return self._check_get(url, qs)
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
            if path == "/api/check/run":
                return self._check_run(body)
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
<title>{{APP}}</title>
<style>
/* All colours are variables, so the light and dark themes only change these values. */
:root{--bg:#fff;--panel:#fff;--ink:#15262e;--mute:#5b6e77;--line:#d3dde2;--ice:#1f6f99;--ice-soft:#dbeaf3;--warn:#a85a00;--bad:#b3261e;--ok:#1d7a4a}
/* The page is always light with a white background (no automatic dark theme). */
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
.modes{display:flex;gap:4px;margin-left:8px}.modes button{padding:4px 12px}.modes button.on{background:var(--ice);border-color:var(--ice);color:var(--panel);font-weight:600}
textarea{width:100%;height:64px;padding:7px 9px;border:1px solid var(--line);border-radius:4px;background:var(--bg);color:var(--ink);font:inherit;resize:vertical}
.bm{display:flex;gap:10px;align-items:flex-start;padding:8px 0;border-bottom:1px solid var(--line)}.bm .t{flex:1;font-size:13px}.bm .id{font-weight:600}.bm .rule{color:var(--mute);font-size:12px}
.sw{position:relative;width:38px;height:22px;flex:none;margin-top:2px;display:block}.sw input{opacity:0;width:100%;height:100%;position:absolute;margin:0;cursor:pointer}
.sw span{position:absolute;inset:0;background:var(--line);border-radius:11px;transition:.15s}.sw span:before{content:"";position:absolute;width:16px;height:16px;left:3px;top:3px;background:#fff;border-radius:50%;transition:.15s}
.sw input:checked+span{background:var(--ice)}.sw input:checked+span:before{transform:translateX(16px)}.sw input:focus-visible+span{outline:2px solid var(--ice);outline-offset:2px}
.lockbox{font-size:12px;background:var(--bg);border:1px solid var(--line);border-radius:6px;padding:6px 8px;margin:6px 0}
#clog{background:var(--bg);border:1px solid var(--line);border-radius:6px;padding:8px;font-size:12px;max-height:150px;overflow:auto;white-space:pre-wrap;margin:8px 0;display:none}
#crep{width:100%;height:calc(100vh - 260px);min-height:420px;border:1px solid var(--line);border-radius:6px;display:none;background:#fff}
</style></head><body>
<!-- Header: tool name, scan state pill (idle, running, done, stopped, failed) and any setup message. -->
<header><h1>{{APP}}</h1><span class="hint" style="margin:0">ONTAP cold data and compliance</span><span class="modes"><button id="m_cold" class="on" type="button">Cold data</button><button id="m_comp" type="button">Compliance</button></span><span id="pill" class="pill">idle</span><span id="hdrmsg" class="hint" style="margin:0"></span></header>
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
<div id="cold_left">
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
<div id="comp_left" style="display:none">
  <div class="panel"><h2>Compliance checks</h2>
    <div class="hint" style="margin-top:0">Uses the cluster login above. Read-only: only GET requests are sent.</div>
    <label for="cx">More clusters (optional, one per line)</label><textarea id="cx" autocomplete="off" spellcheck="false" placeholder="cluster2-mgmt.example.local"></textarea>
    <h2 style="margin-top:16px">Benchmarks</h2>
    <div class="lockbox">&#128274; The values below are locked. They come from the server's config file and cannot be changed here. You can only switch a benchmark on or off for this run.</div>
    <div class="row"><button id="cAllOn" class="mini" type="button">All on</button><button id="cAllOff" class="mini" type="button">All off</button></div>
    <div id="cbm"></div><div id="cexempt" class="hint"></div>
    <div class="row" style="margin-top:14px"><button id="btnCheck" class="primary" type="button">Run checks</button></div>
    <div id="checkmsg" class="msg"></div>
  </div>
</div>
</div>
<div id="cold_right">
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
<div id="comp_right" style="display:none"><div class="panel"><h2>Compliance results</h2>
  <div id="cstatus" class="hint" style="margin-top:0">No run yet. Fill in the cluster login, choose benchmarks and press Run checks.</div>
  <pre id="clog"></pre>
  <div class="row" id="cdl" style="display:none;max-width:480px"></div>
  <iframe id="crep" sandbox="allow-scripts allow-modals" title="Compliance report"></iframe>
</div></div>
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

// ---------------- Compliance tab ----------------
// Mode switch: the Cluster panel (the login) stays visible in both modes.
function setMode(m){const comp=m==="comp";
  $("cold_left").style.display=comp?"none":"block";$("cold_right").style.display=comp?"none":"block";
  $("comp_left").style.display=comp?"block":"none";$("comp_right").style.display=comp?"block":"none";
  $("m_cold").className=comp?"":"on";$("m_comp").className=comp?"on":"";
  if(comp&&!CB.loaded)loadBenchmarks();}
$("m_cold").onclick=()=>setMode("cold");$("m_comp").onclick=()=>setMode("comp");
const CB={loaded:false,boxes:[],timer:null};
function mk(t,c,x){const e=document.createElement(t);if(c)e.className=c;if(x!=null)e.textContent=x;return e}
async function loadBenchmarks(){
  try{const j=await api("/api/check/benchmarks");const box=$("cbm");box.textContent="";CB.boxes=[];
    j.checks.forEach(c=>{const row=mk("div","bm"),sw=mk("label","sw"),inp=document.createElement("input");
      inp.type="checkbox";inp.checked=true;inp.value=c.id;inp.setAttribute("aria-label","Switch "+c.id+" on or off");
      sw.appendChild(inp);sw.appendChild(document.createElement("span"));CB.boxes.push(inp);
      const t=mk("div","t");t.appendChild(mk("div","id",c.id+"  "+c.title));
      t.appendChild(mk("div","rule","\uD83D\uDD12 "+c.rule+" \u00B7 Severity: "+c.severity));
      row.appendChild(sw);row.appendChild(t);box.appendChild(row)});
    const ex=[].concat(j.exempt.volumes,j.exempt.svms);
    $("cexempt").textContent=ex.length?"Exempt (locked): "+ex.join(", "):"";CB.loaded=true;
  }catch(e){$("cbm").textContent="Could not load benchmarks: "+e.message}}
$("cAllOn").onclick=()=>CB.boxes.forEach(b=>b.checked=true);
$("cAllOff").onclick=()=>CB.boxes.forEach(b=>b.checked=false);
async function pollCheck(){
  try{const s=await api("/api/check/status");const log=$("clog");log.style.display="block";log.textContent=s.log.join("\n");
    if(s.state==="running")return;
    clearInterval(CB.timer);$("btnCheck").disabled=false;$("password").value="";
    if(s.state==="error"){$("cstatus").textContent="The run stopped.";say("checkmsg",s.error||"Unknown error","bad");return}
    if(s.state==="done"){$("cstatus").textContent="Finished.";const f=$("crep");f.style.display="block";f.srcdoc=s.html;
      const dl=$("cdl");dl.style.display="flex";dl.textContent="";
      ["html","json","csv"].forEach(x=>{const a=mk("a");a.href="/api/check/download?fmt="+x+"&token="+encodeURIComponent(token);a.style.flex="1";
        const b=mk("button",null,"Download "+x.toUpperCase());b.type="button";b.style.width="100%";a.appendChild(b);dl.appendChild(a)})}
  }catch(e){say("checkmsg",e.message,"bad")}}
$("btnCheck").onclick=async()=>{say("checkmsg","");
  const b=Object.assign(conn(),{clusters_extra:$("cx").value,enabled:CB.boxes.filter(x=>x.checked).map(x=>x.value)});
  $("btnCheck").disabled=true;
  try{await api("/api/check/run",b);$("crep").style.display="none";$("cdl").style.display="none";
    $("cstatus").textContent="Running...";CB.timer=setInterval(pollCheck,1000);pollCheck()}
  catch(e){$("btnCheck").disabled=false;say("checkmsg",e.message,"bad")}};
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
    ap.add_argument("--check-config", help="JSON file with the LOCKED compliance benchmarks (see --init-check-config)")
    ap.add_argument("--check-out", default="reports", help="where compliance reports are saved")
    ap.add_argument("--init-check-config", action="store_true", help="write a sample check_config.json here, then exit")
    ap.add_argument("--certfile")
    ap.add_argument("--keyfile")
    args = ap.parse_args()

    if args.init_check_config:
        if os.path.exists("check_config.json"):
            print("check_config.json exists, left alone")
        else:
            write_private("check_config.json", json.dumps(DEFAULT_CONFIG, indent=2) + "\n")
            print("wrote check_config.json")
        return
    # Store the settings where the request handlers can see them.
    App.token, App.outdir = args.token, args.outdir
    CheckApp.cfg = deep_merge(DEFAULT_CONFIG, load_json(args.check_config, "config") if args.check_config else {})
    CheckApp.outdir = args.check_out
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
    print("%s: %s://%s:%d  (results in %s)" % (APP_NAME, scheme, args.host, args.port,
                                                           os.path.abspath(App.outdir)))
    print("Compliance benchmarks: %s (locked, read from the file only)" % (args.check_config or "built-in defaults"))
    # Serve requests until Ctrl+C. A running scan is stopped when the program exits.
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
