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
Scan results are written as CSV files to ./scans (change with --outdir).
"""
import argparse
import base64
import csv
import json
import os
import queue
import re
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

SKIP = {".", "..", ".snapshot", "~snapshot"}
FIELDS = "name,type,size,bytes_used,accessed_time,modified_time"
MAX_ROWS_IN_MEMORY = 200000   # the CSV always has every row; the GUI table is capped
MAX_ERRORS_KEPT = 500
BUCKETS = [("under 1 year", 365), ("1-2 years", 730), ("2-3 years", 1095),
           ("3-5 years", 1825), ("over 5 years", None)]


# --------------------------------------------------------------------------
# ONTAP REST client (urllib only)
# --------------------------------------------------------------------------
class ApiError(Exception):
    def __init__(self, code, msg):
        super().__init__("HTTP %s: %s" % (code, msg) if code else msg)
        self.code = code


class Ontap:
    def __init__(self, host, user, password, tls="verify", ca=None, timeout=60):
        host = host.strip().rstrip("/")
        if "://" not in host:
            host = "https://" + host
        self.base = host
        token = base64.b64encode(("%s:%s" % (user, password)).encode()).decode()
        self.headers = {"Authorization": "Basic " + token, "Accept": "application/json"}
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
        url = path if path.startswith("http") else self.base + path
        if params:
            url += ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
        delay = 1.0
        for attempt in range(retries + 1):
            try:
                req = urllib.request.Request(url, headers=self.headers)
                with urllib.request.urlopen(req, timeout=self.timeout, context=self.ctx) as r:
                    return json.loads(r.read().decode("utf-8", "replace"))
            except urllib.error.HTTPError as e:
                if e.code in (429, 500, 502, 503, 504) and attempt < retries:
                    time.sleep(delay)
                    delay *= 2
                    continue
                raise ApiError(e.code, self._error_text(e))
            except (urllib.error.URLError, OSError) as e:
                if attempt < retries:
                    time.sleep(delay)
                    delay *= 2
                    continue
                raise ApiError(0, str(getattr(e, "reason", e)))

    @staticmethod
    def _error_text(e):
        try:
            body = json.loads(e.read().decode("utf-8", "replace"))
            return body.get("error", {}).get("message") or str(e.reason)
        except Exception:
            return str(e.reason)

    def paged(self, path, params):
        """Yield records, following _links.next.href verbatim."""
        url, p = path, params
        while url:
            body = self.get(url, p)
            for rec in body.get("records", []):
                yield rec
            nxt = body.get("_links", {}).get("next", {}).get("href")
            url, p = (nxt if nxt else None), None   # href already carries the query

    def cluster_info(self):
        return self.get("/api/cluster", {"fields": "name,version"})

    def volumes(self):
        out = []
        for v in self.paged("/api/storage/volumes",
                            {"fields": "name,uuid,svm.name,state,type,style", "max_records": 500}):
            out.append({"uuid": v.get("uuid"), "name": v.get("name"),
                        "svm": (v.get("svm") or {}).get("name", ""),
                        "state": v.get("state", ""), "type": v.get("type", "")})
        out.sort(key=lambda v: (v["svm"], v["name"]))
        return out

    def dir_url(self, vol, rel, root_style):
        seg = quote_path(rel) if rel else root_style
        return "/api/storage/volumes/%s/files/%s" % (vol, seg)

    def list_dir(self, vol, rel, root_style):
        return self.paged(self.dir_url(vol, rel, root_style),
                          {"fields": FIELDS, "max_records": 1000})


def quote_path(rel):
    # The {path} segment is ONE path parameter: slashes must be sent as %2F.
    return urllib.parse.quote(rel.strip("/"), safe="")


def file_ext(path):
    name = path.rsplit("/", 1)[-1].lower()
    for multi in (".tar.gz", ".tar.bz2", ".tar.xz"):
        if name.endswith(multi):
            return multi
    dot = name.rfind(".")
    return name[dot:] if 0 < dot < len(name) - 1 else "(none)"


_TS_FRAC = re.compile(r"\.\d+")
_TS_TZ = re.compile(r"([+-]\d\d):(\d\d)$")


def parse_ts(s):
    if not s:
        return None
    try:
        s = _TS_FRAC.sub("", s)
        s = s.replace("Z", "+0000")
        s = _TS_TZ.sub(r"\1\2", s)
        if not re.search(r"[+-]\d{4}$", s):
            s += "+0000"
        return datetime.strptime(s, "%Y-%m-%dT%H:%M:%S%z")
    except ValueError:
        return None


def csv_safe(text):
    return "'" + text if text[:1] in ("=", "+", "-", "@") else text


# --------------------------------------------------------------------------
# Scan engine: shared work queue, bounded worker pool, per-directory errors
# --------------------------------------------------------------------------
class Scan:
    def __init__(self, cfg, client, outdir):
        self.cfg, self.client = cfg, client
        self.lock = threading.Lock()
        self.q = queue.Queue()
        self.pending = 0
        self.stop_ev = threading.Event()
        self.state = "starting"
        self.message = ""
        self.started = time.time()
        self.finished = None
        self.dirs = self.files = self.cold_files = 0
        self.cold_bytes = self.total_bytes = self.unknown_ts = 0
        self.excl_files = self.excl_bytes = 0
        self.bucket_files = [0] * len(BUCKETS)
        self.bucket_bytes = [0] * len(BUCKETS)
        self.by_dir = {}
        self.by_ext = {}
        self.by_year = {}
        self.errors, self.error_count = [], 0
        self.rows = []
        self.root_style = ""
        stamp = time.strftime("%Y%m%d-%H%M%S")
        safe_vol = re.sub(r"[^A-Za-z0-9_.-]", "_", cfg["volume_name"] or cfg["volume"])
        self.csv_name = "cryo_%s_%s.csv" % (safe_vol, stamp)
        self.csv_path = os.path.join(outdir, self.csv_name)
        self.now = datetime.now(timezone.utc)
        self.cutoff_days = cfg["days"]

    # -- lifecycle ---------------------------------------------------------
    def start(self):
        threading.Thread(target=self._run, daemon=True).start()

    def stop(self):
        self.stop_ev.set()

    def _run(self):
        try:
            self._probe_root()
            self.csv_file = open(self.csv_path, "w", newline="", encoding="utf-8")
            self.csv_writer = csv.writer(self.csv_file)
            self.csv_writer.writerow(["path", "bytes_used", "accessed_time", "modified_time", "age_days"])
            root = self.cfg["root"].strip("/")
            with self.lock:
                self.pending = 1
            self.q.put(root)
            self.state = "running"
            workers = [threading.Thread(target=self._worker, daemon=True)
                       for _ in range(self.cfg["workers"])]
            for w in workers:
                w.start()
            for w in workers:
                w.join()
            self.state = "stopped" if self.stop_ev.is_set() else "done"
        except Exception as e:  # noqa
            self.state, self.message = "failed", str(e)
        finally:
            try:
                self.csv_file.close()
            except Exception:
                pass
            self.finished = time.time()

    def _probe_root(self):
        """Different ONTAP builds accept different spellings for the volume root."""
        last = None
        for style in ("", "%2F"):
            try:
                url = "/api/storage/volumes/%s/files/%s" % (self.cfg["volume"], style)
                self.client.get(url, {"fields": "name", "max_records": 1})
                self.root_style = style
                return
            except ApiError as e:
                last = e
                if e.code in (401, 403):
                    break
        raise last

    def _worker(self):
        while not self.stop_ev.is_set():
            try:
                rel = self.q.get(timeout=0.5)
            except queue.Empty:
                with self.lock:
                    if self.pending <= 0:
                        return
                continue
            try:
                self._process(rel)
            except Exception as e:  # keep scanning after a bad directory
                self._error(rel, str(e))
            finally:
                with self.lock:
                    self.pending -= 1

    def _error(self, rel, msg):
        with self.lock:
            self.error_count += 1
            if len(self.errors) < MAX_ERRORS_KEPT:
                self.errors.append({"path": "/" + rel, "error": msg})

    # -- per-directory work -------------------------------------------------
    def _process(self, rel):
        cfg, mode = self.cfg, self.cfg["mode"]
        sub_dirs, hits = [], []
        n_files = n_bytes = n_unknown = x_files = x_bytes = 0
        excl = tuple(cfg["exclude"])
        for rec in self.client.list_dir(cfg["volume"], rel, self.root_style):
            if self.stop_ev.is_set():
                return
            name = rec.get("name")
            if not name or name in SKIP:
                continue
            child = (rel + "/" + name) if rel else name
            kind = rec.get("type")
            if kind == "directory":
                sub_dirs.append(child)
            elif kind == "file":
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
                used = {"both": [a, m], "atime": [a], "mtime": [m]}[mode]
                if any(t is None for t in used):
                    n_unknown += 1
                    continue
                age = (self.now - max(used)).days     # age of the most recent timestamp used
                if age >= self.cutoff_days:
                    hits.append((child, size, a, m, age))
        # commit results for this directory
        with self.lock:
            self.dirs += 1
            self.files += n_files
            self.total_bytes += n_bytes
            self.unknown_ts += n_unknown
            self.excl_files += x_files
            self.excl_bytes += x_bytes
            for path, size, a, m, age in hits:
                self.cold_files += 1
                self.cold_bytes += size
                b = next(i for i, (_, lim) in enumerate(BUCKETS) if lim is None or age < lim)
                self.bucket_files[b] += 1
                self.bucket_bytes[b] += size
                parts = path.split("/")[:-1][:cfg["depth"]]
                key = "/" + "/".join(parts)
                d = self.by_dir.setdefault(key, [0, 0])
                d[0] += 1
                d[1] += size
                xt = self.by_ext.setdefault(file_ext(path), [0, 0])
                xt[0] += 1
                xt[1] += size
                yr = self.by_year.setdefault(str(m.year) if m else "unknown", [0, 0])
                yr[0] += 1
                yr[1] += size
                m_age = (self.now - m).days if m else -1
                a_age = (self.now - a).days if a else -1
                a_s = a.isoformat() if a else ""
                m_s = m.isoformat() if m else ""
                self.csv_writer.writerow([csv_safe("/" + path), size, a_s, m_s, age])
                if len(self.rows) < MAX_ROWS_IN_MEMORY:
                    self.rows.append(("/" + path, size, a_s, m_s, age, m_age, a_age))
            self.pending += len(sub_dirs)
        for d in sub_dirs:
            self.q.put(d)

    # -- views for the GUI --------------------------------------------------
    def status(self):
        with self.lock:
            end = self.finished or time.time()
            el = max(end - self.started, 0.001)
            top = sorted(self.by_dir.items(), key=lambda kv: kv[1][1], reverse=True)[:30]
            types = sorted(self.by_ext.items(), key=lambda kv: kv[1][1], reverse=True)[:12]
            years = sorted(self.by_year.items())
            return {
                "state": self.state, "message": self.message, "elapsed": el,
                "dirs": self.dirs, "files": self.files, "cold_files": self.cold_files,
                "cold_bytes": self.cold_bytes, "total_bytes": self.total_bytes,
                "unknown_ts": self.unknown_ts, "queued": max(self.pending - 1, 0),
                "excl_files": self.excl_files, "excl_bytes": self.excl_bytes,
                "dirs_per_sec": self.dirs / el,
                "buckets": [{"label": BUCKETS[i][0], "files": self.bucket_files[i],
                             "bytes": self.bucket_bytes[i]} for i in range(len(BUCKETS))],
                "top_dirs": [{"path": k, "files": v[0], "bytes": v[1]} for k, v in top],
                "types": [{"ext": k, "files": v[0], "bytes": v[1]} for k, v in types],
                "years": [{"year": k, "files": v[0], "bytes": v[1]} for k, v in years],
                "errors": self.errors[-100:], "error_count": self.error_count,
                "csv": self.csv_name, "config": {k: v for k, v in self.cfg.items()},
                "rows_truncated": self.cold_files > len(self.rows),
            }

    def query_rows(self, q, sorts, offset, limit, flt=None):
        with self.lock:
            rows = list(self.rows)
        if q:
            ql = q.lower()
            rows = [r for r in rows if ql in r[0].lower()]
        f = flt or {}
        if f.get("min") is not None:
            rows = [r for r in rows if r[1] >= f["min"]]
        if f.get("max") is not None:
            rows = [r for r in rows if r[1] <= f["max"]]
        if f.get("mod") is not None:
            rows = [r for r in rows if r[5] >= f["mod"]]
        if f.get("acc") is not None:
            rows = [r for r in rows if r[6] >= f["acc"]]
        if f.get("ext"):
            ext = tuple(f["ext"])
            rows = [r for r in rows if r[0].lower().endswith(ext)]
        total_bytes = sum(r[1] for r in rows)
        cols = {"path": 0, "size": 1, "atime": 2, "mtime": 3, "age": 4}
        for key, desc in reversed(sorts):      # stable sorts: last criterion first
            rows.sort(key=lambda r, i=cols[key]: r[i], reverse=desc)
        return {"total": len(rows), "total_bytes": total_bytes, "rows": rows[offset:offset + limit]}


# --------------------------------------------------------------------------
# HTTP server
# --------------------------------------------------------------------------
class Server(ThreadingMixIn, HTTPServer):
    daemon_threads = True
    allow_reuse_address = True


class App:
    scan = None
    token = None
    outdir = "scans"
    lock = threading.Lock()


def client_from(body):
    return Ontap(body.get("cluster", ""), body.get("user", ""), body.get("password", ""),
                 tls=body.get("tls", "verify"), ca=(body.get("ca") or "").strip() or None)


def clamp(v, lo, hi, default):
    try:
        return max(lo, min(hi, int(v)))
    except (TypeError, ValueError):
        return default


class Handler(BaseHTTPRequestHandler):
    server_version = "Cryo/1.0"

    def log_message(self, fmt, *args):
        sys.stderr.write("%s %s\n" % (self.address_string(), fmt % args))

    # helpers
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
        if not App.token:
            return True
        supplied = self.headers.get("X-Token") or urllib.parse.parse_qs(
            urllib.parse.urlparse(self.path).query).get("token", [""])[0]
        return supplied == App.token

    def _body(self):
        n = int(self.headers.get("Content-Length") or 0)
        return json.loads(self.rfile.read(n).decode() or "{}") if n else {}

    def _file(self, name):
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
        if url.path == "/":
            return self._send(200, PAGE.encode(), "text/html; charset=utf-8")
        if not self._authed():
            return self._send(401, {"error": "Access token required"})
        if url.path == "/api/status":
            s = App.scan
            return self._send(200, s.status() if s else {"state": "idle"})
        if url.path == "/api/results":
            s = App.scan
            if not s:
                return self._send(200, {"total": 0, "rows": []})
            g = lambda k, d="": qs.get(k, [d])[0]
            sorts = []
            for part in g("sort", "size:desc").split(",")[:4]:
                key, _, direction = part.partition(":")
                if key in ("path", "size", "atime", "mtime", "age"):
                    sorts.append((key, direction != "asc"))
            def num(k):
                try:
                    return float(g(k)) if g(k) != "" else None
                except ValueError:
                    return None
            flt = {"min": num("fmin"), "max": num("fmax"), "mod": num("mod"), "acc": num("acc"),
                   "ext": [("." + t.lstrip("*.")).lower()
                           for t in re.split(r"[,\s;]+", g("ext")) if t.strip("*.")]}
            return self._send(200, s.query_rows(
                g("q"), sorts or [("size", True)],
                clamp(g("offset", "0"), 0, 10**9, 0), clamp(g("limit", "100"), 1, 1000, 100),
                flt=flt))
        if url.path == "/api/history":
            os.makedirs(App.outdir, exist_ok=True)
            items = []
            for n in sorted(os.listdir(App.outdir), reverse=True):
                if n.endswith(".csv"):
                    st = os.stat(os.path.join(App.outdir, n))
                    items.append({"name": n, "bytes": st.st_size,
                                  "modified": time.strftime("%Y-%m-%d %H:%M", time.localtime(st.st_mtime))})
            return self._send(200, {"files": items})
        if url.path == "/api/file":
            return self._file(qs.get("name", [""])[0])
        self._send(404, {"error": "Not found"})

    def do_POST(self):
        if not self._authed():
            return self._send(401, {"error": "Access token required"})
        try:
            body = self._body()
            path = urllib.parse.urlparse(self.path).path
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
            self._send(404, {"error": "Not found"})
        except ApiError as e:
            self._send(502, {"error": str(e)})
        except ValueError as e:
            self._send(400, {"error": str(e)})
        except Exception as e:  # noqa
            self._send(500, {"error": "%s: %s" % (type(e).__name__, e)})

    def _start(self, b):
        with App.lock:
            if App.scan and App.scan.state in ("starting", "running"):
                return self._send(409, {"error": "A scan is already running. Stop it first."})
            vol = (b.get("volume") or "").strip()
            if not re.fullmatch(r"[0-9a-fA-F-]{36}", vol):
                raise ValueError("Volume must be a UUID. Use Load volumes to pick one.")
            mode = b.get("mode", "both")
            if mode not in ("both", "atime", "mtime"):
                raise ValueError("Unknown criteria")
            tokens = [t for t in re.split(r"[,\s;]+", b.get("exclude") or "") if t.strip("*.")]
            excl = sorted({("." + t.lstrip("*.")).lower() for t in tokens})[:50]
            cfg = {"cluster": b.get("cluster", ""), "volume": vol,
                   "volume_name": (b.get("volume_name") or "").strip(),
                   "root": (b.get("root") or "").strip(), "mode": mode,
                   "days": clamp(b.get("days"), 1, 36500, 180),
                   "workers": clamp(b.get("workers"), 1, 16, 6),
                   "depth": clamp(b.get("depth"), 1, 10, 2),
                   "exclude": excl}
            os.makedirs(App.outdir, exist_ok=True)
            App.scan = Scan(cfg, client_from(b), App.outdir)
            App.scan.start()
        self._send(200, {"ok": True})


# --------------------------------------------------------------------------
# Embedded GUI (no external resources)
# --------------------------------------------------------------------------
PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Cryo</title>
<style>
:root{--bg:#eef2f4;--panel:#fff;--ink:#15262e;--mute:#5b6e77;--line:#d3dde2;--ice:#1f6f99;--ice-soft:#dbeaf3;--warn:#a85a00;--bad:#b3261e;--ok:#1d7a4a}
@media (prefers-color-scheme:dark){:root{--bg:#10191e;--panel:#172329;--ink:#e3edf1;--mute:#8fa4ae;--line:#2a3b44;--ice:#6bb6dd;--ice-soft:#1c3340;--warn:#e0a050;--bad:#f2867e;--ok:#6fcf9b}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.45 system-ui,-apple-system,"Segoe UI",Roboto,"Helvetica Neue",Arial,sans-serif}
header{display:flex;align-items:center;gap:14px;padding:14px 22px;border-bottom:1px solid var(--line);background:var(--panel)}
h1{font-size:18px;margin:0;font-weight:650}
.pill{padding:2px 10px;border-radius:99px;background:var(--ice-soft);color:var(--ice);font-size:13px;font-weight:600}
.pill.running{background:var(--ice);color:var(--panel)} .pill.failed{background:var(--bad);color:var(--panel)} .pill.done{background:var(--ok);color:var(--panel)}
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
.tiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:12px;margin-bottom:16px}
.tile{background:var(--panel);border:1px solid var(--line);border-radius:6px;padding:12px 14px}
.tile b{display:block;font-size:22px;font-weight:650;font-variant-numeric:tabular-nums}
.tile span{font-size:13px;color:var(--mute)}
.tile.hot b{color:var(--ice)}
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
.filters{display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:2px 10px;margin-bottom:12px}.filters label{margin:6px 0 3px}
.cgrid{display:grid;grid-template-columns:repeat(auto-fit,minmax(340px,1fr));gap:20px}.cgrid h2{margin:0 0 6px}.cwide{grid-column:1/-1}
.ch{width:100%;height:auto;display:block}.ch text{fill:var(--ink);font-size:12px}.ch .m{fill:var(--mute);font-size:11px}.ch .tt{fill:var(--panel);font-weight:600}
.pager{display:flex;gap:10px;align-items:center;margin-top:10px;color:var(--mute);font-size:13px}
</style></head><body>
<header><h1>Cryo</h1><span class="hint" style="margin:0">Cold data finder</span><span id="pill" class="pill">idle</span><span id="hdrmsg" class="hint" style="margin:0"></span></header>
<main>
<div>
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
  <div class="panel"><h2>Scan</h2>
    <label for="volume">Volume</label><input id="volume" list="vols" placeholder="Pick from list or paste UUID" autocomplete="off"><datalist id="vols"></datalist>
    <label for="root">Start folder (volume-relative, blank for root)</label><input id="root" placeholder="projects/archive_2022">
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
  <div class="tiles">
    <div class="tile"><b id="t_dirs">0</b><span>folders scanned</span></div>
    <div class="tile"><b id="t_files">0</b><span>files checked</span></div>
    <div class="tile hot"><b id="t_cold">0</b><span id="t_cold_s">cold files</span></div>
    <div class="tile hot"><b id="t_coldb">0 B</b><span id="t_pct">cold size</span></div>
    <div class="tile"><b id="t_rate">0</b><span>folders per second</span></div>
    <div class="tile"><b id="t_time">0:00</b><span id="t_queue">elapsed</span></div>
  </div>
  <div class="panel">
    <div class="tabs" id="tabs">
      <button data-t="summary" class="on">Summary</button><button data-t="charts">Charts</button><button data-t="files">Files</button>
      <button data-t="errors">Errors <span id="errc"></span></button><button data-t="history">Saved scans</button>
    </div>
    <div id="tab_summary">
      <div id="exnote" class="hint" style="margin-top:0"></div>
      <h2>Cold data by age</h2><div class="tbl"><table id="buckets"></table></div>
      <h2 style="margin-top:20px">Largest cold folders</h2><div class="tbl"><table id="topdirs"></table></div>
    </div>
    <div id="tab_charts" style="display:none"><div id="charts"></div></div>
    <div id="tab_files" style="display:none">
      <input id="fq" placeholder="Filter by path" style="margin-bottom:6px">
      <div class="filters">
        <div><label for="fmin">Size at least</label><div class="row"><input id="fmin" type="number" min="0" step="any" placeholder="0"><select id="fminu" aria-label="Minimum size unit"><option value="1024">KiB</option><option value="1048576">MiB</option><option value="1073741824" selected>GiB</option></select></div></div>
        <div><label for="fmax">Size at most</label><div class="row"><input id="fmax" type="number" min="0" step="any" placeholder="no limit"><select id="fmaxu" aria-label="Maximum size unit"><option value="1024">KiB</option><option value="1048576">MiB</option><option value="1073741824" selected>GiB</option></select></div></div>
        <div><label for="fmod">Not modified for (days)</label><input id="fmod" type="number" min="0" placeholder="e.g. 730"></div>
        <div><label for="facc">Not accessed for (days)</label><input id="facc" type="number" min="0" placeholder="e.g. 730"></div>
        <div><label for="fext">Only these file types</label><input id="fext" placeholder=".vmdk, .iso"></div>
        <div style="align-self:end"><button id="fclear">Clear filters</button></div>
      </div>
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
const $=id=>document.getElementById(id);
const esc=s=>String(s).replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const fmtB=n=>{const u=["B","KiB","MiB","GiB","TiB","PiB"];let i=0;n=Number(n)||0;while(n>=1024&&i<u.length-1){n/=1024;i++}return (i?n.toFixed(n<10?2:1):n)+" "+u[i]};
const fmtN=n=>Number(n||0).toLocaleString();
const fmtT=s=>{s=Math.floor(s);const h=Math.floor(s/3600),m=Math.floor(s%3600/60),x=s%60;return (h?h+":"+String(m).padStart(2,"0"):m)+":"+String(x).padStart(2,"0")};
let token=sessionStorage.getItem("tok")||"", page=0, tab="summary", lastState="idle";
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
const conn=()=>({cluster:$("cluster").value,user:$("user").value,password:$("password").value,tls:$("tls").value,ca:$("ca").value});
function say(id,text,cls){const e=$(id);e.textContent=text;e.className="msg "+(cls||"")}
$("tls").onchange=()=>{$("cawrap").style.display=$("tls").value==="ca"?"block":"none"};
$("btnTest").onclick=async()=>{say("connmsg","Connecting...");
  try{const r=await api("/api/test",conn());say("connmsg","Connected to "+r.name+" ("+r.version+")","ok")}catch(e){say("connmsg",e.message,"bad")}};
let volMap={};
$("btnVols").onclick=async()=>{say("connmsg","Loading volumes...");
  try{const r=await api("/api/volumes",conn());volMap={};
    $("vols").innerHTML=r.volumes.map(v=>{volMap[v.uuid]=v.name;return `<option value="${esc(v.uuid)}">${esc(v.svm)}:${esc(v.name)} (${esc(v.type||v.state)})</option>`}).join("");
    say("connmsg",r.volumes.length+" volumes loaded. Click the Volume box to choose one.","ok")}catch(e){say("connmsg",e.message,"bad")}};
$("btnStart").onclick=async()=>{
  const b=Object.assign(conn(),{volume:$("volume").value.trim(),volume_name:volMap[$("volume").value.trim()]||"",root:$("root").value,
    days:$("days").value,workers:$("workers").value,mode:$("mode").value,depth:$("depth").value,exclude:$("exclude").value});
  say("scanmsg","Starting...");
  try{await api("/api/scan/start",b);say("scanmsg","");page=0;poll()}catch(e){say("scanmsg",e.message,"bad")}};
$("btnStop").onclick=async()=>{try{await api("/api/scan/stop",{});say("scanmsg","Stopping after the current folders finish...")}catch(e){say("scanmsg",e.message,"bad")}};
document.querySelectorAll("#tabs button").forEach(b=>b.onclick=()=>{tab=b.dataset.t;
  document.querySelectorAll("#tabs button").forEach(x=>x.classList.toggle("on",x===b));
  ["summary","charts","files","errors","history"].forEach(t=>$("tab_"+t).style.display=t===tab?"block":"none");
  if(tab==="files")loadFiles();if(tab==="history")loadHistory();if(tab==="charts")drawCharts(LAST)});
let LAST=null;
function treemap(items,x,y,w,h,out){
  if(!items.length)return;
  if(items.length===1){out.push(Object.assign({},items[0],{x:x,y:y,w:w,h:h}));return}
  const tot=items.reduce((a,i)=>a+i.v,0);let k=1,acc=items[0].v;
  while(k<items.length-1&&acc<tot/2){acc+=items[k].v;k++}
  const A=items.slice(0,k),B=items.slice(k);
  if(w>=h){const wa=w*acc/tot;treemap(A,x,y,wa,h,out);treemap(B,x+wa,y,w-wa,h,out)}
  else{const ha=h*acc/tot;treemap(A,x,y,w,ha,out);treemap(B,x,y+ha,w,h-ha,out)}
}
function vbars(items,label){
  if(!items.length)return '<div class="empty">No data yet.</div>';
  const n=items.length,W=Math.max(420,n*46),H=210,top=22,bot=30,step=(W-20)/n,bw=Math.min(44,step-8),mx=Math.max(1,...items.map(i=>i.v));
  return `<svg class="ch" viewBox="0 0 ${W} ${H}" role="img" aria-label="${esc(label)}">`+items.map((it,i)=>{
    const h=(H-top-bot)*it.v/mx,x=10+i*step+(step-bw)/2,y=H-bot-h;
    return `<g><title>${esc(it.t)}</title><rect x="${x}" y="${y}" width="${bw}" height="${Math.max(h,1)}" rx="2" fill="var(--ice)"/>`+
      (step>=60?`<text x="${x+bw/2}" y="${y-5}" text-anchor="middle" class="m">${fmtB(it.v)}</text>`:"")+
      `<text x="${x+bw/2}" y="${H-12}" text-anchor="middle">${esc(it.l)}</text></g>`}).join("")+"</svg>";
}
function hbars(items){
  const mx=Math.max(1,...items.map(i=>i.v)),rh=26,W=560,lw=78,rw=150;
  return `<svg class="ch" viewBox="0 0 ${W} ${items.length*rh+4}" role="img" aria-label="Cold size by file type">`+items.map((it,i)=>{
    const y=i*rh+2,bw=(W-lw-rw)*it.v/mx;
    const attr=it.ext&&it.ext.charAt(0)==="."?` data-ext="${esc(it.ext)}" style="cursor:pointer"`:"";
    return `<g${attr}><title>${esc(it.t)}</title><text x="0" y="${y+16}">${esc(it.l)}</text><rect x="${lw}" y="${y+4}" width="${Math.max(bw,1)}" height="14" rx="2" fill="var(--ice)"/><text x="${lw+bw+6}" y="${y+16}" class="m">${fmtB(it.v)} · ${fmtN(it.f)} files</text></g>`}).join("")+"</svg>";
}
function goFiles(path,ext){$("fq").value=path;$("fext").value=ext;page=0;document.querySelector('#tabs button[data-t="files"]').click()}
function drawCharts(s){
  const el=$("charts");
  if(!s||!s.buckets||!s.files){el.innerHTML='<div class="empty">Start a scan to see charts.</div>';return}
  const tot=s.total_bytes||0,cold=s.cold_bytes||0,pct=tot?cold/tot:0,C=2*Math.PI*70;
  const donut=`<svg class="ch" viewBox="0 0 260 190" role="img" aria-label="Cold share of scanned data"><circle cx="95" cy="95" r="70" fill="none" stroke="var(--line)" stroke-width="24"/><circle cx="95" cy="95" r="70" fill="none" stroke="var(--ice)" stroke-width="24" stroke-dasharray="${pct*C} ${C}" transform="rotate(-90 95 95)"/><text x="95" y="93" text-anchor="middle" style="font-size:24px;font-weight:650">${(pct*100).toFixed(1)}%</text><text x="95" y="113" text-anchor="middle" class="m">cold by size</text><rect x="182" y="70" width="10" height="10" rx="2" fill="var(--ice)"/><text x="198" y="79">Cold</text><text x="198" y="94" class="m">${fmtB(cold)}</text><rect x="182" y="112" width="10" height="10" rx="2" fill="var(--line)"/><text x="198" y="121">Not cold</text><text x="198" y="136" class="m">${fmtB(Math.max(0,tot-cold))}</text></svg>`;
  const age=vbars(s.buckets.map(b=>({l:b.label,v:b.bytes,t:b.label+": "+fmtB(b.bytes)+", "+fmtN(b.files)+" files"})),"Cold size by age");
  const yrs=vbars((s.years||[]).map(y=>({l:y.year,v:y.bytes,t:y.year+": "+fmtB(y.bytes)+", "+fmtN(y.files)+" files"})),"Cold size by year last modified");
  const dirs=(s.top_dirs||[]).filter(d=>d.bytes>0).map(d=>({v:d.bytes,path:d.path,files:d.files}));
  const rest=cold-dirs.reduce((a,d)=>a+d.v,0);
  if(rest>cold*0.005)dirs.push({v:rest,path:"",files:0,other:1});
  dirs.sort((a,b)=>b.v-a.v);dirs.forEach((d,i)=>{d.rank=i});
  const out=[];treemap(dirs,0,0,700,300,out);
  const tree=dirs.length?`<svg class="ch" viewBox="0 0 700 300" role="img" aria-label="Cold size by folder">`+out.map(t=>{
    const name=t.other?"All other folders":t.path,mc=Math.floor((t.w-14)/7),lab=name.length>mc?"…"+name.slice(-(mc-1)):name;
    const fill=t.other?'fill="var(--line)"':`fill="var(--ice)" fill-opacity="${(0.7+0.3*(1-t.rank/Math.max(1,dirs.length-1))).toFixed(2)}"`;
    const tcls=t.other?"":' class="tt"';
    const attr=t.other?"":` data-path="${esc(t.path)}" style="cursor:pointer"`;
    return `<g${attr}><title>${esc(name)}\n${fmtB(t.v)}${t.files?", "+fmtN(t.files)+" files":""}</title><rect x="${t.x}" y="${t.y}" width="${t.w}" height="${t.h}" ${fill} stroke="var(--panel)" stroke-width="2"/>`+
      (t.w>60&&t.h>36&&mc>3?`<text x="${t.x+8}" y="${t.y+18}"${tcls}>${esc(lab)}</text><text x="${t.x+8}" y="${t.y+34}"${tcls} style="font-weight:400">${fmtB(t.v)}</text>`:"")+"</g>"}).join("")+"</svg>":'<div class="empty">No cold files found yet.</div>';
  const ty=(s.types||[]).slice(0,10).map(t=>({l:t.ext,ext:t.ext,v:t.bytes,f:t.files,t:t.ext+": "+fmtB(t.bytes)+", "+fmtN(t.files)+" files"}));
  const trest=cold-ty.reduce((a,t)=>a+t.v,0),frest=(s.cold_files||0)-ty.reduce((a,t)=>a+t.f,0);
  if(trest>cold*0.005)ty.push({l:"other",v:trest,f:Math.max(frest,0),t:"All other file types"});
  const types=ty.length?hbars(ty):'<div class="empty">No data yet.</div>';
  el.innerHTML=`<div class="cgrid"><div><h2>Cold versus the rest</h2>${donut}</div><div><h2>Cold data by age</h2>${age}</div>`+
    `<div class="cwide"><h2>Where the cold data is</h2><div class="hint" style="margin:0 0 6px">Box size is cold size. Click a box to list its files.</div>${tree}</div>`+
    `<div><h2>By file type</h2><div class="hint" style="margin:0 0 6px">Click a bar to list those files.</div>${types}</div><div><h2>By year last modified</h2>${yrs}</div></div>`;
}
$("charts").onclick=e=>{const g=e.target.closest("[data-path],[data-ext]");if(g)goFiles(g.dataset.path||"",g.dataset.ext||"")};
function emptyRow(cols,text){return `<tr><td colspan="${cols}" class="empty">${text}</td></tr>`}
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
  $("topdirs").innerHTML="<tr><th>Folder</th><th class='n'>Cold files</th><th class='n'>Cold size</th></tr>"+
    (s.top_dirs.length?s.top_dirs.map(d=>`<tr><td class="p">${esc(d.path)}</td><td class="n">${fmtN(d.files)}</td><td class="n">${fmtB(d.bytes)}</td></tr>`).join(""):emptyRow(3,"No cold files found yet."));
  $("exnote").textContent=s.excl_files?("Excluded by file type: "+fmtN(s.excl_files)+" files, "+fmtB(s.excl_bytes)+". They are not counted in the totals.") :"";
  $("errc").textContent=s.error_count?"("+fmtN(s.error_count)+")":"";
  $("errs").innerHTML="<tr><th>Folder</th><th>Error</th></tr>"+(s.errors.length?s.errors.map(e=>`<tr><td class="p">${esc(e.path)}</td><td>${esc(e.error)}</td></tr>`).join(""):emptyRow(2,"No folder errors."));
  $("trunc").textContent=s.rows_truncated?"The table shows the first 200,000 cold files. The CSV has all of them.":(s.unknown_ts?fmtN(s.unknown_ts)+" files had no usable timestamp and were not counted.":"");
  $("dl").href="/api/file?name="+encodeURIComponent(s.csv)+(token?"&token="+encodeURIComponent(token):"");
  if(!run&&lastState==="running"&&tab==="files")loadFiles();
  lastState=s.state;
}
async function loadFiles(){
  try{const q=encodeURIComponent($("fq").value),sort=encodeURIComponent(sortSpec());
    const r=await api(`/api/results?q=${q}&sort=${sort}&offset=${page*100}&limit=100${filterQS()}`);
    $("files").innerHTML=hdr()+
      (r.rows.length?r.rows.map(x=>`<tr><td class="p">${esc(x[0])}</td><td class="n">${fmtB(x[1])}</td><td class="n">${fmtN(x[4])}</td><td>${esc(x[3].slice(0,10))}</td><td>${esc(x[2].slice(0,10))}</td></tr>`).join(""):emptyRow(5,"No cold files to show yet."));
    document.querySelectorAll("#files th[data-k]").forEach(h=>h.onclick=()=>headSort(h.dataset.k));
    $("pginfo").textContent=r.total?`${page*100+1}-${Math.min(r.total,page*100+100)} of ${fmtN(r.total)} files, ${fmtB(r.total_bytes||0)}`:"";
    $("prev").disabled=page===0;$("next").disabled=(page+1)*100>=r.total;
  }catch(e){}
}
$("prev").onclick=()=>{page=Math.max(0,page-1);loadFiles()};$("next").onclick=()=>{page++;loadFiles()};
$("fq").oninput=()=>{page=0;loadFiles()};
function filterQS(){const p=[],v=id=>$(id).value.trim();
  if(v("fmin")!=="")p.push("fmin="+Math.round(Number(v("fmin"))*Number($("fminu").value)));
  if(v("fmax")!=="")p.push("fmax="+Math.round(Number(v("fmax"))*Number($("fmaxu").value)));
  if(v("fmod")!=="")p.push("mod="+encodeURIComponent(v("fmod")));
  if(v("facc")!=="")p.push("acc="+encodeURIComponent(v("facc")));
  if(v("fext")!=="")p.push("ext="+encodeURIComponent(v("fext")));
  return p.length?"&"+p.join("&"):""}
["fmin","fminu","fmax","fmaxu","fmod","facc","fext"].forEach(id=>$(id).oninput=()=>{page=0;loadFiles()});
$("fclear").onclick=()=>{["fmin","fmax","fmod","facc","fext","fq"].forEach(id=>$(id).value="");page=0;loadFiles()};
const KEYS=[["size","Size"],["age","Cold age (days)"],["mtime","Modified date"],["atime","Accessed date"],["path","Path"]];
const DEFDIR={size:"desc",age:"desc",path:"asc",mtime:"asc",atime:"asc"};
const DIRLBL={size:["Largest first","Smallest first"],age:["Longest first","Shortest first"],mtime:["Newest first","Oldest first"],atime:["Newest first","Oldest first"],path:["Z to A","A to Z"]};
let SORTS=[{k:"size",d:"desc"},{k:"",d:"desc"},{k:"",d:"desc"}];
function sortSpec(){return SORTS.filter(s=>s.k).map(s=>s.k+":"+s.d).join(",")||"size:desc"}
function hdr(){const h=(k,l,c)=>`<th class="s ${c}" data-k="${k}">${l}${SORTS[0].k===k?(SORTS[0].d==="asc"?" ↑":" ↓"):""}</th>`;
  return "<tr>"+h("path","Path","")+h("size","Size","n")+h("age","Age (days)","n")+h("mtime","Modified","")+h("atime","Accessed","")+"</tr>"}
function drawSorts(){
  $("sorts").innerHTML=SORTS.map((s,i)=>{const l=DIRLBL[s.k||"size"];
    return `<div class="sortrow"><span>${i?"then by":"Sort by"}</span><select aria-label="Sort level ${i+1}" data-i="${i}" data-f="k">${i?'<option value="">(none)</option>':""}${KEYS.map(k=>`<option value="${k[0]}"${s.k===k[0]?" selected":""}>${k[1]}</option>`).join("")}</select>`+
    `<select aria-label="Direction ${i+1}" data-i="${i}" data-f="d"${s.k?"":" disabled"}><option value="desc"${s.d==="desc"?" selected":""}>${l[0]}</option><option value="asc"${s.d==="asc"?" selected":""}>${l[1]}</option></select></div>`}).join("");
  $("sorts").querySelectorAll("select").forEach(el=>el.onchange=()=>{const i=+el.dataset.i;
    if(el.dataset.f==="k"){SORTS[i].k=el.value;SORTS[i].d=el.value?DEFDIR[el.value]:"desc"}else SORTS[i].d=el.value;
    drawSorts();page=0;loadFiles()});
}
function headSort(k){const cur=SORTS[0];
  if(cur.k===k)cur.d=cur.d==="asc"?"desc":"asc";else{SORTS=SORTS.filter((s,i)=>i>0&&s.k!==k);SORTS.unshift({k,d:DEFDIR[k]});while(SORTS.length<3)SORTS.push({k:"",d:"desc"});SORTS=SORTS.slice(0,3)}
  drawSorts();page=0;loadFiles()}
document.querySelectorAll(".presets button").forEach(b=>b.onclick=()=>{
  SORTS=b.dataset.p.split(",").map(x=>{const [k,d]=x.split(":");return{k,d}});while(SORTS.length<3)SORTS.push({k:"",d:"desc"});
  drawSorts();page=0;loadFiles()});
async function loadHistory(){
  try{const r=await api("/api/history");
    $("hist").innerHTML="<tr><th>File</th><th>Saved</th><th class='n'>Size</th><th></th></tr>"+(r.files.length?r.files.map(f=>
      `<tr><td class="p">${esc(f.name)}</td><td>${esc(f.modified)}</td><td class="n">${fmtB(f.bytes)}</td><td><a href="/api/file?name=${encodeURIComponent(f.name)}${token?"&token="+encodeURIComponent(token):""}">Download</a></td></tr>`).join(""):emptyRow(4,"No saved scans yet. Each scan saves a CSV on the server."));
  }catch(e){}
}
async function poll(){
  try{const s=await api("/api/status");render(s);if(tab==="files"&&(s.state==="running"))loadFiles()}catch(e){$("hdrmsg").textContent=e.message}
}
drawSorts();poll();setInterval(poll,1500);
</script></body></html>
"""


def main():
    ap = argparse.ArgumentParser(description="Cryo: cold data finder for ONTAP NAS volumes (stdlib only)")
    ap.add_argument("--host", default="127.0.0.1", help="bind address (default 127.0.0.1)")
    ap.add_argument("--port", type=int, default=8080)
    ap.add_argument("--outdir", default="scans", help="where CSV results are saved")
    ap.add_argument("--token", default=os.environ.get("CRYO_TOKEN"),
                    help="require this access token for the GUI/API (or set CRYO_TOKEN)")
    ap.add_argument("--certfile")
    ap.add_argument("--keyfile")
    args = ap.parse_args()

    App.token, App.outdir = args.token, args.outdir
    os.makedirs(App.outdir, exist_ok=True)
    srv = Server((args.host, args.port), Handler)
    scheme = "http"
    if args.certfile:
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        ctx.load_cert_chain(args.certfile, args.keyfile)
        srv.socket = ctx.wrap_socket(srv.socket, server_side=True)
        scheme = "https"
    if args.host not in ("127.0.0.1", "localhost") and not args.token:
        print("WARNING: listening on %s without --token. Anyone who can reach this port "
              "can start scans using credentials they type in." % args.host, file=sys.stderr)
    if args.host not in ("127.0.0.1", "localhost") and scheme == "http":
        print("WARNING: plain HTTP. Cluster passwords typed in the GUI cross the network "
              "unencrypted. Use --certfile/--keyfile or an SSH tunnel.", file=sys.stderr)
    print("Cryo: %s://%s:%d  (results in %s)" % (scheme, args.host, args.port,
                                                           os.path.abspath(App.outdir)))
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
