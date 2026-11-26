#!/usr/bin/env python3
"""A read-only local Git LOC dashboard. Requires Python 3.9+ and Git."""
import argparse
import collections
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import threading
import time
import urllib.parse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from zoneinfo import ZoneInfo

EXCLUDED = (b'datra-haskell/docs/', b'datra-haskell/src/DatraCore/', b'datra-haskell/test/')
HERE = Path(__file__).resolve().parent

def run(args, timeout=180, check=True):
    result = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    if check and result.returncode:
        # Don't echo Git remote URLs or possible credentials in errors.
        raise RuntimeError('Git could not complete ' + str(args[-1] if args[-1] in ('HEAD', '--show-toplevel') else 'the requested history read') + '.')
    return result

class History:
    def __init__(self, repo, cache, timezone, offline=False, progress=lambda s: None):
        self.repo, self.cache = Path(repo).resolve(), Path(cache).resolve()
        self.timezone, self.offline, self.progress = ZoneInfo(timezone), offline, progress
        self.gitdir = self.cache / 'history.git'
        self.cache.mkdir(parents=True, exist_ok=True)
        if not self.gitdir.exists():
            run(['git', 'init', '--bare', str(self.gitdir)])
        self.g = ['git', '--git-dir=' + str(self.gitdir)]
        self.blobs, self.counts = {}, {}
        self.last_remote_sync = None

    def git(self, *args):
        return run(self.g + list(args)).stdout.decode('utf-8', 'replace').strip()

    def snapshot(self):
        g = ['git', '-C', str(self.repo)]
        head = run(g + ['rev-parse', 'HEAD']).stdout.decode().strip()
        name = run(g + ['symbolic-ref', '--quiet', '--short', 'HEAD'], check=False)
        branch = name.stdout.decode().strip() if not name.returncode else 'Detached HEAD'
        return head, branch

    def build(self, head, branch):
        self.progress('Reading the selected branch')
        # Fetch into an isolated cache. Never change the user's branch, index, or working tree.
        run(self.g + ['fetch', '--quiet', str(self.repo), '+HEAD:refs/heads/dashboard-current'])
        actual = self.git('rev-parse', 'refs/heads/dashboard-current')
        if actual != head:
            raise RuntimeError('The branch changed while reading it. The page will retry automatically.')
        remote = run(['git', '-C', str(self.repo), 'remote', 'get-url', 'origin'], check=False).stdout.decode().strip()
        github = bool(re.match(r'^(?:https?://github\.com/|git@github\.com:|ssh://git@github\.com/)', remote))
        warnings = []
        if github and not self.offline and head != self.last_remote_sync:
            self.progress('Reading original PR commits from GitHub')
            env = dict(os.environ, GIT_TERMINAL_PROMPT='0')
            try:
                result = subprocess.run(self.g + ['fetch', '--quiet', remote, '+refs/pull/*/head:refs/pr/*'], stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120, env=env)
                if result.returncode:
                    warnings.append('PR refresh was unavailable; using any previously cached PR history.')
            except subprocess.TimeoutExpired:
                warnings.append('PR refresh timed out; using any previously cached PR history.')
            self.last_remote_sync = head
        self.progress('Counting implementation lines across commits')
        raw = self.git('log', '--all', '--format=%H%x00%P%x00%aI%x00%cI%x00%s')
        metadata = {}
        for line in raw.splitlines():
            sha, parents, author, committer, subject = line.split('\0', 4)
            metadata[sha] = (parents.split(), author, committer, subject)
        pr_refs = {}
        for line in self.git('for-each-ref', '--format=%(refname) %(objectname)', 'refs/pr/').splitlines():
            ref, sha = line.split()
            pr_refs[ref.rsplit('/', 1)[-1]] = sha
        cat = subprocess.Popen(self.g + ['cat-file', '--batch'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        def loc(sha):
            if sha in self.counts:
                return self.counts[sha]
            total = 0
            entries = run(self.g + ['ls-tree', '-r', '-z', sha, '--', 'datra-haskell']).stdout.split(b'\0')
            for entry in entries:
                if not entry:
                    continue
                info, path = entry.split(b'\t', 1)
                mode, kind, blob = info.split()
                if kind != b'blob' or mode == b'120000' or path.startswith(EXCLUDED):
                    continue
                if blob not in self.blobs:
                    cat.stdin.write(blob + b'\n'); cat.stdin.flush()
                    size = int(cat.stdout.readline().split()[2])
                    data = cat.stdout.read(size); cat.stdout.read(1)
                    self.blobs[blob] = 0 if b'\0' in data else data.count(b'\n') + int(bool(data) and not data.endswith(b'\n'))
                total += self.blobs[blob]
            self.counts[sha] = total
            return total
        def day(stamp):
            return dt.datetime.fromisoformat(stamp.replace('Z', '+00:00')).astimezone(self.timezone).date().isoformat()
        events, ancestors, weights = [], {}, {}
        expanded, original_commits, missing, residuals = [], 0, [], []
        def add(sha, value, direct=False):
            if value:
                events.append((day(metadata[sha][2 if direct else 1]), value))
        try:
            commits = self.git('rev-list', '--topo-order', '--reverse', head).splitlines()
            for index, sha in enumerate(commits):
                parents, author, committer, subject = metadata[sha]
                inherited = set()
                for parent in parents:
                    inherited.update(ancestors[parent]); inherited.add(parent)
                ancestors[sha] = inherited
                weight = loc(sha) - sum(weights[p] for p in inherited)
                weights[sha] = weight
                match = re.search(r'\(#(\d+)\)$', subject)
                number = match.group(1) if match else None
                candidate = bool(number and len(parents) == 1 and (loc(sha) or loc(parents[0])))
                if candidate and number in pr_refs:
                    base, pr_head = parents[0], pr_refs[number]
                    local_commits = self.git('rev-list', '--topo-order', '--reverse', pr_head, '^' + base).splitlines()
                    local, la, lw = set(local_commits), {}, {}
                    for q in local_commits:
                        inherited = set()
                        for parent in metadata[q][0]:
                            if parent in local:
                                inherited.update(la[parent]); inherited.add(parent)
                        la[q] = inherited
                        merge_base = self.git('merge-base', q, base)
                        value = loc(q) - loc(merge_base) - sum(lw[p] for p in inherited)
                        lw[q] = value
                        add(q, value)
                    residual = weight - sum(lw.values())
                    add(sha, residual, direct=True)
                    if residual:
                        residuals.append({'pr': int(number), 'lines': residual})
                    expanded.append(int(number)); original_commits += len(local_commits)
                else:
                    if candidate:
                        missing.append(int(number))
                    add(sha, weight, direct=True)
                if index % 50 == 0:
                    self.progress('Counting commit %d of %d' % (index + 1, len(commits)))
            endpoint = loc(head)
            assert sum(v for _, v in events) == endpoint
        finally:
            cat.stdin.close(); cat.stdout.close(); cat.terminate(); cat.wait()
        if not events:
            raise RuntimeError('No implementation history was found under datra-haskell/ on this branch.')
        daily = collections.Counter()
        for date, value in events:
            daily[date] += value
        start = dt.date.fromisoformat(min(daily))
        today = dt.datetime.now(self.timezone).date()
        end = max(today, dt.date.fromisoformat(max(daily)))
        rows, total = [], 0
        for i in range((end - start).days + 1):
            date = (start + dt.timedelta(days=i)).isoformat()
            delta = daily[date]; total += delta
            net7 = None if i < 6 else sum(row['net_loc'] for row in rows[-6:]) + delta
            rows.append({'date': date, 'total_loc': total, 'net_loc': delta, 'rate': None if net7 is None else net7 / 7, 'net_7d': net7})
        assert rows[-1]['total_loc'] == endpoint
        if min(row['total_loc'] for row in rows) < 0:
            warnings.append('Some reconstructed dates are negative because branch histories overlap. Treat daily attribution cautiously; the final total is exact.')
        if missing:
            warnings.append('Original PR history is missing for ' + ', '.join('#' + str(n) for n in sorted(set(missing))) + '; those changes remain on their recorded merge days.')
        if residuals:
            warnings.append('Some PRs need merge-day reconciliation; see reconstruction details.')
        generated = dt.datetime.now(self.timezone).isoformat(timespec='seconds')
        return {'branch': branch, 'head': head, 'repo': self.repo.name, 'timezone': str(self.timezone), 'rows': rows,
                'total': endpoint, 'peak': max(row['total_loc'] for row in rows), 'rate': rows[-1]['rate'],
                'net_7d': rows[-1]['net_7d'], 'generated_at': generated, 'observed_through': rows[-1]['date'],
                'expanded_prs': len(expanded), 'original_commits': original_commits, 'missing_prs': sorted(set(missing)),
                'reconciliations': residuals, 'warnings': warnings, 'excluded': [s.decode() for s in EXCLUDED]}

class Dashboard:
    def __init__(self, history):
        self.history, self.lock = history, threading.Lock()
        self.data, self.error, self.busy, self.stage, self.key = None, None, False, 'Starting', None
        self.history.progress = self.progress
    def progress(self, text):
        with self.lock: self.stage = text
    def check(self):
        try:
            head, branch = self.history.snapshot()
            key = (head, branch, dt.datetime.now(self.history.timezone).date().isoformat())
        except Exception as error:
            with self.lock: self.error = str(error)
            return
        with self.lock:
            if self.busy or key == self.key: return
            self.busy, self.error = True, None
        def build():
            try:
                result = self.history.build(head, branch)
                with self.lock:
                    self.data, self.key, self.error = result, key, None
            except Exception as error:
                with self.lock: self.error = str(error)
            finally:
                with self.lock: self.busy = False
        threading.Thread(target=build, daemon=True).start()
    def status(self):
        with self.lock:
            return {'busy': self.busy, 'stage': self.stage, 'error': self.error, 'data': self.data}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', default='.', help='Git checkout; defaults to the current directory')
    parser.add_argument('--port', type=int, default=8765)
    parser.add_argument('--timezone', default='America/New_York')
    parser.add_argument('--cache-dir', help='Isolated history cache; defaults to a directory under the system temp directory')
    parser.add_argument('--offline', action='store_true', help='Use local/cached PR history without fetching GitHub')
    args = parser.parse_args()
    repo = Path(run(['git', '-C', str(Path(args.repo).resolve()), 'rev-parse', '--show-toplevel']).stdout.decode().strip())
    token = hashlib.sha256(str(repo).encode()).hexdigest()[:16]
    cache = args.cache_dir or str(Path(tempfile.gettempdir()) / ('datra-loc-' + token))
    dashboard = Dashboard(History(repo, cache, args.timezone, args.offline))
    class Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            path = urllib.parse.urlsplit(self.path).path
            if path == '/api/status':
                body = json.dumps(dashboard.status()).encode(); content = 'application/json'
            elif path in ('/', '/index.html'):
                body = (HERE / 'index.html').read_bytes(); content = 'text/html; charset=utf-8'
            else:
                self.send_error(404); return
            self.send_response(200)
            self.send_header('Content-Type', content)
            self.send_header('Cache-Control', 'no-store')
            self.send_header('X-Content-Type-Options', 'nosniff')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers(); self.wfile.write(body)
        def log_message(self, *_): pass
    server = ThreadingHTTPServer(('127.0.0.1', args.port), Handler)
    def watch():
        while True:
            dashboard.check(); time.sleep(10)
    threading.Thread(target=watch, daemon=True).start()
    print('Datra LOC: http://127.0.0.1:%d' % server.server_port, flush=True)
    print('Watching committed HEAD in ' + str(repo), flush=True)
    try: server.serve_forever()
    except KeyboardInterrupt: pass
    finally: server.server_close()

if __name__ == '__main__':
    main()
