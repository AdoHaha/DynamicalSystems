#!/usr/bin/env python3
"""Bounded, branch-local Lean checking session for the BM544 continuation.

The runner only reads source commits; it cannot push source changes. Each
explicit JSON request is compiled at a recorded commit and reported using the
GitHub Checks API. There is no arbitrary shell command field in the request.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import time
import urllib.request

ROOT = Path.cwd()
REPO = os.environ['GITHUB_REPOSITORY']
BRANCH = 'remaining-optimal-control-r4c-worker'
REQUEST = ROOT / 'scripts/bm544_ci_request.json'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def command(args: list[str], timeout: int = 1200) -> tuple[int, str]:
    try:
        result = subprocess.run(args, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=timeout)
        return result.returncode, result.stdout
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or b''
        if isinstance(output, bytes):
            output = output.decode(errors='replace')
        return 124, output + '\nCompilation timeout.\n'


def report(sha: str, code: int, text: str) -> None:
    payload = {'name': 'BM544 incremental Lean audit', 'head_sha': sha,
               'status': 'completed',
               'conclusion': 'success' if code == 0 else 'failure',
               'output': {'title': 'Lean checks passed' if code == 0 else 'Lean diagnostics',
                          'summary': 'Exact source commit: `' + sha + '`.',
                          'text': '```text\n' + text[-58000:] + '\n```'}}
    request = urllib.request.Request(
        f'https://api.github.com/repos/{REPO}/check-runs',
        data=json.dumps(payload).encode(), method='POST',
        headers={'Authorization': 'Bearer ' + os.environ['GH_TOKEN'],
                 'Accept': 'application/vnd.github+json',
                 'Content-Type': 'application/json',
                 'X-GitHub-Api-Version': '2022-11-28'})
    with urllib.request.urlopen(request, timeout=60) as response:
        result = json.load(response)
    print(f"Reported {sha}: {code}; check {result['id']}", flush=True)


def run_request(request: dict) -> tuple[int, str]:
    log = []
    code, output = command(['lean', '--version'])
    log.append(output)
    targets = request.get('targets', [])
    if any(not re.fullmatch(r'DynamicalSystems(?:Test)?(?:\.[A-Za-z0-9_]+)+', s)
           for s in targets):
        return 2, 'Invalid module name in request.'
    if targets:
        code, output = command(['lake', 'build', *targets])
        log.append(output)
        if code:
            return code, '\n'.join(log)
    for filename in request.get('files', []):
        path = (ROOT / filename).resolve()
        if ROOT not in path.parents or path.suffix != '.lean':
            return 2, 'Invalid Lean source path in request.'
        code, output = command(['lake', 'env', 'lean', '-DwarningAsError=true', str(path)])
        log.append(filename + '\n' + output)
        if code:
            return code, '\n'.join(log)
    names = request.get('axioms', [])
    if names:
        if any(not re.fullmatch(r'[A-Za-z0-9_.]+', name) for name in names):
            return 2, 'Invalid declaration name in request.'
        audit = ROOT / 'BM544SessionAudit.lean'
        audit.write_text(''.join('import ' + m + '\n' for m in targets)
                         + ''.join('#print axioms ' + n + '\n' for n in names))
        code, output = command(['lake', 'env', 'lean', str(audit)])
        log.append(output)
        if code:
            return code, '\n'.join(log)
        records = re.findall(r'depends on axioms:\s*\[([^]]*)\]', output)
        if len(records) != len(names):
            return 3, '\n'.join(log) + '\nMissing audit records.'
        for record in records:
            if not {x.strip() for x in record.split(',') if x.strip()} <= ALLOWED:
                return 3, '\n'.join(log) + '\nUnexpected proof dependency.'
    if request.get('campaign_check', False):
        code, output = command(['bash', 'scripts/check_remaining_optimal_control.sh'], 2400)
        log.append(output)
        if code:
            return code, '\n'.join(log)
    return 0, '\n'.join(log)


def main() -> None:
    started = changed = time.monotonic()
    previous = None
    while time.monotonic() - started < 6600 and time.monotonic() - changed < 900:
        code, output = command(['git', 'fetch', '--quiet', 'origin', BRANCH], 120)
        if code:
            raise RuntimeError(output)
        sha = subprocess.check_output(['git', 'rev-parse', 'FETCH_HEAD'], text=True).strip()
        code, output = command(['git', 'reset', '--hard', sha], 120)
        if code:
            raise RuntimeError(output)
        if REQUEST.exists():
            raw = REQUEST.read_text()
            if raw != previous:
                previous = raw
                changed = time.monotonic()
                request = json.loads(raw)
                code, output = run_request(request)
                report(sha, code, output)
                if request.get('stop', False):
                    raise SystemExit(code)
        time.sleep(5)
    print('Bounded checking session ended.', flush=True)


if __name__ == '__main__':
    main()
