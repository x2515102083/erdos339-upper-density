"""Fetch pinned dependencies and byte-verify the attributed upstream proof.

The five upstream files are NOT claimed as our original work. See ATTRIBUTION.md.
No theorem is downloaded from a mutable branch, and an existing mismatched file
or checkout is rejected instead of silently replaced.
"""
from __future__ import annotations
import hashlib
import json
import re
import subprocess
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent
UPSTREAM = '8822f7ddef30fadbd92e1c6ab4ed897af356af5e'
FILES = {
    'ErdosProblems/Erdos440.lean': '43b4bc391d4e7036e82b83b89f00a49bbfa4ce52',
    'ErdosProblems/Erdos440/Constant.lean': '30750dce4db722d68b4b60721fa6d4b386b2dbee',
    'ErdosProblems/Erdos440/Liminf.lean': '7b74d34c77b2b58dbea45c0c05552e397a2826c9',
    'ErdosProblems/Erdos440/SharpConstruction.lean': '42f3e4638449689e88756416b97e4cfe3657e7b0',
    'ErdosProblems/Erdos440/SharpUpper.lean': '587e56c019e02e70be6628a2e68134380eaa8cae',
}

def run(*args: str) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()

def main() -> None:
    for relative, expected in FILES.items():
        path = ROOT / 'upstream' / relative
        if not path.exists():
            url = f'https://raw.githubusercontent.com/plby/lean-proofs/{UPSTREAM}/src/latest/{relative}'
            data = urllib.request.urlopen(url, timeout=60).read()
        else:
            data = path.read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if actual != expected:
            raise RuntimeError(f'Upstream hash mismatch: {relative}: {actual}')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        print('UPSTREAM_VERIFIED', relative, actual, flush=True)
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    for p in manifest['packages']:
        name, sha, url = p['name'], p['rev'], p['url']
        if not re.fullmatch(r'[A-Za-z0-9_-]+', name) or not re.fullmatch(r'[0-9a-f]{40}', sha):
            raise ValueError('Unsafe name or unpinned revision')
        if not url.startswith('https://github.com/'):
            raise ValueError('Unexpected dependency host')
        path = ROOT / '.lake' / 'packages' / name
        if not (path / '.git').exists():
            path.mkdir(parents=True, exist_ok=True)
            if any(path.iterdir()):
                raise RuntimeError(f'Nonempty non-Git dependency directory: {path}')
            run('git', '-C', str(path), 'init')
            run('git', '-C', str(path), 'remote', 'add', 'origin', url)
            run('git', '-C', str(path), 'fetch', '--depth=1', 'origin', sha)
            run('git', '-C', str(path), 'checkout', '--detach', sha)
        if run('git', '-C', str(path), 'rev-parse', 'HEAD') != sha:
            raise RuntimeError(f'Dependency revision mismatch: {name}')
        if run('git', '-C', str(path), 'diff', '--name-only', 'HEAD'):
            raise RuntimeError(f'Modified dependency source: {name}')
        print('DEPENDENCY_VERIFIED', name, sha, flush=True)

if __name__ == '__main__':
    main()
