"""Fetch exactly the revisions in the committed Lake manifest; never update pins."""
from __future__ import annotations
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def run(*args: str) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()

def main() -> None:
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
    for package in manifest['packages']:
        name, sha, url = package['name'], package['rev'], package['url']
        if not re.fullmatch(r'[A-Za-z0-9_-]+', name):
            raise ValueError('Unsafe package name')
        if not re.fullmatch(r'[a-f0-9]{40}', sha):
            raise ValueError(f'Non-pinned revision for {name}')
        if not url.startswith('https://github.com/'):
            raise ValueError(f'Unexpected repository URL for {name}')
        path = ROOT / '.lake' / 'packages' / name
        if path.exists() and not (path / '.git').exists():
            if any(path.iterdir()):
                raise RuntimeError(f'Nonempty non-Git directory: {path}')
        if not (path / '.git').exists():
            path.mkdir(parents=True, exist_ok=True)
            run('git', '-C', str(path), 'init')
            run('git', '-C', str(path), 'remote', 'add', 'origin', url)
            run('git', '-C', str(path), 'fetch', '--depth=1', 'origin', sha)
            run('git', '-C', str(path), 'checkout', '--detach', sha)
        actual = run('git', '-C', str(path), 'rev-parse', 'HEAD')
        if actual != sha:
            raise RuntimeError(f'{name}: existing checkout {actual} != pinned {sha}; not overwritten')
        if run('git', '-C', str(path), 'diff', '--name-only', 'HEAD'):
            raise RuntimeError(f'{name}: modified tracked dependency source; not overwritten')
        print(f'PIN_VERIFIED {name} {sha}', flush=True)

if __name__ == '__main__':
    main()
