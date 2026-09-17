"""Restore the committed dependency revisions; fetch no problem-specific proof.
Run from a checkout of the proof project. This script changes only .lake.
"""
import json
import subprocess
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
ROOT = Path(__file__).resolve().parent
LOCK = ROOT / 'lake-manifest.json'
lock = json.loads(LOCK.read_text(encoding='utf-8'))
if next(p['rev'] for p in lock['packages'] if p['name'] == 'mathlib') != '520045ab14e26149ee970e2e617ca04b09bde5d6':
    raise RuntimeError('Unexpected Mathlib lock revision')
def run(args, cwd):
    subprocess.run(args, cwd=cwd, check=True)
def prepare(p):
    folder = ROOT / '.lake' / 'packages' / p['name']
    folder.mkdir(parents=True, exist_ok=True)
    if not (folder / '.git').exists():
        run(['git', 'init'], folder)
        run(['git', 'remote', 'add', 'origin', p['url']], folder)
    current = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=folder, text=True, capture_output=True)
    if current.returncode or current.stdout.strip() != p['rev']:
        run(['git', 'fetch', '--depth=1', 'origin', p['rev']], folder)
        run(['git', 'checkout', '--detach', p['rev']], folder)
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=folder, text=True).strip()
    if actual != p['rev']:
        raise RuntimeError('Dependency mismatch: ' + p['name'])
    print('PINNED', p['name'], actual, flush=True)
with ThreadPoolExecutor(max_workers=3) as pool:
    list(pool.map(prepare, lock['packages']))
