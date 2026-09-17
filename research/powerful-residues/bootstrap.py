"""Prepare the exact dependency lock inherited from the pinned parent project.
No problem-specific proof source is fetched or generated.
"""
import json
import subprocess
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
ROOT = Path(__file__).resolve().parent
LOCK = ROOT / 'lake-manifest.json'
if not LOCK.exists():
    data = json.loads((ROOT.parent.parent / 'lake-manifest.json').read_text())
    data['name'] = 'PowerfulResidues'
    LOCK.write_text(json.dumps(data, indent=2) + '\n')
lock = json.loads(LOCK.read_text())
assert next(p['rev'] for p in lock['packages'] if p['name'] == 'mathlib') == '520045ab14e26149ee970e2e617ca04b09bde5d6'
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
