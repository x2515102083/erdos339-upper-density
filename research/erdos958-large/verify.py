"""Strictly compile the committed sources and audit their printed axiom closures.

Run after `python3 bootstrap.py` and `lake exe cache get`. Standard-library only.
No proof source is generated, patched, or downloaded by this verifier.
"""
from __future__ import annotations
import hashlib
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCES = ('Geometry.lean', 'Counting.lean', 'Complete.lean')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
REQUIRED = {
    'Erdos958Large.arc_injOn',
    'Erdos958Large.no_common_circle',
    'Erdos958Large.no_common_line',
    'Erdos958Large.ArcConfig.card_points',
    'Erdos958Large.ArcConfig.card_distances',
    'Erdos958Large.ArcConfig.multiplicity_image',
    'Erdos958Large.counterexample_every_n',
    'Erdos958Large.not_eventual_classification',
    'Erdos958.erdos_958',
}

def run(*args: str) -> str:
    result = subprocess.run(args, cwd=ROOT, text=True, encoding='utf-8',
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end='', flush=True)
    if result.returncode:
        raise RuntimeError(f'Command failed ({result.returncode}): {args}')
    return result.stdout

def without_comments(source: str) -> str:
    """Remove nested Lean block comments and line comments, preserving newlines."""
    result: list[str] = []
    i = depth = 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            result.append(' ')
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            result.append(' ')
            i += 2
        elif depth:
            if source[i] == '\n':
                result.append('\n')
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            result.append(source[i])
            i += 1
    if depth:
        raise ValueError('Unterminated Lean comment')
    return ''.join(result)

def main() -> None:
    version = run('lean', '--version')
    if 'version 4.32.1,' not in version or 'f054605aea4b840552cca2e725580bffd1e1b704' not in version:
        raise RuntimeError('Wrong Lean release; use the committed lean-toolchain')
    run('python3', 'bootstrap.py')
    forbidden = re.compile(r'\b(sorry|admit|axiom|native_decide|ofReduceBool|implemented_by|unsafe)\b')
    for name in SOURCES:
        source = (ROOT / name).read_text(encoding='utf-8')
        hit = forbidden.search(without_comments(source))
        if hit:
            raise RuntimeError(f'Forbidden proof construct in {name}: {hit.group(0)}')
        digest = hashlib.sha256(source.encode('utf-8')).hexdigest()
        print(f'SOURCE_SHA256 {name} {digest}', flush=True)
    build = ROOT / '.lake' / 'build' / 'lib' / 'lean'
    build.mkdir(parents=True, exist_ok=True)
    logs: list[str] = []
    for name in SOURCES:
        target = build / (Path(name).stem + '.olean')
        if target.exists():
            target.unlink()
        logs.append(run('lake', 'env', 'lean', '-DwarningAsError=true', '-o', str(target), name))
    text = '\n'.join(logs)
    (ROOT / 'verification.log').write_text(text, encoding='utf-8')
    found: set[str] = set()
    for name, raw in re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", text):
        axioms = {a.strip() for a in raw.split(',') if a.strip()}
        if not axioms <= ALLOWED:
            raise RuntimeError(f'Unexpected axioms for {name}: {axioms - ALLOWED}')
        found.add(name)
    if not REQUIRED <= found:
        raise RuntimeError(f'Missing axiom audit outputs: {REQUIRED - found}')
    print('VERIFIED: all three source files compile with warnings as errors;', flush=True)
    print('VERIFIED: all nine required axiom closures contain only standard Lean axioms.', flush=True)
    print('The checked endpoint covers every n >= 4 and refutes the original eventual statement.', flush=True)
    print('Verification does not determine prize eligibility, priority, or payment.', flush=True)

if __name__ == '__main__':
    main()
