"""Fail-closed audit of printed theorem dependencies, with two negative controls.

This is a submitter-operated supplementary audit, not independent human review
or the prize operator's designated isolated verification.
"""
from __future__ import annotations
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
TARGETS = [
    'Erdos440Real.mem_realGoodEdges_iff',
    'Erdos440Real.qualifying_indices_finite',
    'Erdos440Real.realCount_eq_ncard',
    'Erdos440Real.realCount_eq_count_floor',
    'Erdos440Real.map_floor_atTop',
    'Erdos440Real.real_limsup_eq_nat',
    'Erdos440Real.real_liminf_eq_nat',
    'Erdos440Real.complete_original_problem',
    'Erdos440Cutoff.strict_cutoff',
    'Erdos440Cutoff.square_threshold',
]

def check_axioms(text: str, names: list[str]) -> dict[str, list[str]]:
    reports: dict[str, list[str]] = {}
    for name in names:
        pattern = re.escape("'" + name + "' depends on axioms:") + r'\s*\[([^\]]*)\]'
        found = re.findall(pattern, text, re.S)
        if len(found) != 1:
            raise ValueError(f'Expected exactly one axiom report for {name}; found {len(found)}')
        axioms = [a.strip() for a in found[0].split(',') if a.strip()]
        unapproved = set(axioms) - ALLOWED
        if unapproved:
            raise ValueError(f'Unapproved axioms for {name}: {sorted(unapproved)}')
        reports[name] = axioms
    return reports

def strip_lean_comments(source: str) -> str:
    out: list[str] = []
    depth, i = 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
            out.append('\n')
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError('Unterminated Lean comment')
    return ''.join(out)

def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit('Usage: python3 audit.py axioms.log')
    reports = check_axioms(Path(sys.argv[1]).read_text(encoding='utf-8'), TARGETS)
    sources = [ROOT / 'Proof.lean', ROOT / 'Cutoff.lean', *sorted((ROOT / 'upstream').rglob('*.lean'))]
    if len(sources) != 7:
        raise ValueError('Expected two new proof files and exactly five pinned upstream files')
    banned = r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b|debug\.skipKernelTC'
    for p in sources:
        if re.search(banned, strip_lean_comments(p.read_text(encoding='utf-8'))):
            raise ValueError(f'Forbidden proof-source token in {p}')
    with tempfile.TemporaryDirectory(prefix='erdos440-audit-') as temporary:
        tmp = Path(temporary)
        wrong = tmp / 'WrongProof.lean'
        wrong.write_text('theorem audit_wrong : False := by\n  exact True.intro\n', encoding='utf-8')
        result = subprocess.run(['lake', 'env', 'lean', str(wrong)], cwd=ROOT,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode == 0 or 'type mismatch' not in result.stdout.lower():
            raise ValueError('Wrong-proof negative control did not fail for a type mismatch')
        print('WRONG_PROOF_REJECTED')
        bad = tmp / 'BadAxiom.lean'
        bad.write_text('axiom audit_unapproved : False\ntheorem audit_bad : False := audit_unapproved\n'
                       '#print axioms audit_bad\n', encoding='utf-8')
        result = subprocess.run(['lake', 'env', 'lean', str(bad)], cwd=ROOT,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode != 0:
            raise ValueError('Bad-axiom control failed to elaborate; audit control is invalid')
        try:
            check_axioms(result.stdout, ['audit_bad'])
        except ValueError as error:
            if 'Unapproved axioms' not in str(error):
                raise
        else:
            raise ValueError('Unapproved-axiom negative control was incorrectly accepted')
        print('UNAPPROVED_AXIOM_REJECTED')
    for malformed in ['', "'Erdos440Real.complete_original_problem' depends on axioms: [sorryAx]"]:
        try:
            check_axioms(malformed, TARGETS)
        except ValueError:
            pass
        else:
            raise ValueError('Missing-report negative control was incorrectly accepted')
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'bootstrap.py', 'audit.py']:
        hashes[name] = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    result = {'status': 'PASS', 'targets': reports, 'sha256': hashes,
              'negative_controls': ['wrong proof rejected', 'unapproved axiom rejected', 'missing report rejected'],
              'scope': 'Submitter-operated kernel-dependency audit; not prize adjudication or independent-operator review.'}
    (ROOT / 'audit-result.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
