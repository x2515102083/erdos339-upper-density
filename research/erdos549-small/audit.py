"""Require all complete-proof axiom reports; reject missing or additional axioms."""
from __future__ import annotations
import json
import re
import sys
from pathlib import Path

ROOTS = {
    'Erdos549Small.' + s for s in (
        'tree_isTree', 'blue_union_bound', 'blue_degree', 'red_degree',
        'no_monochromatic_copy', 'ramsey_ne_35', 'not_erdos_549',
        'explicit_counterexample')
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit('Usage: python3 audit.py axioms.log')
    text = Path(sys.argv[1]).read_text(encoding='utf-8-sig')
    reports = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text))
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        reports[name] = ''
    if set(reports) != ROOTS:
        raise SystemExit(f'Missing or unexpected theorem reports: {set(reports) ^ ROOTS}')
    result = {}
    for name, report in reports.items():
        used = {a.strip() for a in report.split(',') if a.strip()}
        if not used <= ALLOWED:
            raise SystemExit(f'Unexpected axioms for {name}: {used - ALLOWED}')
        result[name] = sorted(used)
    print(json.dumps(result, indent=2, sort_keys=True))
    print('COMPLETE_ORIGINAL_NEGATION_AXIOM_AUDIT_PASSED')

if __name__ == '__main__':
    main()
