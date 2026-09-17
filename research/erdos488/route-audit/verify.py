"""Exact checks for two auxiliary conjectures; NOT counterexamples to Erdos 488.

Only Python's standard library is used. No floating-point decisions, solver
status, expected result file, or downloaded proof is trusted by these checks.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Iterable

BASE = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)
SPARSE = tuple(2 * p for p in BASE) + (227,)
CORE = (2, 3)
TAIL = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def primitive(a: tuple[int, ...]) -> bool:
    return len(a) == len(set(a)) and all(x == y or y % x != 0 for x in a for y in a)


def direct_hits(a: Iterable[int], n: int) -> list[int]:
    a = tuple(a)
    return [x for x in range(1, n + 1) if any(x % g == 0 for g in a)]


def sieve_hits(a: Iterable[int], n: int) -> list[int]:
    flags = bytearray(n + 1)
    for g in a:
        for x in range(g, n + 1, g):
            flags[x] = 1
    return [x for x in range(1, n + 1) if flags[x]]


def avoiding_tail(base: int, tail: tuple[int, ...], n: int, start: int = 0) -> int:
    """Exact alternating inclusion-exclusion, pruned only when lcm > n."""
    total = n // base
    for i in range(start, len(tail)):
        q = math.lcm(base, tail[i])
        if q <= n:
            total -= avoiding_tail(q, tail, n, i + 1)
    return total


def split_direct(n: int) -> list[int]:
    return [x for x in range(1, n + 1)
            if (x % 2 == 0 or x % 3 == 0) and all(x % v != 0 for v in TAIL)]


def split_ie(n: int) -> int:
    return (avoiding_tail(2, TAIL, n) + avoiding_tail(3, TAIL, n)
            - avoiding_tail(6, TAIL, n))


def prime_trial(n: int) -> bool:
    return n >= 2 and all(n % d != 0 for d in range(2, math.isqrt(n) + 1))


def run() -> dict:
    require(primitive(SPARSE), 'Sparse set is not primitive')
    require(math.gcd(*SPARSE) == 1, 'Sparse gcd is not 1')
    h = direct_hits(SPARSE, 228)
    require(h == sieve_hits(SPARSE, 228), 'Independent sparse counts disagree')
    incidence = sum(228 // g for g in SPARSE)
    require((len(h), incidence, len(SPARSE)) == (99, 183, 16), 'Sparse values changed')
    require(2 * len(h) < 228 and incidence + len(SPARSE) > 2 * len(h), 'Not a sparse obstruction')

    require(primitive(CORE + TAIL), 'Core and tail are not primitive')
    require(all(prime_trial(p) for p in CORE + TAIL), 'Primality trial failed')
    require(TAIL == tuple(p for p in range(5, 80) if prime_trial(p)), 'Tail list incomplete')
    n, m = 191, 3158
    hn, hm = split_direct(n), split_direct(m)
    require(len(hn) == split_ie(n) == 25, 'Split n count mismatch')
    require(len(hm) == split_ie(m) == 827, 'Split m count mismatch')
    gap = n * len(hm) - 2 * m * len(hn)
    require(gap == 57, 'Split gap mismatch')
    full_n, full_m = len(direct_hits(CORE + TAIL, n)), len(direct_hits(CORE + TAIL, m))
    require(n * full_m < 2 * m * full_n, 'Do not confuse split and union counts')

    # Regression checks only. The all-d family in proof.md is justified by a
    # mathematical bijection and a coprimality argument, not these samples.
    samples = []
    for d in (2, 3, 4, 5, 7, 10, 31, 100):
        G = tuple(d * p for p in BASE) + (114 * d - 1,)
        N = 114 * d
        H = direct_hits(G, N)
        require(H == sieve_hits(G, N), f'Scale {d}: count mismatch')
        I = sum(N // g for g in G)
        require(primitive(G) and math.gcd(*G) == 1, f'Scale {d}: invalid set')
        require((len(H), I, len(G)) == (99, 183, 16), f'Scale {d}: values mismatch')
        require(2 * len(H) < N and I + len(G) > 2 * len(H), f'Scale {d}: inequality')
        samples.append(dict(d=d, n=N, count=len(H), incidence=I, cardinality=len(G)))

    return {
        'scope': 'Auxiliary Conjectures 6.11 and 4.8 in the cited paper, NOT Erdos 488',
        'sparse': {'G': SPARSE, 'n': 228, 'count': len(h), 'incidence': incidence,
                   'cardinality': len(SPARSE), 'gcd': 1,
                   'density': str(Fraction(len(h), 228)), 'total_order_slack': -1,
                   'covered_integers': h},
        'pair_tail': {'core': CORE, 'tail': TAIL, 'n': n, 'm': m,
                      'split_count_n': len(hn), 'split_count_m': len(hm),
                      'left_cross_product': n * len(hm),
                      'right_cross_product': 2 * m * len(hn), 'reversed_gap': gap,
                      'density_ratio': str(Fraction(n * len(hm), m * len(hn))),
                      'survivors_n': hn, 'survivors_m': hm,
                      'full_union_count_n': full_n, 'full_union_count_m': full_m,
                      'full_union_original_gap': 2 * m * full_n - n * full_m},
        'scale_regression_samples': samples,
        'base': {'P': BASE, 'n': 114, 'count': len(direct_hits(BASE, 114)),
                 'incidence': sum(114 // p for p in BASE), 'cardinality': len(BASE)},
        'limitations': 'Finite ordinary-Python checks; see Lean source and actual CI for kernel checks. '
                       'All-d argument is separate in proof.md. No global priority or prize claim.'
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('results.json'))
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2, ensure_ascii=False) + '\n'
    args.output.write_text(text, encoding='utf-8')
    print(json.dumps({
        'verified': True, 'output': str(args.output),
        'sha256': hashlib.sha256(text.encode()).hexdigest(),
        'sparse_values': [99, 183, 16], 'split_values': [25, 827],
        'pair_tail_reversed_gap': 57, 'original_union_gap': result['pair_tail']['full_union_original_gap'],
        'claim': 'Two auxiliary counterexamples, not a main-problem counterexample'
    }, indent=2))


if __name__ == '__main__':
    main()
