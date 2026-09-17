"""Exact computational research for Erdos 488 / JSP-000395.

For 2 <= n <= N, verify the conjectured inequality for every m > n.
This is NOT a proof for unbounded n, NOT a Lean verification, and NOT a
prize submission. Arithmetic is exact; see README.md for the reduction.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import time
from fractions import Fraction
from math import lcm
from pathlib import Path


def coverage(A, upper):
    flags = bytearray(upper + 1)
    for a in A:
        for t in range(a, upper + 1, a):
            flags[t] = 1
    C = [0] * (upper + 1)
    for t in range(1, upper + 1):
        C[t] = C[t - 1] + flags[t]
    return C


def primitive(A):
    result = []
    for a in sorted(set(A)):
        if not any(a % b == 0 for b in result):
            result.append(a)
    return tuple(result)


def families(N, A=(), remaining=None):
    if remaining is None:
        remaining = tuple(range(2, N + 1))
    if A:
        yield A
    for i, a in enumerate(remaining):
        yield from families(N, A + (a,),
                            tuple(b for b in remaining[i + 1:] if b % a))


def coefficients(A):
    c = {}
    for a in A:
        new = c.copy()
        new[a] = new.get(a, 0) + 1
        for q, v in c.items():
            r = lcm(q, a)
            new[r] = new.get(r, 0) - v
        c = {q: v for q, v in new.items() if v}
    return c


def self_test():
    from itertools import combinations
    for N in range(2, 15):
        expected = set()
        for mask in range(1, 1 << (N - 1)):
            A = [a for a in range(2, N + 1) if mask & (1 << (a - 2))]
            expected.add(primitive(A))
        actual = list(families(N))
        assert len(actual) == len(set(actual))
        assert set(actual) == expected
    for A in families(12):
        direct = {}
        for k in range(1, len(A) + 1):
            for S in combinations(A, k):
                q = lcm(*S)
                direct[q] = direct.get(q, 0) + (1 if k % 2 else -1)
        assert coefficients(A) == {q: v for q, v in direct.items() if v}
        C = coverage(A, 64)
        for m in range(1, 65):
            assert C[m] == sum(any(t % a == 0 for a in A)
                               for t in range(1, m + 1))
    print('SELF_TESTS_PASSED: independent powerset, antichain and direct-count checks')


def check(N):
    if not 2 <= N <= 26:
        raise ValueError('Require 2 <= N <= 26')
    start = time.monotonic()
    count = finite_checks = identity_checks = max_tail = 0
    largest = None
    min_delta = None
    digest = hashlib.sha256()
    for A in families(N):
        c = coefficients(A)
        d = sum((Fraction(v, q) for q, v in c.items()), Fraction())
        E = sum(-v for v in c.values() if v < 0)
        small = coverage(A, N)
        rho = min(Fraction(2 * small[n], n) for n in range(A[-1], N + 1))
        delta = rho - d
        if delta <= 0:
            raise RuntimeError(f'Tail proof unavailable for A={A}: delta={delta}')
        T = E // delta + 1
        upper = max(T - 1, 2 * N)
        C = coverage(A, upper)
        for m in range(1, upper + 1):
            assert sum(v * (m // q) for q, v in c.items()) == C[m]
            assert Fraction(C[m]) <= m * d + E
            identity_checks += 1
        for n in range(A[-1], N + 1):
            for m in range(n + 1, T):
                finite_checks += 1
                if not n * C[m] < 2 * m * C[n]:
                    raise RuntimeError(f'Exact counterexample: A={A}, n={n}, m={m}')
        assert T * delta > E
        count += 1
        if T > max_tail:
            max_tail = T
            largest = dict(A=A, cutoff=T, density=str(d), error_bound=E,
                           rho=str(rho), delta=str(delta))
        min_delta = delta if min_delta is None else min(min_delta, delta)
        digest.update(json.dumps([A, sorted(c.items()), str(d), E, str(rho), T],
                                 separators=(',', ':')).encode() + b'\n')
    return dict(kind='bounded_n_all_m_verified_by_exact_python', n_max=N,
                m_scope='ALL integers m > n; no upper bound on m',
                nonempty_primitive_generator_sets=count,
                finite_A_n_m_inequality_checks=finite_checks,
                independent_direct_vs_inclusion_exclusion_checks=identity_checks,
                maximum_required_tail_start=max_tail, largest_tail_case=largest,
                minimum_delta=str(min_delta),
                certificate_stream_sha256=digest.hexdigest(),
                seconds=round(time.monotonic() - start, 3),
                limitations='Bounded n only. Not Lean-checked, not a complete solution, no novelty or award claim.')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--n-max', type=int, default=20)
    p.add_argument('--output', type=Path)
    p.add_argument('--self-test', action='store_true')
    args = p.parse_args()
    if args.self_test:
        self_test()
    result = check(args.n_max)
    text = json.dumps(result, indent=2)
    print(text)
    if args.output:
        args.output.write_text(text + '\n', encoding='utf-8')


if __name__ == '__main__':
    main()
