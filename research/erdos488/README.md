# Erdős 488 / JSP-000395: bounded-n research

**Not a complete solution, not a Lean proof and not a prize submission.**
The current result concerns every `n <= 20` and **all** integers `m > n`.
The unbounded-n problem remains unresolved in this work. No mathematical
novelty, first priority, independent referee review or award entitlement is
asserted. This isolated research branch does not modify PR #681.

## Original target and prior work

Let A be a nonempty finite subset of the integers at least 2, and let
`C_A(t) = #{1 <= k <= t : some a in A divides k}`. The target asks whether

```
n * C_A(m) < 2 * m * C_A(n)
```

always holds for `m > n >= max(A)`.

Statement source: [Formal Conjectures, pinned version](https://github.com/google-deepmind/formal-conjectures/blob/cbee53b0ccb3bacf2d9e9b2bf2eea493a373b22c/FormalConjectures/ErdosProblems/488.lean).
Original discussion: https://www.erdosproblems.com/488 .
The Formal Conjectures file is a statement with proof holes, not a proof.
The nonempty and minimum-generator conditions are intentional.

[Existing PR #192](https://github.com/TheJustinSunPrize/awards/pull/192)
proves a restricted five-generator pairwise-coprime theorem. That work is
acknowledged and is not claimed as our contribution. The selected
[plby entry](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/ErdosProblems/Erdos488b.md)
is explicitly about a former statement, not evidence that this full target
has been proved. A search is not a global priority certification.

This implementation was prepared for public account x2515102083 with
ChatGPT assistance. It does not import or copy either proof. Research
software and mathematical exposition are distinct from confirmed recipient
identity; no recipient or award record is created.

## Why the m range is unbounded

First remove each generator divisible by another generator. The resulting
nonempty divisibility antichain P generates exactly the same set of
multiples, and `max(P) <= max(A)`. It suffices to enumerate the antichains.
The recursion in `families` chooses elements in increasing order and removes
all future multiples of a chosen element. Each antichain is produced exactly
once; no other families are produced.

For a fixed P, aggregate inclusion-exclusion over subset least common
multiples, obtaining finitely many integers c_q with

```
C_P(m) = sum_q c_q * floor(m/q).
d = sum_q c_q/q.
E = sum_{c_q < 0} (-c_q).
```

The union update is `old + 1_a - old*1_a`, with intersections represented by
least common multiples. This proves the recurrence in `coefficients`.
For every positive integer m, positive-coefficient terms use
`floor(m/q) <= m/q`; negative-coefficient terms use
`floor(m/q) >= m/q - 1`. Consequently

```
C_P(m) <= m*d + E                       (all m).
```

Fix the finite n bound N. Compute exactly

```
rho = min_{max(P) <= n <= N} 2*C_P(n)/n,
delta = rho - d.
```

Whenever delta is positive, set `T = floor(E/delta)+1`. For every m >= T,
`m*delta > E`, so

```
C_P(m) <= m*d + E < m*rho <= 2*m*C_P(n)/n.
```

Thus all m >= T are covered by the inequality, not by finite experimentation.
For each legal n, the remaining n < m < T are checked with exact integer
arithmetic and independently computed divisibility counts. Failure of
`delta > 0` is explicitly reported as failure of this proof method, not
silently treated as a successful check.

## Observed local verification

The N=20 calculation completed using standard-library Python. It enumerated
10,239 nonempty primitive generator sets, checked 999,461 remaining triples,
and made 706,180 comparisons between direct counting and inclusion-exclusion.
Every delta was positive; the smallest was 1/190. The largest required tail
start was 407. Hence the computation plus the reduction above covers all
m > n for every legal A and n <= 20, with no upper bound on m.

The certificate stream SHA-256 is
`7bb8a41789e7661da6a358547f6fad5db2182ceb0c13553a69753b58d12a7810`.
A separate local all-subsets search over n <= 20 and m <= 256 covered 524,287
nonempty generator subsets and 248,507,345 logical triples; its largest ratio
was 19/10, attained by A={10}, n=19, m=20. Six local regression tests passed,
including comparisons with direct subset enumeration and direct divisibility.

Reproduce the compact published checker, including its own independent
self-tests:

```sh
python3 research/erdos488/check.py --n-max 20 --self-test --output result.json
```

No third-party Python dependency is needed. The larger CLI cap is merely a
software guard; a result for a larger N is not claimed without an actual run.

## Boundary of this result

The computation is ordinary exact Python, **not Lean kernel verification**.
Its finite enumeration and implementation remain part of the computational
trust assumptions. Tests and hosted reproduction do not replace formal
verification. The reduction is elementary; novelty is not asserted.

The universal theorem still needs a proof for arbitrary n, or a concrete
exactly verified counterexample. This bounded-n result cannot be submitted as
a complete solution under the current prize contribution rules. No official
catalog, eligibility, claim, candidate, recipient or award field is changed.
