# Erdos 488 / JSP-000395: rounded reformulation and an all-scale subfamily

**Research only: not a complete solution, not a prize submission.**
The finite enumeration is exact Python, not Lean kernel verification. The Lean
package proves a reformulation only; consult the actual workflow result for its
build status. No novelty, first priority, independent human review, recipient
confirmation, or award entitlement is asserted.

## Exact target and equivalent rounded inequality

For a nonempty finite set A of integers at least 2, let
`F_A(t) = #{1 <= x <= t : some a in A divides x}`. The original conjecture is

```
n F_A(m) < 2m F_A(n)                 (m > n >= max(A)).       [S]
```

The universal conjecture [S] is equivalent to

```
(n+1) F_A(m) <= 2m F_A(n)             (m > n >= max(A)).       [R]
```

[R] implies [S] because F_A(m)>0. Conversely, suppose [R] fails and write
`s=(n+1)F_A(m)-2mF_A(n)>=1`, `u=F_A(m)>0`. Set `d=ceil(u/s)`,
`A'=dA`, `N=d(n+1)-1`, and `M=dm`. Dividing covered integers by d is a bijection,
so `F_(dA)(t)=F_A(floor(t/d))`. Hence `M>N>=max(A')`, the two relevant counts
are unchanged, and

```
N F_A'(M) - 2M F_A'(N) = ds-u >= 0.
```

This is a counterexample to the original strict inequality. The simpler choice
`d=u` always works and is the one used by the Lean lifting theorem. This is a
finite argument, not a limiting heuristic. It does **not** prove either conjecture.

The formal count is literally a filtered `Finset.Icc 1 t`. The dilation identity
is proved in the Lean source, not supplied as an extra assumption.

## Fixed shapes imply every common dilation

Assume [R] for a fixed A and every legal n,m. Given `M>N>=d max(A)`, put
`j=floor(M/d)`, `k=floor(N/d)`. If j=k the positive counts agree and [S] is
immediate. If j>k, use `N<d(k+1)` and `dj<=M` to get

```
N F_A(j) < d(k+1)F_A(j) <= 2dj F_A(k) <= 2M F_A(k).
```

Thus [S] holds for every positive integer dilation d, without upper bounds on
d,N,M.

## Finite certificates for all n and m

Remove generators divisible by smaller ones. Enumerating the resulting
nonempty divisibility antichains suffices. Group inclusion-exclusion by subset
least common multiples:

```
F_A(x) = sum_q c_q floor(x/q)
delta = sum_q c_q/q > 0
W+ = sum_(c_q>0) c_q
W- = sum_(c_q<0) (-c_q).
```

For every positive x,

```
delta*x-W+ < F_A(x) <= delta*x+W-.
```

The lower bound is strict: at least one positive coefficient occurs, and every
fractional part is strictly less than one. Define

```
N0 = max(max(A), ceil(1+(2W+ + W-)/delta)).
```

For all n>=N0 and m>n,

```
2F_A(n) - (n+1)F_A(m)/m
  > delta*(n-1)-2W+ - ((n+1)/m)W-
  >= delta*(n-1)-2W+ - W-
  >= 0.
```

This proves [R] throughout the infinite large-n region. For the remaining n,
compute `rho=min_(max(A)<=n<N0) 2F_A(n)/(n+1)` and `gap=rho-delta`.
If gap>0, take `T=max(1,ceil(W-/gap))`. For m>=T,

```
F_A(m)/m <= delta+W-/m <= rho <= 2F_A(n)/(n+1).
```

Only `max(A)<=n<N0`, `n<m<T` remain for finite checking. The case gap=0,W-=0
is covered directly by the upper bound. Other nonpositive gaps are reported
as failure of the certificate method, not accepted. An empty finite n interval
needs no check, since the large-n result already applies.

The producer checks suffix maxima of F_A(m)/m. The independent consumer uses
prefix minima of 2F_A(n)/(n+1). This optimization covers all remaining pairs;
it does not reduce the mathematical domain.

## Actual completed local results

For **every nonempty A subset {2,...,20}**, all certificates passed. Consequently
[R] holds for all legal n,m, and [S] holds for all common positive integer
multiples of every such A. In contrast with the earlier result, n is no longer
bounded by 20. The remaining restriction is the generator shape.

- 10,239 nonempty primitive generator sets.
- 660,619 producer suffix-maximum comparisons.
- 2,118,650 direct count / inclusion-exclusion comparisons.
- Maximum N0: 1,488; maximum T: 540, both attained at A={11,...,20}.
- Additional direct tests: 458,059 rounded pairs and 157,964 dilation counts.
- The separate consumer screened all 524,287 nonempty subsets, recovered the
  same antichains, and passed 663,031 prefix-minimum comparisons plus
  2,118,650 independently reconstructed counts. It imports no producer code.

Certificate SHA-256:

```
254c1f5513c540341bf8abc55d31f1bcd5f6602c6c1403eb839af36d6075be98
```

From this directory, with standard Python and no third-party packages:

```sh
python3 all_scales_check.py --n-max 20 --self-test
python3 independent_verify.py all-scales-n20-certificates.jsonl 20
```

Do not use `-O` or `PYTHONOPTIMIZE`; the scripts reject assertion-disabled mode.
The separate implementations are not independent human review or independent
implementations of the Python arithmetic runtime.

### Gcd-normalized interpretation

Let P be the primitive reduction. The result covers `max(P)/gcd(P)<=20`, with
the normalized singleton {1} handled by the elementary singleton argument:
if `q=floor(n/a)>=1`, then `n+1<=a(q+1)<=2aq`, yielding [R] for A={a}.
A normalized primitive set containing 1 can only be {1}.
This is not a theorem for arbitrary sets with at most ten primitive generators.
No pairwise-coprime hypothesis is imposed.

## Search beyond the certified class

A separate mixed-integer search targeted strict violations of [R] and required
an exact integer recheck before accepting any witness. It ran 78 selected n,m
pairs, with n from 25 to 400 and m up to 2,000: 69 solver-infeasible outcomes,
9 time limits, and no exact counterexample. These are diagnostics, not formal
infeasibility certificates and not exhaustive coverage of those parameter ranges.
Equality is allowed in [R], but would violate [S].

## Prior work and attribution

Statement: [Formal Conjectures, pinned version](https://github.com/google-deepmind/formal-conjectures/blob/cbee53b0ccb3bacf2d9e9b2bf2eea493a373b22c/FormalConjectures/ErdosProblems/488.lean).
The statement file is not a complete proof.

The signed lcm tail framework is already recorded in Przemyslaw Chojecki,
[Signed Transport, Pair-Tail Reduction, and Low Layers in an Erdos Density-Doubling Problem](https://www.ulam.ai/research/erdos488.pdf), 20 March 2026,
Proposition 2.4 and Corollary 2.5. The extra unit in N0 here accounts for n+1.
We do not claim discovery of that tail method or verification of the paper's
other claims.

The [candidate four-generator argument](https://github.com/dicnunz/erdos488-four-generators)
was inspected for overlap. It covers unbounded primitive generators of cardinality
at most four; its code and finite quotient checks are not imported here. That
result and this bounded-normalized-shape result have different scopes. The
pairwise-coprime five-generator submission is [awards PR #192](https://github.com/TheJustinSunPrize/awards/pull/192).

Prepared for public account x2515102083 with ChatGPT assistance. The full problem
still requires arbitrary normalized generator shapes or an exact counterexample.
No official catalog, eligibility, claim, candidate, recipient, award, or PR #681
field is changed by this research branch.
