# Two auxiliary counterexamples in the Erdős 488 research route

**Scope:** this note refutes two auxiliary conjectures in the cited paper. It does
not solve or refute Erdős Problem 488 / JSP-000395. No mathematical priority,
independent human review, prize eligibility, or award entitlement is asserted.
Prepared for the public account x2515102083 with ChatGPT assistance.

## Source and statement correspondence

P. Chojecki, *Signed Transport, Pair–Tail Reduction, and Low Layers in an Erdős
Density-Doubling Problem*, PDF dated 20 March 2026, retrieved during this research:
https://www.ulam.ai/research/erdos488.pdf .

The exact targets are Conjecture 6.11 (printed page 17), using the sparse condition
(9) on page 15, and Conjecture 4.8 (printed page 10). The statements and surrounding
definitions were read directly, including visual inspection of pages 10 and 17.
The PDF can change at that URL; the date, conjecture numbers, formulas below and
page numbers specify the version being discussed. No claim is made about later
revisions or about every theorem in the paper.

For finite G of positive integers, define

    F_G(t) = #{x in {1,...,t}: some g in G divides x},
    I_G(t) = sum_{g in G} floor(t/g).

A set is primitive when no two distinct elements divide one another. The main
Erdős problem is the strict inequality n F_G(m) < 2m F_G(n), for all admissible
m > n >= max(G). The two conjectures below are proposed sufficient routes to
that main problem, not equivalent versions of it.

## 1. Counterexample to sparse order-slack (Conjecture 6.11)

The conjecture requires, for every primitive G and n >= max(G) with 2F_G(n) < n,
that some ordering of G have nonnegative total order-slack. This is exactly

    I_G(n) + |G| <= 2F_G(n).

Indeed, in any ordering g_1,...,g_r, let nu_i=floor(n/g_i) and let tau_i count the
multiples of g_i first encountered at index i. First-coverage classes partition
the union of multiples, so sum tau_i=F_G(n), whereas sum nu_i=I_G(n). Therefore

    sum_i (2tau_i-nu_i-1) = 2F_G(n)-I_G(n)-r,

which is independent of the ordering. This is also the paper's identity (13).
Thus changing the ordering cannot repair a negative total.

Take

    G = {4,6,10,14,22,26,34,38,46,58,62,74,82,86,94,227},
    n = 228.

This is a nonempty primitive set of 16 integers at least 2, with maximum 227 and
gcd 1. Direct counting and a separate sieve give

    F_G(228)=99,    I_G(228)=183,    |G|=16.

Consequently 2F_G(228)=198<228, but I_G(228)+|G|=199>198. The total order-slack is
-1 in every ordering. This refutes the conjecture with all stated conditions
satisfied. The gcd-one condition additionally excludes common-scale artifacts.

The finite structure, counts and resulting negation are formalized in
`lean/RouteAudit.lean` as `sparse_structure`, `sparse_values` and
`not_sparse_order_slack`. The displayed first-coverage correspondence is a
mathematical argument in this note; it is not separately formalized in that file.

## 2. An infinite, arbitrarily sparse, gcd-one obstruction family

This section is a mathematical deduction, not an all-parameter Lean theorem in
this package. The included Python samples are regression checks, not its proof.

Let P={2,3,5,7,11,13,17,19,23,29,31,37,41,43,47}. For every integer d>=2 put

    q_d = 114d-1,
    G_d = {dp: p in P} union {q_d},
    N_d = 114d.

The scaled primes form a primitive 15-element set. Since q_d>47d and q_d is
coprime to d, it is distinct from these elements and has no divisibility relation
with them. As 2d and 3d are members, the gcd of the scaled set is d; adjoining
q_d gives gcd(G_d)=gcd(d,114d-1)=1.

The finite base counts are F_P(114)=98 and I_P(114)=182. For the first count,
every composite at most 114 has a prime divisor at most sqrt(114)<11; the only
missed numbers are 1 and the 15 primes in (47,114]. Alternatively, both base
counts are directly checked by `verify.py`.

Multiplication by d bijects the covered integers for P up to 114 with those
for dP up to N_d. The only positive multiple of q_d up to N_d is q_d itself,
and it is not divisible by d. It therefore contributes exactly one new point
and one incidence. For every d>=2,

    F_Gd(N_d)=99,    I_Gd(N_d)=183,    |G_d|=16,
    2F_Gd(N_d)-I_Gd(N_d)-16 = -1.

The density is 99/(114d), tending to zero. Hence no fixed strengthening of the
sparse cutoff to a smaller positive density threshold rescues this auxiliary
conjecture. Neither does requiring gcd 1.

For clarity, the main Erdős inequality actually holds for this entire family,
for every m>n>=q_d. The union is contained in dN union q_d N, so

    F_Gd(m) <= (1/d+1/q_d)m <= (114/113)m/d,

because q_d>=113d. On the other hand it contains the multiples of 2d or 3d,
which contribute four integers per complete block of length 6d. Thus

    F_Gd(n) >= 4 floor(n/(6d)) > 2n/(3d)-4.

Since n/d>=113,

    2F_Gd(n) - n F_Gd(m)/m
      > (4/3-114/113)n/d - 8
      >= (110/339)*113 - 8 = 86/3 > 0.

This is again an unformalized mathematical deduction included to separate the
auxiliary obstruction from a purported counterexample to the main problem.

## 3. Counterexample to pair-vs-tail split doubling (Conjecture 4.8)

For a core U and forbidden tail V, let

    S(t)=#{1<=x<=t: (some u in U divides x) and no v in V divides x}.

Use U={2,3} and

    V={5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79},
    n=191, m=3158.

All generators in U union V are distinct primes. In particular the full set is
primitive and pairwise coprime, 2<3<min(V), and m>n>=max(U union V)=79.

The exact counts are S(191)=25 and S(3158)=827. The 25 smaller survivors are

    2,3,4,6,8,9,12,16,18,24,27,32,36,48,54,64,72,81,96,108,128,144,
    162,166,178.

The full 827-element list is in `results.json`. Two different exact counting
methods agree: direct divisibility testing and recursively pruned
inclusion-exclusion over least common multiples. The latter prunes only terms
whose least common multiple exceeds the interval endpoint; all such terms are
exactly zero.

Now

    n S(m) = 191*827 = 157957,
    2m S(n) = 2*3158*25 = 157900.

The conjectured strict inequality is reversed with a positive gap of 57; this
is not merely an equality-edge counterexample. The literal split counts,
structure, negated conjecture and gap are formalized as `split_values`,
`tail_structure`, `not_pair_tail` and `pair_tail_gap`.

## 4. The split count must not be confused with the original union count

Removing multiples of V is not the same as adjoining V to the generator set.
In fact, every finite A containing 2 and 3 satisfies the main strict inequality
for all n>=3 and m>n. The even integers up to n together with the integer 3 give

    F_A(n) >= floor(n/2)+1,
    2F_A(n) >= n+1.

As F_A(m)<=m and m>0,

    n F_A(m) <= nm < (n+1)m <= 2m F_A(n).

This general deduction and its application to U union V are included in Lean
as `original_for_sets_containing_two_three` and
`tail_example_satisfies_original`. They rule out interpreting our split witness
as a counterexample to Erdős 488, for all legal n,m, not merely the displayed pair.

## 5. Consequences for further research and limits

Neither universally nonnegative sparse total slack nor componentwise pair-tail
doubling can be used as a valid general lemma. A block-decomposition proof
would instead need to control compensation between blocks, or use a different
aggregate estimate. The decomposition identity itself is not refuted here.
The earlier rounded-equivalence theorem and bounded-normalized-generator
verification do not assume these conjectures and are not invalidated.

These are complete finite refutations of the two specified auxiliary claims.
They are not a complete solution of the original prize problem. No prize PR,
official status change, recipient record or payment claim is made. Independent
human review and a comprehensive priority assessment have not been obtained.
