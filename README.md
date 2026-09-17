# Erdős 339: both original density questions

This project integrates a **complete formalization of both original clauses**
of [Erdős Problem 339](https://www.erdosproblems.com/339), corresponding to
Justin Sun Prize catalog **JSP-000281**. A claim of successful verification
must refer to a **specific successful GitHub Actions run and its commit**;
the presence of these source files alone is not such evidence.

## Exact statements

For `A : Set Nat`, let `r • A` be the sumset allowing repetitions and
`restrictedSums r A` the sums of exactly `r` pairwise distinct elements.

* `Erdos339.erdos_339`: an asymptotic additive basis of order `r` has a
  restricted order-`r` sumset of positive **lower density**.
* `Erdos339.erdos_339_upperDensity`: positive **upper density** of `r • A`
  implies positive upper density of `restrictedSums r A`.
* `Erdos339.erdos_339_complete` in `Erdos339/Complete.lean`: the conjunction
  of those two original statements, universally quantified over `A` and `r`.
* `Erdos339.upperDensity_nsmul_le_restrictedSums`: the quantitative comparison
  for infinite `A`. No density limit, basis hypothesis, or fixed order is
  assumed for the second original clause.

Order zero is included, with impossible premises. The basis definition is
cofiniteness of the unrestricted sumset, not an extra unproved hypothesis.
`Audit.lean` prints both definitions and all target statement/axiom reports.

## Reproduce at a pinned commit

Use branch **`complete-original-problem`**. For a submitted commit, check out
its full 40-character SHA before running these commands. Install elan first
and make its `lean` and `lake` shims available on PATH. Python 3.10+ is required.

```sh
python3 bootstrap.py
lake exe cache get
lake build
lake env lean Audit.lean
```

The Lean toolchain is `leanprover/lean4:v4.32.1`. Mathlib is pinned by
`lake-manifest.json` to `520045ab14e26149ee970e2e617ca04b09bde5d6`.
Do not run `lake update` or change the lockfile to reproduce a submission.
The bootstrap downloads one immutable upstream source, checks SHA-256
`2ff897f1d26d160f01ad2a50c94050aab55f80ef00d4a2545a15f3eabfcfd87d`, and
extracts the proved finite machinery and lower-density endpoint. It makes
one disclosed compatibility proof change, not an assumption or axiom.

[Verification workflow](https://github.com/x2515102083/erdos339-upper-density/actions/workflows/verify.yml)
runs a clean checkout, bootstrap, Mathlib cache retrieval, `lake build`, and
an axiom audit rejecting anything outside `propext`, `Classical.choice`, and
`Quot.sound` for all four target theorems. Read the actual run conclusion;
failed or pending runs do not establish verification. Cached Mathlib is used,
not a from-source rebuild of all transitive dependencies or an independent
kernel implementation. This workflow does not make a prize decision.

`evidence/legacy-upper-density.log` is a historical submitted log for the old
upper-only revision `96eab57b0ab449bc03a95e797e3dd5e4de841156`.
It is **not** evidence that this complete-problem revision was verified.
The old `SHA256SUMS` was removed because it described that earlier snapshot.
Git commit pinning and the current workflow identify the present sources.

## Attribution and contribution being evaluated

Mathematical solution: **Norbert Hegyvári, François Hennecart and Alain
Plagne**, *A proof of two Erdös conjectures on restricted addition and further
results*, J. Reine Angew. Math. 560 (2003), 199–220,
[DOI](https://doi.org/10.1515/crll.2003.055).

Reused finite proof and lower-density formalization: **Codex / GPT-5.6 Sol**
in **plby/lean-proofs**, immutable source
[`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos339.lean).
The new contribution under review is the AI-assisted **upper-density
extension and full-statement reproducibility integration**, submitted by
GitHub account `x2515102083`. The lower-density proof is included to make the
original problem complete, **not** claimed as new work. The earlier official
[evidence issue #22](https://github.com/TheJustinSunPrize/awards/issues/22)
should be considered when assessing overlap and attribution.

No mathematical discovery, sole ownership of reused code, globally first
priority, guaranteed eligibility, award amount, or payment is asserted.
A public applicant/recipient identity remains unconfirmed. Use
`RECIPIENT-JSP-000281-A` until the organizer confirms a public identity.
Never post identity documents, payment details, or private contact information
in this repository or in public prize threads.

## Licensing limitation

New files and the explicitly licensed density utility have the scoped
Apache-2.0 notices in `LICENSE` and `NOTICE`. The upstream finite and lower
proof has **no stated redistribution license**. The generated `Finite.lean`
and `LowerDensity.lean` are therefore not distributed here. Fetching a public
source does not confer a new redistribution license; this dependency remains
an issue for maintainer review and possible upstream permission. No license
or authorship rights in upstream material are asserted by this repository.
