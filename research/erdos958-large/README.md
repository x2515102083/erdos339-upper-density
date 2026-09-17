# Erdős 958: counterexamples of every size n >= 4

This directory is a self-contained Lean project proving the negative answer to the **eventual equidistant-line-or-circle classification** in Erdős Problem 958. It does not solve the general-position crescent problem. In particular, it is **not asserted to solve JSP-000199**.

## Scope and attribution

Mathematical construction: Felix Christian Clemen, Adrian Dumitrescu and Dingyuan Liu, *On the mutiplicities of interpoint distances*, arXiv:2505.04283v1 (7 May 2025), Introduction Question (4), Section 5. The mathematics is prior work, not a new mathematical discovery by this contributor.

Original source: <https://arxiv.org/html/2505.04283v1#S5>.

New Lean development: **x2515102083**, with **ChatGPT (GPT-6 Astra Pro)** assistance. The three Lean modules were written in this branch. They do not import proofs from the other Erdős projects in this repository. Mathematical solver credit and formalization contribution credit must remain separate.

The two distance definitions, classification predicates and statement are adapted from the Apache-2.0 Formal Conjectures project at the pinned commit:

`d5ba143cc2fafd48cc6d5b6320a3aab287c38df7`

Reference files:
- <https://github.com/google-deepmind/formal-conjectures/blob/d5ba143cc2fafd48cc6d5b6320a3aab287c38df7/FormalConjectures/ErdosProblems/958.lean>
- <https://github.com/google-deepmind/formal-conjectures/blob/d5ba143cc2fafd48cc6d5b6320a3aab287c38df7/FormalConjecturesForMathlib/Geometry/Metric.lean>

Their authors' copyright notices are retained in the source. New code and documentation in this directory are Apache-2.0; see `LICENSE` and `NOTICE`.

## Exact endpoints

`Erdos958Large.counterexample_every_n` proves, for every natural number `n >= 4`, existence of a finite set of **exactly n genuine Euclidean planar points** with:

- exactly `n - 1` nonzero distinct distances;
- the image of their unordered-pair distance multiplicities equal to `Finset.Icc 1 (n - 1)`;
- neither the reference equidistant-line predicate nor the reference equidistant-circle predicate.

`Erdos958Large.not_eventual_classification` refutes the original threshold statement by choosing `n = max N 4` for any proposed threshold `N`.

`Erdos958.erdos_958` has the original `False ↔ ...` shape. The reference's `answer(False)` is resolved to `False`, `ℝ²` is spelled out as `EuclideanSpace ℝ (Fin 2)`, and cardinality notation is expanded. No restriction to a fixed small example or extra unproved geometric hypothesis is introduced.

`distanceSet` is the image of *all* ordered off-diagonal pairs under Euclidean distance. `distanceMultiplicity` is the filtered ordered-pair count divided by two. The proof uses these definitions directly, not a postulated equivalence with a different metric or a distance table.

## Proof organization

For `m = n - 1`, set `t = pi / (6 * (m + 1))`. Place `m` unit-circle points at angles `(i - 1) * t`, for `0 <= i < m`, and add the origin.

`Geometry.lean` proves the distance identities, injectivity of the short arc, strict ordering of gap distances, and their separation from radius 1. Three selected points cannot lie on any common line. The origin and the arc points at angles `-t, 0, t` cannot lie on any common circle, regardless of its centre.

`Counting.lean` proves an abstract `ArcConfig` counting theorem. It partitions the complete off-diagonal pair set into spokes and gap classes. The radius has multiplicity `m`; gap `k` has multiplicity `m-k`. Both orientations are counted before division by two, so all distances and all pairs are covered.

`Complete.lean` supplies every `ArcConfig` assumption using actual points, establishes both classification exclusions, and proves the full eventual statement false.

## Reproduction

Pinned proof/build revision:

`606c2de91dd864f73cd3739d36e78370316a0dbe`

Branch: `research/erdos958-large-20260918`

With Git, Python 3 and Elan installed:

```sh
git clone https://github.com/x2515102083/erdos339-upper-density.git
cd erdos339-upper-density
git checkout 606c2de91dd864f73cd3739d36e78370316a0dbe
cd research/erdos958-large
python3 bootstrap.py
lake exe cache get
python3 verify.py
```

The version pins are Lean `4.32.1` (compiler commit `f054605aea4b840552cca2e725580bffd1e1b704`) and Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`. All transitive package revisions are fixed in `lake-manifest.json`; `bootstrap.py` checks exact revisions and rejects modified tracked dependencies. Do not run `lake update` to reproduce this result.

`verify.py` compiles all three files with warnings treated as errors. It scans the proof source for placeholders, custom axiom declarations and several bypass constructs; prints SHA-256 source hashes; and checks nine printed axiom closures, including all final endpoints, against `{propext, Classical.choice, Quot.sound}`. It does not generate, patch or download proof source. It uses the normal Lean kernel and cached Mathlib dependencies; it is not an independent implementation of a proof checker or a fresh source rebuild of all dependencies.

Public CI record for the pinned revision:
<https://github.com/x2515102083/erdos339-upper-density/actions/runs/35276651741>.

Consult the actual run conclusion and log rather than treating this document as a substitute for verification.

## Prior formalizations and prize status

**No first-formalization priority is claimed.** During final scope checks we found the earlier full-family submission by **KunHcz**, linked from official issue **#750** and original PR **#421**. Its statement covers every `n >= 4` and the same original eventual classification. This is material overlapping prior formalization, not merely the previously known four-point example. We have not independently rebuilt that other package.

- Existing correspondence request: <https://github.com/TheJustinSunPrize/awards/issues/750>
- Earlier full-family package: <https://github.com/KunHcz/jsp-nonpinnacle-proofs/tree/d1a0fc2d9badb31f290c95d937f430b99c0f962b/submissions/erdos-958>
- General-position scope correction: <https://github.com/TheJustinSunPrize/awards/issues/57>

The present branch's proof and counting were authored before inspecting that full-family package. The earlier submission is disclosed, not claimed as this account's work. Earlier Aristotle/Seed-Prover-related references for 958 also require due consideration; inspecting one small-example file does not establish that all prior formalizations were small examples.

Our arc contains many cocircular points. The weaker condition “not all points lie on a circle” is not equivalent to “no four points are cocircular.” Consequently, these results cannot be applied to the latter problem. An existing catalog identifier for this exact 958 statement has not been confirmed. No catalog status, candidate status, award eligibility, monetary entitlement, or payment is asserted. Any request for recognition must disclose the overlap and be assessed separately by maintainers.
