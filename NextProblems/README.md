# Next problem formalizations

This directory is an independent work batch on branch `next-problems-20260917`.
The previously submitted `complete-original-problem` branch and awards PR #681
are not modified by this work.

## Exact coverage

| File | Result | Important boundary |
| --- | --- | --- |
| `Powerful.lean` | Complete negative answer to the scoped JSP-000301 question, using 12167 and 12168. | This finite counterexample already has earlier public formalization submissions; no first-priority claim is made. |
| `Powerful.lean` | `arbitrarily_large`: for every natural bound N, there is n>N such that n and n+1 are powerful and neither is square. | This is an additional infinite-family result, not the counting question in Erdos #365. |
| `Erdos1209.lean` | Exact negative answers to Erdos #1209 parts (i) and (ii), including strict monotonicity and every prescribed pointwise growth bound. | This does not settle the remaining parts (iii.a)-(iii.d), and is not a complete solution of the broad JSP-001014 record. |

The stronger `simultaneous_unique_shift` theorem gives the same sequence for both
parts of #1209: its prime-good shifts and squarefree-good shifts are both exactly
`{0}`. The six printed axiom reports are six verification endpoints, not six
independent problems.

## Mathematical construction

For powerful pairs, start with `(x,y)=(1,1)` and apply

```
x' = 24335*x + 24336*y
y' = 24334*x + 24335*y.
```

The recurrence preserves `12167*x^2 + 1 = 12168*y^2`. Both coordinates stay positive,
and the first strictly increases. Multiplication by a positive square preserves
powerfulness, while the fixed rational nonsquare classes of 12167 and 12168
exclude squares. This yields explicit pairs above every bound.

For #1209, fix a positive shift n and choose a prime q>n. Then n is coprime to q^2.
Dirichlet's theorem supplies an arbitrarily large prime p with
`p = -n (mod q^2)`, so n+p is not squarefree. At index k, choose this prime for
n=k+1, above both the requested bound f(k) and the preceding sequence term.
The zero shift makes every term prime and hence squarefree. Every positive shift
is excluded by its assigned index. The two original implications to infinitude
therefore fail for every proposed growth-bound function.

## Reproduce

From this repository at the selected branch, with elan installed:

```sh
lake exe cache get
lake env lean NextProblems/Powerful.lean
lake env lean NextProblems/Erdos1209.lean
```

Both files import Mathlib only. Running `bootstrap.py` or building the old Erdős
339 library is unnecessary for these commands.

The committed environment is Lean **4.32.1**, Mathlib revision
`520045ab14e26149ee970e2e617ca04b09bde5d6`, with transitive dependency revisions
in the existing `lake-manifest.json`. The proof-source snapshot is commit
`e27776b597c7197ea17ced39b16e249978fda027`.

The workflow [Verify next problem proofs](../.github/workflows/next-problems.yml)
compiles every new Lean file, requires all six endpoint reports, rejects any
reported axiom outside `propext`, `Classical.choice`, and `Quot.sound`, and prints
the tested commit and source SHA-256 hashes. An existing workflow is not evidence
of success: use a completed successful run for the exact submitted revision.
GitHub Actions logs are hosted execution evidence, not permanent independent
archival or mathematical peer review.

## Provenance and limitations

These are AI-assisted formalizations of known mathematics, not claimed new
mathematical discoveries. New proof implementations were written for this batch.
Mathlib supplies library results, including its proved Dirichlet theorem; no
additional axiom is introduced for that theorem.

The #1209 statement formulations are adapted from The Formal Conjectures Authors
(Apache 2.0), with the original attribution preserved in the Lean header:

- [Exact statement source at cbee53b0ccb3bacf2d9e9b2bf2eea493a373b22c](https://github.com/google-deepmind/formal-conjectures/blob/cbee53b0ccb3bacf2d9e9b2bf2eea493a373b22c/FormalConjectures/ErdosProblems/1209.lean).
- [Scoped JSP-000301 record at 82be4c4913b8fe394d68d1391f4c221fde947211](https://github.com/TheJustinSunPrize/awards/blob/82be4c4913b8fe394d68d1391f4c221fde947211/problems/catalog-0301-0400.md#JSP-000301).
- [JSP-001014 record at the same catalog revision](https://github.com/TheJustinSunPrize/awards/blob/82be4c4913b8fe394d68d1391f4c221fde947211/problems/catalog-1001-1022.md#JSP-001014).

Earlier JSP-000301 filings include awards PRs #33 and #108, among others. This
batch makes no first-formalization, priority, prize eligibility, award, or payment
claim. No new awards PR is submitted for the duplicate finite example or for a
partial solution of the broader #1209 problem. Existing solver attribution,
eligibility fields, and official review records are unchanged.
