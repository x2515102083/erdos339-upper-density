# Generalized Erdos 316: research workbench

This is an isolated research branch, not an award submission. The earlier Erdos 339 proof branch and its pinned submission are unchanged. The package name is retained only to reuse its exact dependency lockfile.

## Scope

`Packing.lean` develops an integer-capacity obstruction, its rational-grid and genuine-unit-fraction bridges, and one explicit three-bin counterexample. It does NOT yet prove `Erdos316.erdos_316.variants.generalized` for every number of bins. No complete-generalization, first-formalization, official-verification, prize-eligibility or payment claim is made.

The general mathematical result is credited to Csaba Sandor, *On a problem of Erdos*, Journal of Number Theory 63 (1997), 203-210, as recorded in the Formal Conjectures source. The main two-bin formalization already exists and is credited there to Bhavik Mehta; it is not claimed as our new contribution.

Primary statement and existing proof:
https://github.com/google-deepmind/formal-conjectures/blob/cbee53b0ccb3bacf2d9e9b2bf2eea493a373b22c/FormalConjectures/ErdosProblems/316.lean

The target uses partitions into **at most** n nonempty parts, or equivalently colorings into n colors with empty color classes allowed. Replacing this with exactly n nonempty parts permits vacuous witnesses and is not acceptable.

New code in this branch was prepared with AI assistance for GitHub account x2515102083. Attribution of the historical theorem is not changed. No JSP identifier or award eligibility has been established for this research target.

## Reproduction

Lean 4.32.1; Mathlib commit 520045ab14e26149ee970e2e617ca04b09bde5d6 and all transitive revisions are locked in lake-manifest.json.

```
lake exe cache get
lake build Packing
lake env lean Packing.lean
```

The workflow checks only the declarations actually present in Packing.lean and audits their axioms. A successful run, if observed, does not establish the missing universally quantified construction or an official prize decision. No successful run is asserted by this initial research commit.
