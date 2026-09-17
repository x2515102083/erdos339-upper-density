# Completed verification evidence

This is contributor-run build and axiom evidence, not an independent referee attestation, a first-priority certificate, or an award decision.

## First successful complete proof

- Proof source commit: `3bbb1287abd588301218fa850a009a93953ec984`.
- Branch: `research/prize-complete-20260918`.
- [Successful run 35265756520](https://github.com/x2515102083/erdos339-upper-density/actions/runs/35265756520), job `105352398131`.
- The completed success status and full job log were both read.
- `lake build` succeeded, followed by fresh source elaboration with `lake env lean Small.lean`.
- Lean 4.32.1; Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`.

All eight named roots reported exactly `[propext, Classical.choice, Quot.sound]`:

```
Erdos549Small.tree_isTree
Erdos549Small.blue_union_bound
Erdos549Small.blue_degree
Erdos549Small.red_degree
Erdos549Small.no_monochromatic_copy
Erdos549Small.ramsey_ne_35
Erdos549Small.not_erdos_549
Erdos549Small.explicit_counterexample
```

The workflow checked the expected root names and rejected any additional axiom. The complete original universal negation is one of these roots, not just the concrete numeric facts. `IsContained` is ordinary non-induced containment. The target graph's tree property and bipartition are proved.

Hosted source SHA-256:

```
129f0f29aa613d6c12964679e8e06c9c0e76cd51134ddb10432d34c93874e891  Small.lean
ab172e753bb753cd86ad81cbffaa55c0e1f78c65908e70ffd5ee6ede60cfd159  RamseyDefs.lean
8e3538e0ab5f81a3ee04927d8838c8c674e0e112838b4b3ce87ec218143276af  lean-toolchain
9391ecc612cb21e648f272fdaa2e8e190f84cc1543f21df09b6b71d77cd188a0  lakefile.toml
```

The manifest generated during that earlier run had SHA-256 `be1ed4a5bb83d4083f7852e30297b5d667235fbec496ce15b17cf479ae9b7dd3`. The subsequently committed manifest explicitly pins the same package revisions; its serialization is not claimed byte-identical. The expanded final workflow uses the committed manifest without `lake update`, rejects lockfile changes, treats Lean warnings as errors, and separately runs the Python witness check. Refer to its actual run result at the selected commit; a workflow definition alone is not evidence that it passed.

The initial run `35265094310` failed on the new graph relation-instance interface and explicit type/cardinality conversions. Commit `3bbb1287abd588301218fa850a009a93953ec984` supplied those instance constructors and conversions. No mathematical hypothesis, witness, or conclusion was dropped or changed to obtain the successful proof. Failed runs are not verification evidence.

## Scope and limits

The result is a complete negative resolution of the original asserted formula `R(T)=4k-1`, using k=9. It does not determine every tree Ramsey number, claim the first disproof, claim the first formalization, or certify that 35 is the smallest possible witness. Prior mathematical work and the earlier complete 63-vertex formalization/PR #839 are disclosed in README.md.

Mathlib's compiled cache is used. Neither a fresh source rebuild of all dependencies, an independent checker implementation, nor independent human review is claimed. No official catalog eligibility, candidate, recipient, award, or payment field is changed by the proof repository.
