# Erdős 440 / JSP-000359: real thresholds and a strict finite cutoff

This is an **incremental Lean formalization with an explicitly attributed core**, not a first mathematical solution or a first Lean solution of this problem. Prior intake includes TheJustinSunPrize/awards issue #22 and PR #34. No prize entitlement, global priority, independent-operator review or designated isolated verification is asserted.

For an arbitrary strictly increasing sequence A of positive integers, define

    C_A(x) = #{ i >= 0 : lcm(A(i), A(i+1)) <= x }.

`Proof.lean` defines this count over real x and proves that its finite enumeration includes **every** qualifying index. `realCount_eq_ncard` and `qualifying_indices_finite` identify it with the literal set cardinality.

## Complete real-threshold endpoint

`Erdos440Real.complete_original_problem` proves all five statements:

1. Every C_A(x) is O(sqrt(x)) as real x tends to infinity.
2. Every limsup C_A(x)/sqrt(x) is at most kappa.
3. The attributed explicit sharp sequence attains limsup kappa.
4. Every liminf C_A(x)/sqrt(x) is at most 1.
5. The sequence of all positive integers attains liminf 1.

Here kappa = sum over d >= 1 of 1/(sqrt(d)*(d+1)), namely the imported `Erdos440.sharpConstant`. The main new bridge theorems `real_limsup_eq_nat` and `real_liminf_eq_nat` preserve **both** extrema exactly. They do not rely on the invalid inference that a subsequence controls both extrema.

The proof uses C_A(x)=C_A(floor(x)) for x>=0 and sqrt(floor(x))/sqrt(x) -> 1. The floor map carries the real atTop filter exactly onto the natural atTop filter. Nonnegativity and boundedness hypotheses needed for real-valued liminf/limsup are proved explicitly.

## Strict finite refinement

`Erdos440Cutoff.strict_cutoff` proves, for every positive natural threshold X and cutoff t,

    t * C_A(X) < t * (t-1) + X.

Consequently, `Erdos440Cutoff.square_threshold` gives

    C_A(m^2) + 2 <= 2*m       for every m>=1.

Split indices according to A(i)<t or A(i)>=t. The first part has at most t-1 indices. For the second, telescope the reciprocal drops 1/A(i)-1/A(i+1); the remaining endpoint term is strictly positive. Keeping this term gives the strict inequality rather than discarding it in an asymptotic estimate. This is an elementary finite refinement, not a claimed globally new number-theoretic discovery.

## Provenance and contribution boundary

The five files fetched unchanged under `upstream/` come from `plby/lean-proofs`, commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, and are checked against fixed Git blob hashes. Their formal authors are credited as Codex and GPT-5.6 Sol. The historical mathematics is attributed to Erdős and Szemerédi. The natural-threshold optimal constants and sharp construction are **reused**, not authored here. See `ATTRIBUTION.md`.

New local files `Proof.lean` and `Cutoff.lean`, reproducibility and audit integration: x2515102083 with ChatGPT assistance. PR #34 already gives an independent real-threshold square-root bound and sharp liminf; it expressly excludes the optional sharp limsup. Reviewers must assess the usefulness, overlap and award eligibility of this additional transfer and finite refinement.

## Reproduce

Install the exact toolchain from `lean-toolchain` (Lean 4.33.0), then run in this directory:

```sh
python3 bootstrap.py
lake exe cache get
lake build
lake env lean -DwarningAsError=true Proof.lean > proof-axioms.log
lake env lean -DwarningAsError=true Cutoff.lean > cutoff-axioms.log
cat proof-axioms.log cutoff-axioms.log > axioms.log
python3 audit.py axioms.log
python3 bootstrap.py
git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json
```

Mathlib is pinned to `db584cd6d46c92f209a44c0f1c829460d327499d`; all transitive dependencies are pinned in the committed lockfile. The bootstrap rejects modified tracked dependency sources or mismatched existing checkouts. Upstream files are rechecked byte-for-byte. Dependency caches may be used; this is not a network-isolated run.

The audit requires exactly one dependency report for each of ten named public theorems and permits only `propext`, `Classical.choice` and `Quot.sound`. It checks the seven proof-source files and runs wrong-proof, unapproved-axiom and missing-report negative controls. A successful preliminary environment/probe workflow is **not** evidence that these proof gates passed; only a run that checks both proof files and completes the audit counts.

Official mathematical-fidelity review, independent-operator reproduction, the designated isolated audit, attribution/priority review and any award decision are still separate requirements.
