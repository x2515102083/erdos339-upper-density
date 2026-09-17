# Erdos 549 / JSP-000440: a 35-vertex counterexample

This package gives a complete Lean proof of the **negation of the original universal formula**, not a formula for every tree Ramsey number. It is not a claim of first mathematical solution, first formalization, minimal witness size, independent referee approval, or award entitlement.

The main theorem is `Erdos549Small.not_erdos_549` in `Small.lean`. An additional existential endpoint is `Erdos549Small.explicit_counterexample`.

## Exact original question and correspondence

For every integer k >= 2, and every tree T with bipartition classes of sizes k and 2k, is its two-color Ramsey number equal to 4k-1?

The answer is no. Take k=9 and the double star S(17,8), with 27 vertices and bipartition sizes 9 and 18. A concrete coloring of the complete graph on 35=4*9-1 vertices contains no monochromatic, **not necessarily induced**, copy of this tree.

The Lean endpoint quantifies over the same types and hypotheses as the [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/d5ba143cc2fafd48cc6d5b6320a3aab287c38df7/FormalConjectures/ErdosProblems/549.lean). Only the unused proof-binder name changes. Instead of that file's answer macro, the endpoint directly proves the negation of the complete universal proposition. A counterexample is a complete negative resolution of that universal question, not merely a special-case positive result.

The two Ramsey-number definitions in `RamseyDefs.lean` are reproduced, with attribution and license, from the same pinned repository's [Ramsey definitions](https://github.com/google-deepmind/formal-conjectures/blob/d5ba143cc2fafd48cc6d5b6320a3aab287c38df7/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean). No theorem proving this problem is imported. Mathlib's `IsContained` means an injective graph homomorphism, not an induced embedding.

## Construction and proof

The target tree has vertices `Fin 9` plus `Fin 18`. Join the left vertex i to the right vertex j exactly when i=0 or j=0. This gives 26 edges. Every vertex reaches the left center, so the graph is connected; connectedness and the edge count imply it is a tree. The high-degree center has 18 neighbors. The tree and bipartition properties are proved, not assumed.

Divide the 35 host vertices into five blocks of size seven. Label the blocks cyclically modulo 5, and label vertices inside a block from 0 to 6. Color an edge blue when its endpoints are in the same block, or in consecutive blocks with different internal labels. Color every other edge red.

Each blue vertex has six neighbors in its own block and six in each adjacent block, giving blue degree 18 and red degree 16.

For a blue edge inside one block, the two neighborhoods have union size 21. For an edge between consecutive blocks, the union consists of all seven vertices in each endpoint block, together with six vertices in each of the two outside adjacent blocks, for a total of 26. The needed finite upper bound and degrees are checked in Lean with ordinary `decide`; Python data and external solvers are not assumptions.

If the target tree had a blue copy, every one of its 27 vertices would lie in the union of the blue neighborhoods of the two center images. The centers form a blue edge, so this union has at most 26 vertices, contradicting injectivity. A red copy would require 18 different neighbors at its high-degree center, contradicting red degree 16.

Thus the defining universal Ramsey property fails at 35. The proof of `ramsey_ne_35` handles the natural-number `sInf` convention explicitly: an assumed value 35 is positive, hence the defining set is nonempty and its infimum belongs to it. No unproved Ramsey-existence assumption is added to the endpoint. This proof is of R(T) != 35 and the complete original negation; no separate formalized exact Ramsey value is asserted.

## Attribution and prior work

The original mathematical disproof belongs to **Sergey Norin, Yue Ru Sun, and Yi Zhao**, [Asymptotics of Ramsey numbers of double stars](https://arxiv.org/abs/1605.03612), arXiv:1605.03612 (2016). Their paper's Corollary 3.2 uses a five-cycle blow-up framework. The present exact construction deletes equal-label matchings between adjacent seven-vertex blocks, rather than invoking a probabilistic asymptotic existence result. This package does not claim the underlying five-cycle method as new.

An earlier complete formalization exists in [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos549.lean). Its header credits Codex and GPT-5.6 Sol and uses a 63-vertex, threefold clique blow-up of the line graph of K7, with tree S(31,15). [Award PR #839](https://github.com/TheJustinSunPrize/awards/pull/839) is a dedicated intake/interface for that existing proof. Those earlier contributions are acknowledged and not displaced. The present proof is not a wrapper or copy of that source: it uses the distinct 35-vertex witness and independently written proofs in `Small.lean`. Related projects were not independently rebuilt here. Searches and inspected headers are not a worldwide priority certification.

Contributor for this submitted concrete formalization: public account **x2515102083**, with ChatGPT assistance in construction, Lean development, checking, and documentation. Public-account attribution does not establish a verified legal identity. Mathematical-solver credit, Lean contribution credit, organizer verification, and award decisions remain distinct.

## Reproduction and trust boundary

Pinned Lean: `leanprover/lean4:v4.32.1`. Pinned Mathlib: `520045ab14e26149ee970e2e617ca04b09bde5d6`. The committed manifest also fixes all transitive package revisions.

From this directory:

```sh
python3 bootstrap.py
lake exe cache get
lake build
lake env lean -DwarningAsError=true Small.lean > axioms.log
python3 audit.py axioms.log
python3 verify.py --output results.json
```

`bootstrap.py` fetches exactly the committed revisions, rejects modified tracked dependency sources, and does not update the lockfile. The optional Python verifier separately constructs the blue graph in two ways and checks the tree, degrees and complete edge-neighborhood histogram. It is not part of the Lean proof's premises.

The Lean source uses no proof placeholders, custom axioms, or native-decision shortcuts. Its finite computations use ordinary `decide`. The audit requires all eight named roots and permits only `propext`, `Classical.choice`, and `Quot.sound`. The project uses the pinned Mathlib compiled cache, not a fresh rebuild of every dependency or a second independent proof-checker implementation.

See [VERIFICATION.md](VERIFICATION.md) for completed hosted evidence. A green workflow is not an award or independent human review. Earlier Erdos 339/#681 and Erdos 488 work is outside this package and is not altered by this contribution.

## License

The new concrete proof, scripts and documentation are offered under Apache-2.0 to the extent copyright applies. `RamseyDefs.lean` retains the Formal Conjectures Authors notice and license. See [LICENSE-APACHE-2.0](LICENSE-APACHE-2.0). No third-party Erdos 549 proof source is vendored.
