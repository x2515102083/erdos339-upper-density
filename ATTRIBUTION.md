# Attribution and scope

This is an incremental formalization, not a claim to the first mathematical solution or first Lean proof of Erdős 440 / JSP-000359.

The historical mathematics is attributed to Paul Erdős and Endre Szemerédi (1980). The elementary square-root argument also has expositions by Terence Tao and W. van Doorn.

The five files fetched under `upstream/` are reused unchanged from **plby/lean-proofs**, commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, `src/latest/ErdosProblems/Erdos440.lean` and its four local dependencies. Their header lists formal authors **Codex** and **GPT-5.6 Sol**. We do not claim authorship of their upper bound, sharp constant, sharp sequence construction, or optimal liminf argument. The bootstrap checks their exact Git blob hashes. No copy of those sources is represented as our own.

Prior intake includes awards issue #22 and PR #34 (zilan520), which provides an independent real-threshold proof of the square-root bound and sharp liminf. That PR expressly excludes the optional sharp limsup. Our intended new scope is a reusable real/natural threshold transfer preserving both limit extrema, an integrated real-threshold sharp-limsup resolution using the attributed core, and a finite rounding estimate. No global novelty is claimed for an elementary transfer or bound before independent review.

New local source and integration: x2515102083, with ChatGPT assistance. Any award is solely for the contribution reviewers determine attributable to this increment, not the reused proof. Formal mathematical fidelity, designated isolated verification, priority and prize assessment remain external decisions. This research branch is not itself a prize claim.
