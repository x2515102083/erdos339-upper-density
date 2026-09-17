# Erdős 339 upstream license clarification

Checked on 2026-09-18. This note is a review record, not a license grant.

## Evidence

The source used by the complete-problem submission is
[Erdos339.lean at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos339.lean).
Its header credits the mathematical and formal authors, but supplies no explicit
license grant. The enclosing
[src/latest/LICENSE](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/LICENSE)
says only that **some files from external sources** are licensed under Apache-2.0.
It does not identify Erdos339.lean as one of those files or grant a blanket
license for the directory. GitHub's repository-license endpoint returned 404;
that alone would not establish the absence of a license.

Conclusion: an applicable grant for this specific file has not been established.
Keep the dependency limitation in the submission. Downloading and transforming
the source locally does not itself supply permission. Do not relabel it Apache-2.0
or remove the limitation without an explicit applicable grant.

The published `complete-original-problem` branch and its pinned proof commit
remain unchanged. This note on `main` does not amend or revalidate the complete
proof or supply permission for its dependencies.

## Unsent clarification request

Suggested title: License clarification for ErdosProblems/Erdos339.lean

Hello, could an authorized rights holder clarify the license applying to
`src/latest/ErdosProblems/Erdos339.lean` at commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`?

The file attributes the formalization to Codex / GPT-5.6 Sol. The enclosing
LICENSE mentions Apache-2.0 for some externally sourced files, but I could not
establish that this statement covers Erdos339.lean. Our downstream formalization
uses its finite combinatorial and lower-density proofs and makes a disclosed
compatibility change. We retain attribution and currently disclose the unclear
license; generated upstream files are not committed to the downstream repository.

Could you confirm whether copying, modification, redistribution, and use in a
public formalization/prize submission are permitted, and under which license?
If possible, please add a file-specific or otherwise unambiguous license notice
and clarify whether it covers the cited revision. Thank you.

This draft has not been posted. If permission cannot be established, alternatives
are an independently authored replacement or not relying on the dependency for
the submission; neither is completed by this note.
