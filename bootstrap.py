"""Fetch and extract the pinned, attributed finite proof dependency locally.

The upstream theorem has no stated redistribution license. This script does
not grant one; the generated dependency is excluded from this repository.
"""
from hashlib import sha256
from pathlib import Path
from urllib.request import urlopen

REVISION = "8822f7ddef30fadbd92e1c6ab4ed897af356af5e"
BASE = f"https://raw.githubusercontent.com/plby/lean-proofs/{REVISION}/src/latest/"
ROOT = Path(__file__).resolve().parent


def fetch(path: str, digest: str) -> str:
    with urlopen(BASE + path, timeout=60) as response:
        data = response.read()
    if sha256(data).hexdigest() != digest:
        raise ValueError(f"Pinned source checksum mismatch: {path}")
    return data.decode("utf-8")


def between(source: str, start: str, stop: str) -> str:
    return source[source.index(start):source.index(stop)]


def main() -> None:
    source = fetch(
        "ErdosProblems/Erdos339.lean",
        "2ff897f1d26d160f01ad2a50c94050aab55f80ef00d4a2545a15f3eabfcfd87d",
    )
    header = source[:source.index("import ErdosProblems.Erdos868")]
    finite = (
        header
        + "/- Extracted finite combinatorial machinery from plby/lean-proofs, commit "
        + REVISION
        + ".\nOriginal authors and mathematical provenance retained above.\n"
        + "The unrelated Erdos868 import and lower-density endpoint are omitted. -/\n\n"
        + "import Mathlib.Algebra.Group.Pointwise.Set.BigOperators\n"
        + "import Mathlib.Algebra.Order.BigOperators.Group.Finset\n"
        + "import Mathlib.Tactic.Ring\nimport Mathlib.Tactic.SplitIfs\n"
        + "import Util.Density\n\n"
        + between(source, "open Filter Function", "/-! ## Consequences of the asymptotic-basis hypothesis")
        + between(source, "lemma eventually_large_prefix_of_infinite", "lemma basis_prefix_card_lower_bound")
        + between(source, "lemma partialDensity_nat_eq_prefix_card", "/-!\n## Erdős Problem 339")
        + "\nend Erdos339\n"
    )
    # Lean/mathlib 4.32.1: avoid simplifying a subtype membership to True.
    old = "    simpa [B] using b.property"
    if finite.count(old) != 1:
        raise ValueError("Expected exactly one source-selection compatibility site")
    finite = finite.replace(old, "    obtain ⟨n, _, hn⟩ := Finset.mem_image.mp b.property\n    exact ⟨n, hn⟩")
    target = ROOT / "Erdos339" / "Finite.lean"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(finite, encoding="utf-8", newline="\n")
    print(f"Prepared {target.name} from {REVISION}; SHA-256 {sha256(finite.encode()).hexdigest()}")


if __name__ == "__main__":
    main()
