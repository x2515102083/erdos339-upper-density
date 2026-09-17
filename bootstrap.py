"""Prepare both proved clauses of Erdos 339 from an immutable dependency.

The upstream source has no stated redistribution license. Generated files
are excluded from this repository; this script does not grant such a license.
Mathematical and formal authors are retained in each generated file.
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
    first = source.index(start)
    last = source.index(stop, first + len(start))
    return source[first:last]


def write_generated(name: str, content: str) -> None:
    target = ROOT / "Erdos339" / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(content, encoding="utf-8", newline="\n")
    print(f"Prepared {name} from {REVISION}; SHA-256 {sha256(content.encode()).hexdigest()}")


def main() -> None:
    source = fetch(
        "ErdosProblems/Erdos339.lean",
        "2ff897f1d26d160f01ad2a50c94050aab55f80ef00d4a2545a15f3eabfcfd87d",
    )
    header = source[:source.index("import ErdosProblems.Erdos868")]
    provenance = (
        "/- Generated locally from plby/lean-proofs, commit " + REVISION
        + ".\nThe source header records its original environment; this project uses"
        + " the committed lean-toolchain and lake-manifest.json.\n"
        + "Original authors and mathematical provenance are retained above. -/\n\n"
    )
    finite = (
        header + provenance
        + "import Mathlib.Algebra.Group.Pointwise.Set.BigOperators\n"
        + "import Mathlib.Algebra.Order.BigOperators.Group.Finset\n"
        + "import Mathlib.Tactic.Ring\nimport Mathlib.Tactic.SplitIfs\n"
        + "import Util.Density\n\n"
        + between(source, "open Filter Function", "/-! ## Consequences of the asymptotic-basis hypothesis")
        + between(source, "lemma eventually_large_prefix_of_infinite", "lemma basis_prefix_card_lower_bound")
        + between(source, "lemma partialDensity_nat_eq_prefix_card", "/-!\n## Erdős Problem 339")
        + "\nend Erdos339\n"
    )
    # The sole compatibility change to the reused finite proof in Lean 4.32.1.
    old = "    simpa [B] using b.property"
    if finite.count(old) != 1:
        raise ValueError("Expected exactly one source-selection compatibility site")
    finite = finite.replace(old, "    obtain ⟨n, _, hn⟩ := Finset.mem_image.mp b.property\n    exact ⟨n, hn⟩")
    lower = (
        header + provenance
        + "import Erdos339.Finite\nimport Erdos339.Basis\n\n"
        + "open Filter Function\nopen scoped Pointwise BigOperators\n\nnamespace Erdos339\n\n"
        + between(source, "lemma infinite_of_isAsymptoticAddBasisOfOrder", "lemma eventually_large_prefix_of_infinite")
        + between(source, "lemma basis_prefix_card_lower_bound", "lemma partialDensity_nat_eq_prefix_card")
        + between(source, "/-!\n## Erdős Problem 339", "\nend Erdos339")
        + "\nend Erdos339\n"
    )
    write_generated("Finite.lean", finite)
    write_generated("LowerDensity.lean", lower)


if __name__ == "__main__":
    main()
