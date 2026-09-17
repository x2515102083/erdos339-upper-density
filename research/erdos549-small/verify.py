"""Auxiliary exact checks of the 35-vertex witness; not a substitute for Lean."""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)

def blue(u: int, v: int) -> bool:
    a, x = divmod(u, 7)
    b, y = divmod(v, 7)
    return u != v and (a == b or (x != y and ((a + 1) % 5 == b or (b + 1) % 5 == a)))

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('results.json'))
    args = parser.parse_args()
    vertices = set(range(35))
    N = [{v for v in vertices if blue(u, v)} for u in range(35)]
    R = [vertices - N[u] - {u} for u in range(35)]
    edges = [(u, v) for u, v in combinations(range(35), 2) if blue(u, v)]
    require(all(blue(u, v) == blue(v, u) for u in vertices for v in vertices), 'Asymmetry')
    require(all(u not in N[u] for u in vertices), 'Loop')
    require(all(len(s) == 18 for s in N), 'Blue degree')
    require(all(len(s) == 16 for s in R), 'Red degree')
    histogram = Counter(len(N[u] | N[v]) for u, v in edges)
    require(histogram == {21: 105, 26: 210}, 'Neighbor-union histogram')
    # Independent set construction of the same blue graph.
    second = set()
    for a in range(5):
        second.update(tuple(sorted((7*a+x, 7*a+y))) for x, y in combinations(range(7), 2))
        second.update(tuple(sorted((7*a+x, 7*((a+1)%5)+y)))
                      for x in range(7) for y in range(7) if x != y)
    require(second == set(edges), 'Independent graph definitions disagree')
    # Tree left vertices 0..8, right vertices 9..26; centers 0 and 9.
    tree_edges = {(i, 9+j) for i in range(9) for j in range(18) if i == 0 or j == 0}
    require(len(tree_edges) == 26, 'Tree edge count')
    reached = {0}
    while True:
        enlarged = reached | {x for u, v in tree_edges for x in (u, v) if u in reached or v in reached}
        if enlarged == reached:
            break
        reached = enlarged
    require(reached == set(range(27)), 'Disconnected tree')
    result = dict(vertices=35, k=9, tree_vertices=27, tree_edges=26,
                  bipartition=[9, 18], tree_leaves=[17, 8], blue_edges=len(edges),
                  blue_degree=18, red_degree=16,
                  blue_edge_neighbor_union_histogram=dict(sorted(histogram.items())),
                  claim='Exact auxiliary witness checks; the full non-induced-containment proof is in Lean')
    output = json.dumps(result, indent=2) + '\n'
    args.output.write_text(output, encoding='utf-8')
    print(output, end='')

if __name__ == '__main__':
    main()
