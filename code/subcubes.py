# Sub-cubes of an anchor cube (anchor_cubes.py), for cubes whose proof would not fit in memory. In the canonical form
# of the lean formula the rows are in lexicographic order with column 0 the most significant, so once columns 0..k-1
# are known the rows fall into groups with equal entries in those columns, each group consecutive and in lexicographic
# order of the remaining columns: column k has its ones at the start of every group, and is known from its count in
# each group. Fixing columns 1..depth this way splits a cube into sub-cubes that together cover it. Only necessary
# conditions prune the counts:
#   - column k has the degree of its class, and its count in the anchor's rows is one of the values the pattern still
#     leaves for its class after the columns fixed before it;
#   - no three rows lie in three of the fixed columns: for every pair of fixed columns, column k holds at most two of
#     the rows the pair shares;
#   - a column of the same degree as the column before it is not lexicographically larger (equal-degree columns are in
#     lexicographic order, column 0 included).
#   .venv/bin/python subcubes.py count <m> <n> <T> <profile json> <cube> <depth>
import itertools, json, pathlib, sys
from collections import Counter

def options(m, profile, pattern, depth):
    """Every admissible choice of the supports of columns 1..depth, as tuples of row tuples."""
    c = profile[0]; col0 = tuple(range(c))
    out = []
    def vec(support):
        return tuple(1 if r in support else 0 for r in range(m))
    def rec(k, groups, supports, used):
        if k > depth:
            out.append(tuple(supports[1:])); return
        d = profile[k]; left = Counter(pattern[d]) - used[d]
        pairs = list(itertools.combinations(range(len(groups[0][1])), 2))
        for counts in itertools.product(*[range(len(rows) + 1) for rows, _ in groups]):
            if sum(counts) != d: continue
            inside = sum(nk for nk, (rows, v) in zip(counts, groups) if v[0] == 1)
            if left[inside] == 0: continue
            if any(sum(nk for nk, (rows, v) in zip(counts, groups) if v[p] and v[q]) > 2 for p, q in pairs): continue
            support = tuple(sorted(r for nk, (rows, v) in zip(counts, groups) for r in rows[:nk]))
            if profile[k - 1] == d and vec(support) > vec(supports[-1]): continue
            split = [g for nk, (rows, v) in zip(counts, groups) for g in ((rows[:nk], v + (1,)), (rows[nk:], v + (0,))) if g[0]]
            rec(k + 1, split, supports + [support], {**used, d: used[d] + Counter([inside])})
    rec(1, [(col0, (1,)), (tuple(range(c, m)), (0,))], [col0], {d: Counter() for d in set(profile)})
    return out

def extensions(m, profile, pattern, prefix, depth):
    """The options of the given depth whose first len(prefix) columns are `prefix` (same conditions as options(),
    without enumerating the other branches)."""
    c = profile[0]; col0 = tuple(range(c)); out = []
    def vec(support):
        return tuple(1 if r in support else 0 for r in range(m))
    groups = [(col0, (1,)), (tuple(range(c, m)), (0,))]; supports = [col0]
    used = {d: Counter() for d in set(profile)}
    for k, support in enumerate(prefix, start=1):              # replay the prefix: the same splits as in options()
        S = set(support); inside = sum(1 for r in support if r < c)
        groups = [g for rows, v in groups for g in ((tuple(r for r in rows if r in S), v + (1,)), (tuple(r for r in rows if r not in S), v + (0,))) if g[0]]
        supports.append(tuple(support)); used = {**used, profile[k]: used[profile[k]] + Counter([inside])}
    def rec(k, groups, supports, used):
        if k > depth:
            out.append(tuple(supports[1:])); return
        d = profile[k]; left = Counter(pattern[d]) - used[d]
        pairs = list(itertools.combinations(range(len(groups[0][1])), 2))
        for counts in itertools.product(*[range(len(rows) + 1) for rows, _ in groups]):
            if sum(counts) != d: continue
            inside = sum(nk for nk, (rows, v) in zip(counts, groups) if v[0] == 1)
            if left[inside] == 0: continue
            if any(sum(nk for nk, (rows, v) in zip(counts, groups) if v[p] and v[q]) > 2 for p, q in pairs): continue
            support = tuple(sorted(r for nk, (rows, v) in zip(counts, groups) for r in rows[:nk]))
            if profile[k - 1] == d and vec(support) > vec(supports[-1]): continue
            split = [g for nk, (rows, v) in zip(counts, groups) for g in ((rows[:nk], v + (1,)), (rows[nk:], v + (0,))) if g[0]]
            rec(k + 1, split, supports + [support], {**used, d: used[d] + Counter([inside])})
    rec(len(prefix) + 1, groups, supports, used)
    return out

def units(m, n, supports):
    """Unit literals fixing columns 1..len(supports): x(r, j) = r*n + j + 1, as in the lean formula."""
    return [(r * n + j + 1) * (1 if r in support else -1) for j, support in enumerate(supports, start=1) for r in range(m)]

if __name__ == "__main__":
    m, n, T = map(int, sys.argv[2:5]); profile = tuple(json.loads(sys.argv[5])); cube, depth = int(sys.argv[6]), int(sys.argv[7])
    folder = pathlib.Path(__file__).resolve().parent / "certificates" / f"z{m}x{n}-ge{T}" / f"anchor-{'-'.join(map(str, profile))}"
    pattern = {int(d): tuple(ms) for d, ms in json.loads((folder / "patterns.json").read_text())[cube].items()}
    print(json.dumps({"cube": cube, "pattern": {str(d): list(ms) for d, ms in pattern.items()}, "depth": depth,
                      "sub-cubes": len(options(m, profile, pattern, depth))}))
