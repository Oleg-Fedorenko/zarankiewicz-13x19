# The rigid best matrices, taken apart: every automorphism listed and checked on the matrix, the group named by its
# order, element orders and commutativity, the orbits of rows and columns, and the tactical decomposition — for each
# row orbit and column orbit, how many ones a row of the one has in the other and a column of the other in the one.
#   python3 rigid.py        -> rigid.json and a summary
import itertools, json, pathlib, sys
from collections import Counter
HERE = pathlib.Path(__file__).resolve().parent
TOP = HERE.parent
sys.path.insert(0, str(HERE))
from structure import load, graph, refine_pair, individualise, automorphisms

def all_automorphisms(M):
    """Every automorphism as (row permutation, column permutation), each checked entry by entry."""
    m, n = len(M), len(M[0]); adj, c = graph(M)
    out = []
    def walk(cG, cH):
        r = refine_pair(adj, cG, adj, cH)
        if r is None: return
        cG, cH = r
        sizes = Counter(cG)
        if all(k == 1 for k in sizes.values()):
            where = {col: w for w, col in enumerate(cH)}
            f = [where[cG[v]] for v in range(m + n)]
            rp, cp = tuple(f[:m]), tuple(x - m for x in f[m:])
            if all(M[rp[i]][cp[j]] == M[i][j] for i in range(m) for j in range(n)): out.append((rp, cp))
            return
        target = min((k, col) for col, k in sizes.items() if k > 1)[1]
        v = next(x for x in range(m + n) if cG[x] == target)
        for w in (x for x in range(m + n) if cH[x] == target):
            walk(individualise(cG, v), individualise(cH, w))
    walk(c, c)
    return sorted(set(out))

def compose(a, b):  # a after b
    return tuple(a[0][i] for i in b[0]), tuple(a[1][j] for j in b[1])
def order(g, identity):
    k, x = 1, g
    while x != identity: x = compose(g, x); k += 1
    return k
def name_group(G):
    n = len(G); identity = (tuple(range(len(G[0][0]))), tuple(range(len(G[0][1]))))
    orders = Counter(order(g, identity) for g in G)
    abelian = all(compose(a, b) == compose(b, a) for a in G for b in G)
    if n == 1: return "trivial"
    if max(orders) == n: return f"Z{n}"
    if n == 4: return "Z2×Z2"
    if n == 6: return "Z6" if abelian else "S3"
    if n == 8:
        if abelian: return "Z4×Z2" if 4 in orders else "Z2×Z2×Z2"
        return "D4" if orders[2] == 5 else "Q8"
    if n == 10: return "Z10" if abelian else "D5"
    if n == 12: return f"order 12 ({'abelian' if abelian else 'non-abelian'}, element orders {dict(sorted(orders.items()))})"
    return f"order {n} ({'abelian' if abelian else 'non-abelian'}, element orders {dict(sorted(orders.items()))})"

def orbits(perms, size):
    parent = list(range(size))
    def root(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for p in perms:
        for x in range(size):
            a, b = root(x), root(p[x])
            if a != b: parent[b] = a
    groups = {}
    for x in range(size): groups.setdefault(root(x), []).append(x)
    return sorted(groups.values(), key=lambda g: (len(g), g))

def tactical(M, R, C):
    """For each row orbit and column orbit: ones per row of the row orbit inside the column orbit (if constant), and
    ones per column; None where it is not constant (then the decomposition is not tactical)."""
    rows = [[sorted({sum(M[i][j] for j in c) for i in r}) for c in C] for r in R]
    cols = [[sorted({sum(M[i][j] for i in r) for j in c}) for c in C] for r in R]
    return rows, cols

TARGETS = [("15x23", 156), ("16x22", 158), ("14x19", 128), ("15x19", 136), ("13x21", 131), ("16x17", 132), ("16x20", 147)]

def rigid_pool():
    """Every different best matrix of each rigid cell, from all sources, by canonical form."""
    from canon import canon
    pool = {}
    for folder in [TOP / "found", HERE / "borsik-matrices", HERE / "norris-witnesses", TOP / "found3", HERE / "derived"] + sorted((HERE / "harvest").glob("*")):
        for path in folder.glob("*.json"):
            M = load(path); key = f"{len(M)}x{len(M[0])}"
            pool.setdefault((key, sum(map(sum, M))), {}).setdefault(canon(M)[0], M)
    return pool

if __name__ == "__main__":
    pool = rigid_pool(); report = {}
    for key, k in TARGETS:
        for idx, M in enumerate(pool.get((key, k), {}).values()):
            G = all_automorphisms(M)
            assert len(G) == automorphisms(M), (key, len(G))
            R = orbits([g[0] for g in G], len(M)); C = orbits([g[1] for g in G], len(M[0]))
            rows, cols = tactical(M, R, C)
            is_tactical = all(len(x) == 1 for line in rows for x in line) and all(len(x) == 1 for line in cols for x in line)
            report[f"{key} {k} #{idx}"] = {"group": name_group(G), "order": len(G), "row orbits": [len(r) for r in R], "column orbits": [len(c) for c in C],
                                           "tactical": is_tactical, "ones per row in each column orbit": [[x[0] if len(x) == 1 else x for x in line] for line in rows]}
            print(f"{key} {k} #{idx}: |Aut| {len(G)} = {name_group(G)} | row orbits {[len(r) for r in R]} | column orbits {[len(c) for c in C]} | tactical {is_tactical}", flush=True)
    (HERE / "rigid.json").write_text(json.dumps(report, indent=1))
