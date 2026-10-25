# Structure of K_{3,3}-free 0/1 matrices: invariants, isomorphism (rows to rows, columns to columns) and the order of
# the automorphism group, by colour refinement with individualisation. Standard library only.
import itertools, json, pathlib, re
from collections import Counter

def load(path):
    return json.loads(pathlib.Path(path).read_text())

def graph(M):
    """The bipartite graph of M: vertices 0..m-1 are the rows, m..m+n-1 the columns; colour 0 rows, 1 columns."""
    m, n = len(M), len(M[0])
    adj = [[] for _ in range(m + n)]
    for i in range(m):
        for j in range(n):
            if M[i][j]:
                adj[i].append(m + j); adj[m + j].append(i)
    return adj, [0] * m + [1] * n

def refine_pair(adjG, cG, adjH, cH):
    """Refines two colourings together, naming colours alike in both. None when they stop matching."""
    while True:
        sG = [(cG[v], tuple(sorted(cG[u] for u in adjG[v]))) for v in range(len(adjG))]
        sH = [(cH[v], tuple(sorted(cH[u] for u in adjH[v]))) for v in range(len(adjH))]
        names = {s: i for i, s in enumerate(sorted(set(sG) | set(sH)))}
        nG, nH = [names[s] for s in sG], [names[s] for s in sH]
        if Counter(nG) != Counter(nH): return None
        if len(set(nG)) == len(set(cG)): return nG, nH
        cG, cH = nG, nH

def individualise(c, v):
    d = list(c); d[v] = max(c) + 1
    return d

def find_iso(adjG, cG, adjH, cH):
    """A map f with f(G) = H respecting the colours, or None."""
    r = refine_pair(adjG, cG, adjH, cH)
    if r is None: return None
    cG, cH = r
    sizes = Counter(cG)
    if all(k == 1 for k in sizes.values()):
        where = {c: w for w, c in enumerate(cH)}
        f = [where[cG[v]] for v in range(len(adjG))]
        setsH = [set(a) for a in adjH]
        return f if all(f[u] in setsH[f[v]] for v in range(len(adjG)) for u in adjG[v]) else None
    target = min((k, c) for c, k in sizes.items() if k > 1)[1]
    v = next(x for x in range(len(adjG)) if cG[x] == target)
    for w in (x for x in range(len(adjH)) if cH[x] == target):
        f = find_iso(adjG, individualise(cG, v), adjH, individualise(cH, w))
        if f is not None: return f
    return None

def aut_order(adj, c):
    """|Aut| by orbit and stabiliser: the orbit of a vertex times the order of its stabiliser."""
    c = refine_pair(adj, c, adj, c)[0]
    sizes = Counter(c)
    if all(k == 1 for k in sizes.values()): return 1
    target = min((k, col) for col, k in sizes.items() if k > 1)[1]
    cls = [x for x in range(len(adj)) if c[x] == target]
    v = cls[0]; cv = individualise(c, v)
    orbit = sum(1 for w in cls if find_iso(adj, cv, adj, individualise(c, w)) is not None)
    return orbit * aut_order(adj, cv)

def isomorphic(A, B):
    if (len(A), len(A[0])) != (len(B), len(B[0])): return False
    (aG, cG), (aH, cH) = graph(A), graph(B)
    return find_iso(aG, cG, aH, cH) is not None

def automorphisms(M):
    adj, c = graph(M)
    return aut_order(adj, c)

def invariants(M):
    m, n = len(M), len(M[0])
    rows = [sum(r) for r in M]; cols = [sum(c) for c in zip(*M)]
    rsets = [frozenset(j for j in range(n) if M[i][j]) for i in range(m)]
    csets = [frozenset(i for i in range(m) if M[i][j]) for j in range(n)]
    row_triples = Counter(len(rsets[a] & rsets[b] & rsets[c]) for a, b, c in itertools.combinations(range(m), 3))
    col_triples = Counter(len(csets[a] & csets[b] & csets[c]) for a, b, c in itertools.combinations(range(n), 3))
    row_pairs = Counter(len(rsets[a] & rsets[b]) for a, b in itertools.combinations(range(m), 2))
    col_pairs = Counter(len(csets[a] & csets[b]) for a, b in itertools.combinations(range(n), 2))
    c4 = sum((k * (k - 1) // 2) * v for k, v in row_pairs.items())
    return {
        "ones": sum(rows), "rows": dict(sorted(Counter(rows).items())), "cols": dict(sorted(Counter(cols).items())),
        # a row triple lies in at most two columns; how many lie in 0, 1, 2 — and the slack of the packing count
        "row_triples": dict(sorted(row_triples.items())), "col_triples": dict(sorted(col_triples.items())),
        "row_pair_codegrees": dict(sorted(row_pairs.items())), "col_pair_codegrees": dict(sorted(col_pairs.items())),
        "c4": c4,
    }

def best_by_cell(folder, pattern=r"z-(\d+)-(\d+)-(\d+)\.json"):
    best = {}
    for path in pathlib.Path(folder).glob("*.json"):
        hit = re.fullmatch(pattern, path.name)
        if not hit: continue
        m, n, k = map(int, hit.groups())
        if k > best.get((m, n), (0, None))[0]: best[m, n] = (k, path)
    return {cell: load(path) for cell, (k, path) in best.items()}
