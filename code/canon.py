# An independent check of isomorphism: the canonical form — the smallest relabelled matrix over every leaf of the
# individualisation tree. Two matrices are isomorphic exactly when their canonical forms are equal.
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from structure import *
def leaves(adj, c, out):
    c = refine_pair(adj, c, adj, c)[0]
    sizes = Counter(c)
    if all(k == 1 for k in sizes.values()): out.append(c); return
    target = min((k, col) for col, k in sizes.items() if k > 1)[1]
    for v in [x for x in range(len(adj)) if c[x] == target]:
        leaves(adj, individualise(c, v), out)
def canon(M):
    m, n = len(M), len(M[0]); adj, c = graph(M); out = []; leaves(adj, c, out)
    best = None
    for col in out:
        rows = sorted(range(m), key=lambda i: col[i]); cols = sorted(range(n), key=lambda j: col[m + j])
        form = "".join("".join(str(M[i][j]) for j in cols) for i in rows)
        if best is None or form < best: best = form
    return best, len(out)
if __name__ == "__main__":
    ours, borsik, norris = best_by_cell(sys.argv[2]), best_by_cell(sys.argv[3]), best_by_cell(sys.argv[4])
    disagree = 0
    for cell in sorted(ours):
        srcs = {k: v for k, v in (("ours", ours.get(cell)), ("Borsik", borsik.get(cell)), ("Norris", norris.get(cell))) if v is not None}
        forms = {k: canon(v)[0] for k, v in srcs.items()}
        names = list(srcs)
        for i, a in enumerate(names):
            for b in names[i + 1:]:
                if sum(map(sum, srcs[a])) != sum(map(sum, srcs[b])): continue
                by_canon, by_search = forms[a] == forms[b], isomorphic(srcs[a], srcs[b])
                disagree += by_canon != by_search
                if by_canon: print(cell, f"{a} = {b}")
    print("disagreements between the two methods:", disagree)
