# The same question as symsearch, put to a SAT solver: is there an m x n 0/1 matrix with at least T ones, no 3x3 block
# of ones, and (optionally) invariant under a group acting on rows and columns? Every matrix the solver returns is
# checked again by an independent program.
#
# Encoding: a variable per cell; for every triple of rows (a, b, c) and column j, y = 1 is forced when the three rows
# all have a one in column j, and at most two of the y of a triple may be 1; at least T cells are 1 (a cardinality
# encoding); a group is imposed by making all the cells of an orbit equal. Rows and columns may also be ordered
# lexicographically to break the symmetry of relabelling — only when no group is imposed.
#   .venv/bin/python satclass.py <matrix.json> <T> [aut|none] [--lex] [--count N]
import itertools, json, pathlib, sys, time
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from structure import load
from rigid import all_automorphisms

def k33_free(M):
    m, n = len(M), len(M[0])
    cols = [frozenset(i for i in range(m) if M[i][j]) for j in range(n)]
    return all(len(cols[a] & cols[b] & cols[c]) <= 2 for a, b, c in itertools.combinations(range(n), 3))

def lex_geq(pool, clauses, xs, ys, tag):
    """xs >= ys lexicographically (lists of literals, most significant first), by the usual chain of equalities."""
    eq_prev = None
    for k, (x, y) in enumerate(zip(xs, ys)):
        e = pool.id(("eq", tag, k))
        # while all before are equal, x must not be below y
        cond = [] if eq_prev is None else [-eq_prev]
        clauses.append(cond + [x, -y])
        # e <-> (prefix equal and x == y)
        if eq_prev is None:
            clauses += [[-e, x, -y], [-e, -x, y], [e, x, y], [e, -x, -y]]
        else:
            clauses += [[-e, eq_prev], [-e, x, -y], [-e, -x, y], [e, -eq_prev, x, y], [e, -eq_prev, -x, -y]]
        eq_prev = e

def build(m, n, T, group=None, lex=False, broken=False, columns=False, reps=False):
    # ordering rows and columns is sound for the full problem (Flener et al., CP 2002), not together with a group
    if group and lex: raise ValueError("lexicographic ordering and an imposed group do not mix")
    pool = IDPool()
    v = lambda i, j: pool.id(("x", i, j))
    for i in range(m):
        for j in range(n): v(i, j)
    clauses = []
    if not broken:
        triples = list(itertools.combinations(range(m), 3))
        if reps and group:
            # an invariant matrix needs the condition for one triple of each orbit of triples only
            seen, keep = set(), []
            for t in triples:
                if t in seen: continue
                keep.append(t)
                seen |= {tuple(sorted(g[0][x] for x in t)) for g in group}
            triples = keep
        for a, b, c in triples:
            ys = []
            for j in range(n):
                y = pool.id(("y", a, b, c, j)); ys.append(y)
                clauses.append([-v(a, j), -v(b, j), -v(c, j), y])
            clauses += CardEnc.atmost(lits=ys, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses
    if columns and not broken:
        ctriples = list(itertools.combinations(range(n), 3))
        if reps and group:
            seen, keep = set(), []
            for t in ctriples:
                if t in seen: continue
                keep.append(t)
                seen |= {tuple(sorted(g[1][x] for x in t)) for g in group}
            ctriples = keep
        for p_, q_, r_ in ctriples:
            zs = []
            for i in range(m):
                z = pool.id(("z", p_, q_, r_, i)); zs.append(z)
                clauses.append([-v(i, p_), -v(i, q_), -v(i, r_), z])
            clauses += CardEnc.atmost(lits=zs, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses
    cells = [v(i, j) for i in range(m) for j in range(n)]
    clauses += CardEnc.atleast(lits=cells, bound=T, vpool=pool, encoding=EncType.totalizer).clauses
    if group:
        seen = set()
        for i in range(m):
            for j in range(n):
                if (i, j) in seen: continue
                orb = sorted({(g[0][i], g[1][j]) for g in group}); seen |= set(orb)
                r = v(*orb[0])
                for cell in orb[1:]:
                    clauses += [[-v(*cell), r], [v(*cell), -r]]
    if lex:
        for i in range(m - 1): lex_geq(pool, clauses, [v(i, j) for j in range(n)], [v(i + 1, j) for j in range(n)], ("row", i))
        for j in range(n - 1): lex_geq(pool, clauses, [v(i, j) for i in range(m)], [v(i, j + 1) for i in range(m)], ("col", j))
    return pool, clauses, v

def solve(m, n, T, group=None, lex=False, count=1, broken=False, solver="cadical153"):
    pool, clauses, v = build(m, n, T, group, lex, broken)
    start = time.time(); found = []
    with Solver(name=solver, bootstrap_with=clauses) as s:
        while len(found) < count and s.solve():
            model = set(l for l in s.get_model() if l > 0)
            M = [[1 if v(i, j) in model else 0 for j in range(n)] for i in range(m)]
            found.append(M)
            s.add_clause([-v(i, j) if M[i][j] else v(i, j) for i in range(m) for j in range(n)])
    return found, round(time.time() - start, 1), len(clauses)

if __name__ == "__main__":
    M = load(sys.argv[1]); T = int(sys.argv[2])
    mode = sys.argv[3] if len(sys.argv) > 3 and not sys.argv[3].startswith("--") else "aut"
    lex = "--lex" in sys.argv
    count = int(sys.argv[sys.argv.index("--count") + 1]) if "--count" in sys.argv else 1
    group = all_automorphisms(M) if mode == "aut" else None
    found, took, size = solve(len(M), len(M[0]), T, group, lex, count, broken="--broken" in sys.argv)
    ok = all(k33_free(X) and sum(map(sum, X)) >= T for X in found)
    print(json.dumps({"cell": f"{len(M)}x{len(M[0])}", "T": T, "symmetry": f"Aut, order {len(group)}" if group else "none", "lex": lex,
                      "clauses": size, "found": len(found), "all checked": ok, "seconds": took, "ones": sorted({sum(map(sum, X)) for X in found})}))
