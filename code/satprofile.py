# The full question split by degree profile (the method of the certificate papers): a matrix with exactly T ones —
# enough, since deleting ones keeps a matrix K3,3-free — has some multiset of column degrees; each multiset allowed by
# the counting conditions is a case of its own, solved separately and in parallel.
#
# Counting conditions (all necessary): every triple of rows lies in at most two columns, so sum_j C(c_j, 3) <= 2 C(m, 3);
# the k-line cuts: any k columns hold at least T - z(m, n - k) ones (z from table.py's upper bounds), so the k smallest
# column degrees sum to at least that. Symmetry breaking in a case: columns sorted by degree, non-increasing (fixed by
# the case), columns of equal degree in non-increasing lexicographic order, rows in non-increasing lexicographic order
# — every matrix can be brought to that form (each swap raises the matrix read row by row), so no matrix is lost.
#   .venv/bin/python satprofile.py <m> <n> <T> <k> <seconds per case> <workers> [--first N]   -> profiles-<m>x<n>-<T>.json
import itertools, json, math, multiprocessing, pathlib, sys, time
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from satfull import upper
from satclass import k33_free, lex_geq

C3 = lambda x: math.comb(x, 3)

def column_profiles(m, n, T):
    b = {k: T - upper(m, n - k) for k in range(1, n) if upper(m, n - k) is not None and T - upper(m, n - k) > 0}
    lo = max(0, b.get(1, 0)); cap = 2 * C3(m); out = []
    def rec(prefix, remaining, left, top):
        if left == 0:
            if remaining == 0:
                d = sorted(prefix)
                if sum(C3(x) for x in d) <= cap and all(sum(d[:k]) >= v for k, v in b.items()): out.append(tuple(prefix))
            return
        for x in range(min(top, remaining - lo * (left - 1)), lo - 1, -1):
            if x * left < remaining: break
            rec(prefix + [x], remaining - x, left - 1, x)
    rec([], T, n, m)
    return out, b

def case_formula(m, n, T, profile, kmax):
    pool = IDPool(); v = lambda i, j: pool.id(("x", i, j))
    for i in range(m):
        for j in range(n): v(i, j)
    clauses = []
    for a, b, c in itertools.combinations(range(m), 3):
        ys = []
        for j in range(n):
            y = pool.id(("y", a, b, c, j)); ys.append(y)
            clauses.append([-v(a, j), -v(b, j), -v(c, j), y])
        clauses += CardEnc.atmost(lits=ys, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses
    for j, d in enumerate(profile):
        clauses += CardEnc.equals(lits=[v(i, j) for i in range(m)], bound=d, vpool=pool, encoding=EncType.seqcounter).clauses
    # rows: the k-row cuts
    for k in range(1, kmax + 1):
        U = upper(m - k, n)
        if U is None or T - U <= 0: continue
        for S in itertools.combinations(range(m), k):
            clauses += CardEnc.atleast(lits=[v(i, j) for i in S for j in range(n)], bound=T - U, vpool=pool, encoding=EncType.seqcounter).clauses
    # symmetry: rows lexicographic; columns of equal degree lexicographic
    for i in range(m - 1): lex_geq(pool, clauses, [v(i, j) for j in range(n)], [v(i + 1, j) for j in range(n)], ("row", i))
    for j in range(n - 1):
        if profile[j] == profile[j + 1]:
            lex_geq(pool, clauses, [v(i, j) for i in range(m)], [v(i, j + 1) for i in range(m)], ("col", j))
    return pool, clauses, v

def _case(args):
    m, n, T, profile, kmax, limit = args
    import threading
    pool, clauses, v = case_formula(m, n, T, profile, kmax)
    start = time.time()
    with Solver(name="glucose4", bootstrap_with=clauses) as s:   # glucose can be interrupted; CaDiCaL cannot
        timer = threading.Timer(limit, s.interrupt); timer.start()
        r = s.solve_limited(expect_interrupt=True); timer.cancel()
        took = round(time.time() - start, 1)
        if r is None: return {"profile": profile, "verdict": "time ran out", "seconds": took}
        if r is False: return {"profile": profile, "verdict": "UNSAT", "seconds": took}
        model = set(l for l in s.get_model() if l > 0)
        M = [[1 if v(i, j) in model else 0 for j in range(n)] for i in range(m)]
        return {"profile": profile, "verdict": "SAT", "seconds": took, "matrix": M, "checked": k33_free(M) and sum(map(sum, M)) == T}

if __name__ == "__main__":
    m, n, T, kmax, limit, workers = map(int, sys.argv[1:7])
    first = int(sys.argv[sys.argv.index("--first") + 1]) if "--first" in sys.argv else None
    profiles, b = column_profiles(m, n, T)
    if first: profiles = profiles[:first]
    out = HERE / f"profiles-{m}x{n}-{T}.json"
    print(json.dumps({"cell": f"{m}x{n}", "T": T, "column cuts": b, "profiles": len(profiles)}), flush=True)
    results = []
    with multiprocessing.Pool(workers) as p:
        for r in p.imap_unordered(_case, [(m, n, T, prof, kmax, limit) for prof in profiles]):
            results.append(r)
            out.write_text(json.dumps({"cell": f"{m}x{n}", "T": T, "k": kmax, "column cuts": b, "results": results}, indent=1))
            print(json.dumps({k: v for k, v in r.items() if k != "matrix"}), flush=True)
            if r["verdict"] == "SAT" and r.get("checked"):
                (HERE / "symwork" / f"PROFILE-SAT-{m}x{n}-{T}.json").write_text(json.dumps(r["matrix"]))
    tally = {v: sum(1 for r in results if r["verdict"] == v) for v in ("UNSAT", "SAT", "time ran out")}
    print(json.dumps({"done": len(results), **tally}), flush=True)
