# Block C: the full question for a cell, with no symmetry assumed — is there an m x n K3,3-free matrix with T ones?
# Rows and columns are ordered lexicographically (sound for row and column symmetry: Flener et al., CP 2002), and the
# degrees are bounded below by the deletion argument: deleting the lightest column of a matrix with T ones leaves a
# matrix of the cell (m, n-1), so that column has at least T - z(m, n-1) ones, and every column has at least as many;
# the same for rows with z(m-1, n). The bounds z used are the closed upper bounds of table.py — the cuts are only as
# good as the literature they come from, and each run records which values it used.
#   .venv/bin/python satfull.py <m> <n> <T> [seconds] [--no-cuts] [--k K]
import itertools, json, multiprocessing, pathlib, sys, time
HERE = pathlib.Path(__file__).resolve().parent
TOP = HERE.parent
sys.path.insert(0, str(HERE)); sys.path.insert(0, str(TOP))
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
from satclass import build, k33_free

def upper(m, n):
    """The closed upper bound of z(m, n; 3, 3) from table.py, symmetric in m and n; None outside its table."""
    from table import frontier
    lo, hi, src, printed = frontier()
    for key in ((m, n), (n, m)):
        if key in hi: return hi[key]
    return None

def formula(m, n, T, cuts=True, kmax=1):
    pool, clauses, v = build(m, n, T, None, lex=True)
    used = {}
    # deleting ANY k rows leaves a matrix of the cell (m-k, n): so every set of k rows holds at least T - z(m-k, n)
    # ones, and the same for columns. k = 1 is the cut below; larger k adds one cardinality constraint per set.
    for k in range(2, kmax + 1):
        zr, zc = upper(m - k, n), upper(m, n - k)
        if zr is not None and T - zr > 0:
            used[f"z({m - k},{n}) <= {zr}"] = f"every {k} rows hold at least {T - zr} ones"
            for S in itertools.combinations(range(m), k):
                clauses += CardEnc.atleast(lits=[v(i, j) for i in S for j in range(n)], bound=T - zr, vpool=pool, encoding=EncType.seqcounter).clauses
        if zc is not None and T - zc > 0:
            used[f"z({m},{n - k}) <= {zc}"] = f"every {k} columns hold at least {T - zc} ones"
            for S in itertools.combinations(range(n), k):
                clauses += CardEnc.atleast(lits=[v(i, j) for i in range(m) for j in S], bound=T - zc, vpool=pool, encoding=EncType.seqcounter).clauses
    if cuts:
        zc, zr = upper(m, n - 1), upper(m - 1, n)
        if zc is not None and T - zc > 0:
            used[f"z({m},{n - 1}) <= {zc}"] = f"every column has at least {T - zc} ones"
            for j in range(n): clauses += CardEnc.atleast(lits=[v(i, j) for i in range(m)], bound=T - zc, vpool=pool, encoding=EncType.seqcounter).clauses
        if zr is not None and T - zr > 0:
            used[f"z({m - 1},{n}) <= {zr}"] = f"every row has at least {T - zr} ones"
            for i in range(m): clauses += CardEnc.atleast(lits=[v(i, j) for j in range(n)], bound=T - zr, vpool=pool, encoding=EncType.seqcounter).clauses
    return pool, clauses, v, used

def _solve(args, queue):
    m, n, T, cuts, solver, kmax = args
    pool, clauses, v, used = formula(m, n, T, cuts, kmax)
    with Solver(name=solver, bootstrap_with=clauses) as s:
        if s.solve():
            model = set(l for l in s.get_model() if l > 0)
            queue.put(("SAT", [[1 if v(i, j) in model else 0 for j in range(n)] for i in range(m)], used, len(clauses)))
        else:
            queue.put(("UNSAT", None, used, len(clauses)))

def ask(m, n, T, limit, cuts=True, solver="cadical153", kmax=1):
    queue = multiprocessing.Queue()
    proc = multiprocessing.Process(target=_solve, args=((m, n, T, cuts, solver, kmax), queue))
    start = time.time(); proc.start()
    try:
        verdict, M, used, size = queue.get(timeout=limit)
    except Exception:
        proc.terminate(); proc.join()
        return {"cell": f"{m}x{n}", "T": T, "k": kmax, "verdict": "time ran out", "seconds": limit, "cuts": cuts}
    proc.join()
    out = {"cell": f"{m}x{n}", "T": T, "k": kmax, "verdict": verdict, "seconds": round(time.time() - start, 1), "cuts": used, "clauses": size}
    if M is not None:
        out["checked"] = k33_free(M) and sum(map(sum, M)) >= T
        (HERE / "symwork" / f"FULL-{m}x{n}-{T}.json").write_text(json.dumps(M))
    return out

if __name__ == "__main__":
    m, n, T = map(int, sys.argv[1:4])
    limit = int(sys.argv[4]) if len(sys.argv) > 4 else 3600
    kmax = int(sys.argv[sys.argv.index("--k") + 1]) if "--k" in sys.argv else 1
    print(json.dumps(ask(m, n, T, limit, cuts="--no-cuts" not in sys.argv, kmax=kmax)), flush=True)
