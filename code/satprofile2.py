# The finer split for the column profiles satprofile could not decide: each is split again by row profile, so that a
# case fixes the degree of every row and every column. A row profile must satisfy the same counting conditions as a
# column profile (sum_i C(r_i, 3) <= 2 C(n, 3); the k smallest row degrees hold at least T - z(m - k, n)), and the pair
# must satisfy the Gale-Ryser condition (a 0/1 matrix with those row and column sums exists at all).
# Symmetry breaking in a case: rows sorted by degree and columns sorted by degree (both fixed by the case), rows of equal
# degree and columns of equal degree in non-increasing lexicographic order — reachable from any matrix with those
# degrees by swaps that raise the matrix read row by row, so no matrix is lost.
#   .venv/bin/python satprofile2.py <m> <n> <T> <seconds per case> <workers> <column profiles json>
import itertools, json, math, multiprocessing, pathlib, sys, threading, time
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from satfull import upper
from satclass import k33_free, lex_geq

def row_profiles(m, n, T, kmax=None):
    """kmax limits the k-row cuts to k <= kmax, so that the profiles rest on fewer published values (None: every k the table has)."""
    ks = range(1, m if kmax is None else min(m, kmax + 1))
    b = {k: T - upper(m - k, n) for k in ks if upper(m - k, n) is not None and T - upper(m - k, n) > 0}
    lo = max(0, b.get(1, 0)); cap = 2 * math.comb(n, 3); out = []
    def rec(prefix, remaining, left, top):
        if left == 0:
            if remaining == 0:
                d = sorted(prefix)
                if sum(math.comb(x, 3) for x in d) <= cap and all(sum(d[:k]) >= v for k, v in b.items()): out.append(tuple(prefix))
            return
        for x in range(min(top, remaining - lo * (left - 1)), lo - 1, -1):
            if x * left < remaining: break
            rec(prefix + [x], remaining - x, left - 1, x)
    rec([], T, m, n)
    return out

def gale_ryser(rows, cols):
    """A 0/1 matrix with row sums rows and column sums cols exists (both non-increasing, equal totals)."""
    if sum(rows) != sum(cols): return False
    for k in range(1, len(rows) + 1):
        if sum(rows[:k]) > sum(min(c, k) for c in cols): return False
    return True

def case_formula(m, n, rows, cols):
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
    for i, d in enumerate(rows):
        clauses += CardEnc.equals(lits=[v(i, j) for j in range(n)], bound=d, vpool=pool, encoding=EncType.seqcounter).clauses
    for j, d in enumerate(cols):
        clauses += CardEnc.equals(lits=[v(i, j) for i in range(m)], bound=d, vpool=pool, encoding=EncType.seqcounter).clauses
    for i in range(m - 1):
        if rows[i] == rows[i + 1]: lex_geq(pool, clauses, [v(i, j) for j in range(n)], [v(i + 1, j) for j in range(n)], ("row", i))
    for j in range(n - 1):
        if cols[j] == cols[j + 1]: lex_geq(pool, clauses, [v(i, j) for i in range(m)], [v(i, j + 1) for i in range(m)], ("col", j))
    return pool, clauses, v

def _case(args):
    m, n, rows, cols, limit = args
    pool, clauses, v = case_formula(m, n, rows, cols)
    start = time.time()
    with Solver(name="glucose4", bootstrap_with=clauses) as s:
        timer = threading.Timer(limit, s.interrupt); timer.start()
        r = s.solve_limited(expect_interrupt=True); timer.cancel()
        took = round(time.time() - start, 1)
        base = {"rows": rows, "columns": cols, "seconds": took}
        if r is None: return {**base, "verdict": "time ran out"}
        if r is False: return {**base, "verdict": "UNSAT"}
        model = set(l for l in s.get_model() if l > 0)
        M = [[1 if v(i, j) in model else 0 for j in range(n)] for i in range(m)]
        return {**base, "verdict": "SAT", "matrix": M, "checked": k33_free(M) and sum(map(sum, M)) == sum(rows)}

if __name__ == "__main__":
    m, n, T, limit, workers = map(int, sys.argv[1:6])
    columns = [tuple(p) for p in json.loads(sys.argv[6])]
    rows_all = row_profiles(m, n, T)
    cases = [(m, n, r, c, limit) for c in columns for r in rows_all if gale_ryser(r, c)]
    out = HERE / f"profiles2-{m}x{n}-{T}.json"
    print(json.dumps({"cell": f"{m}x{n}", "T": T, "column profiles": len(columns), "row profiles": len(rows_all), "cases after Gale-Ryser": len(cases)}), flush=True)
    results = []
    with multiprocessing.Pool(workers) as p:
        for r in p.imap_unordered(_case, cases):
            results.append(r)
            if len(results) % 50 == 0 or r["verdict"] != "UNSAT":
                out.write_text(json.dumps({"cell": f"{m}x{n}", "T": T, "results": results}, indent=1))
                print(json.dumps({k: v for k, v in r.items() if k != "matrix"}), flush=True)
            if r["verdict"] == "SAT" and r.get("checked"):
                (HERE / "symwork" / f"PROFILE2-SAT-{m}x{n}-{T}.json").write_text(json.dumps(r["matrix"]))
    out.write_text(json.dumps({"cell": f"{m}x{n}", "T": T, "results": results}, indent=1))
    tally = {v: sum(1 for r in results if r["verdict"] == v) for v in ("UNSAT", "SAT", "time ran out")}
    print(json.dumps({"done": len(results), **tally}), flush=True)
