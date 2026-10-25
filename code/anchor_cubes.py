# Anchor cubes (proposed by GLM on 2026-10-19), measured before use. In the canonical form of the lean formula the first
# column B has the largest degree c and, rows being in lexicographic order with B the most significant column, occupies
# the first c rows. For every other column j let i_j = |col_j ∩ B| and o_j = c_j - i_j. Every K3,3-free matrix satisfies
#   (I)   Σ C(i_j,3) <= C(c,3)             (each triple inside B lies in B and in at most one more column)
#   (II)  Σ C(o_j,3) <= 2 C(13-c,3)        (triples outside B)
#   (III) Σ C(i_j,2) o_j <= 2 C(c,2)(13-c) (two rows in B, one outside)
#   (IV)  Σ i_j C(o_j,2) <= 2 c C(13-c,2)  (one row in B, two outside)
# and the row cuts bound Σ i_j = (ones in the rows of B) - c: rows hold >= cut1 ones and, when cut2 = 2 cut1 + 1, at most
# one row holds exactly cut1, so the c rows of B hold >= c(cut1+1) - 1 and the other rows >= (m-c)(cut1+1) - 1.
# A pattern = for each degree class of the other columns, the multiset of their i_j. A cube = the lean formula plus
# "B is the first c rows" plus, per class and per threshold t, the number of class columns with i_j >= t (two AtMost
# constraints over upward totalizers, so nothing is assumed beyond the pattern).
#   .venv/bin/python anchor_cubes.py count <m> <n> <T> <profile json> [<SImin> <SImax>]
#   .venv/bin/python anchor_cubes.py run <m> <n> <T> <profile json> <seconds per cube> <workers> <out.json>
import itertools, json, math, multiprocessing, pathlib, subprocess, sys, time
from collections import Counter
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from pysat.card import CardEnc, EncType, ITotalizer
from pysat.formula import CNF
import satprofile
from satlean import case_formula_lean

KISSAT = HERE / "tools" / "kissat-src" / "arminbiere-kissat-8af8e56" / "build" / "kissat"

def window(m, T, c, cuts):
    c1 = cuts.get(1, 0); two = cuts.get(2, 0) >= 2 * c1 + 1
    inside = c * (c1 + 1) - 1 if two else c * c1
    outside = (m - c) * (c1 + 1) - 1 if two else (m - c) * c1
    return inside - c, (T - outside) - c

def patterns(m, profile, c, lo, hi):
    others = list(profile); others.remove(c)
    caps = (math.comb(c, 3), 2 * math.comb(m - c, 3), 2 * math.comb(c, 2) * (m - c), 2 * c * math.comb(m - c, 2))
    classes = sorted(Counter(others).items(), reverse=True)
    out = []
    def options(d, cnt):
        vals = [i for i in range(0, min(d, c) + 1) if d - i <= m - c]
        return list(itertools.combinations_with_replacement(vals, cnt))
    per = [(d, options(d, cnt)) for d, cnt in classes]
    def rec(k, acc, sums, si):
        if any(s > cap for s, cap in zip(sums, caps)) or si > hi: return
        if k == len(per):
            if lo <= si <= hi: out.append(dict(acc))
            return
        d, opts = per[k]
        for ms in opts:
            add = [sum(math.comb(i, 3) for i in ms), sum(math.comb(d - i, 3) for i in ms),
                   sum(math.comb(i, 2) * (d - i) for i in ms), sum(i * math.comb(d - i, 2) for i in ms)]
            rec(k + 1, acc + [(d, ms)], [a + b for a, b in zip(sums, add)], si + sum(ms))
    rec(0, [], [0, 0, 0, 0], 0)
    return out

def cube_formula(m, n, T, profile, kcuts, pattern, mixed=False):
    pool, clauses, v, info = case_formula_lean(m, n, T, profile, kcuts, mixed=mixed)
    clauses = list(clauses); c = profile[0]
    for r in range(m): clauses.append([v(r, 0)] if r < c else [-v(r, 0)])
    for d, ms in pattern.items():
        cols = [j for j in range(1, n) if profile[j] == d]
        assert len(cols) == len(ms)
        up, down = {}, {}
        for j in cols:
            t1 = ITotalizer(lits=[v(r, j) for r in range(c)], ubound=c, top_id=pool.top); clauses += t1.cnf.clauses; pool.top = t1.top_id
            t2 = ITotalizer(lits=[-v(r, j) for r in range(c)], ubound=c, top_id=pool.top); clauses += t2.cnf.clauses; pool.top = t2.top_id
            up[j], down[j] = t1.rhs, t2.rhs
        for t in range(1, c + 1):
            a_t = sum(1 for i in ms if i >= t)                        # class columns with i_j >= t
            b_t = len(ms) - a_t                                       # class columns with i_j <= t-1
            # at most a_t columns with >= t ones in B's rows: up[j][t-1] is forced by ">= t ones"
            if a_t < len(cols):
                clauses += CardEnc.atmost(lits=[up[j][t - 1] for j in cols], bound=a_t, vpool=pool, encoding=EncType.seqcounter).clauses
            # at most b_t columns with <= t-1 ones, i.e. >= c-t+1 zeros: down[j][c-t] is forced by that
            if b_t < len(cols):
                clauses += CardEnc.atmost(lits=[down[j][c - t] for j in cols], bound=b_t, vpool=pool, encoding=EncType.seqcounter).clauses
    return pool, clauses

def run_cube(args):
    m, n, T, profile, kcuts, idx, pattern, limit, work = args
    pool, clauses = cube_formula(m, n, T, profile, kcuts, {int(d): tuple(ms) for d, ms in pattern.items()})
    cnf = pathlib.Path(work) / f"cube-{idx:05d}.cnf"; CNF(from_clauses=clauses).to_file(str(cnf))
    start = time.time()
    try:
        r = subprocess.run([str(KISSAT), "-q", "-n", "--unsat", f"--time={limit}", str(cnf)], capture_output=True, text=True, timeout=limit + 60)
        code = r.returncode
    except subprocess.TimeoutExpired:
        code = -1
    cnf.unlink(missing_ok=True)
    verdict = {10: "SAT", 20: "UNSAT"}.get(code, "unknown")
    return {"cube": idx, "pattern": pattern, "verdict": verdict, "seconds": round(time.time() - start, 1)}

if __name__ == "__main__":
    mode = sys.argv[1]; m, n, T = map(int, sys.argv[2:5]); profile = tuple(json.loads(sys.argv[5]))
    cuts = {k: T - satprofile.upper(m - k, n) for k in (1, 2, 3) if satprofile.upper(m - k, n) is not None}
    c = profile[0]
    if mode == "count":
        lo, hi = (int(sys.argv[6]), int(sys.argv[7])) if len(sys.argv) > 7 else window(m, T, c, cuts)
        ps = patterns(m, profile, c, lo, hi)
        print(json.dumps({"profile": list(profile), "anchor": c, "window": [lo, hi], "cuts": cuts, "patterns": len(ps)}))
    else:
        limit, workers = int(sys.argv[6]), int(sys.argv[7]); out = HERE / sys.argv[8]
        lo, hi = window(m, T, c, cuts)
        ps = patterns(m, profile, c, lo, hi)
        work = HERE / "symwork" / "anchor-cubes"; work.mkdir(parents=True, exist_ok=True)
        todo = [(m, n, T, profile, 3, i, {str(d): list(ms) for d, ms in p.items()}, limit, str(work)) for i, p in enumerate(ps)]
        head = {"profile": list(profile), "anchor": c, "window": [lo, hi], "cubes": len(ps), "limit": limit}
        print(json.dumps(head), flush=True)
        results = []; t0 = time.time()
        with multiprocessing.Pool(workers) as pool:
            for r in pool.imap_unordered(run_cube, todo):
                results.append(r); out.write_text(json.dumps({**head, "results": results}))
                if r["verdict"] != "UNSAT": print(json.dumps(r), flush=True)
        secs = [r["seconds"] for r in results]
        print(json.dumps({"done": len(results), "UNSAT": sum(r["verdict"] == "UNSAT" for r in results),
                          "SAT": sum(r["verdict"] == "SAT" for r in results), "unknown": sum(r["verdict"] == "unknown" for r in results),
                          "sum seconds": round(sum(secs)), "max": max(secs), "wall": round(time.time() - t0)}), flush=True)
