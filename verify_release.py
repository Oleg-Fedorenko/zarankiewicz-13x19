# Standalone verifier of the certificate that z(13,19;3,3) <= 120, from this repository alone (no proofs needed).
#
# Every formula is generated here with the upper bounds of Collins, Riasanovsky, Wallace and Radziszowski (2016,
# Table 4), closed under the deletion lemma, plus z(12,18) <= 108 — itself checked below. Then:
#   1. bounds    the eight bounds the formulas use follow from that closure;
#   2. 12 x 18   at 109 ones, with Collins's bounds only, there is one column profile, (7, 6^17); its formula, generated
#                here, has the SHA-256 of the formula that Glucose refuted and drat-trim verified (data/z12x18-109.json);
#   3. profiles  the column profiles of 13 x 19 at 121 are 30; the 26 decided whole: formula SHA-256 = the certified
#                one, and the record says drat-trim VERIFIED (data/profiles-whole.json);
#   4. cubes     for each of the four other profiles (data/anchor/{A,B,C,D}): the anchor patterns, enumerated here, are
#                the stored list; a cube decided whole has the certified formula's SHA-256 and a verified proof; a cube
#                split into sub-cubes is covered — every option of the deepest depth used, enumerated here, has a prefix
#                among its certified sub-cubes — and each sub-cube is certified: a Farkas vector checked here in exact
#                arithmetic against the linear system rebuilt here, or a formula with the certified SHA-256 whose proof
#                drat-trim, or lrat-check-strict while it was written, verified;
#   5. witness   witness/z-13-19-120.txt is 13 x 19 with 120 ones and no 3 x 3 block of ones, and each of the 18
#                matrices of the neighbouring cells has its stated size and number of ones and no such block.
# With --resolve N, N solver parts drawn at random are solved again (CaDiCaL with its LRAT proof streamed into
# lrat-check-strict, which first has to refuse a bogus proof of a satisfiable formula); tools/BUILD.md builds both.
#   python3 verify_release.py [--workers K] [--resolve N] [--only A,B,C,D]
import gzip, hashlib, io, json, multiprocessing, os, pathlib, random, re, subprocess, sys, tempfile
ROOT = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "code"))
from pysat.formula import CNF
import satprofile, satfull
from collins import closure
from anchor_cubes import patterns, window, cube_formula
import subcubes, subcube_lp

M, N, T = 13, 19, 121
HI = closure({(12, 18): 108})
def upper(a, b):
    return HI.get((a, b), HI.get((b, a)))
def collins_only(a, b):
    lone = closure({})
    return lone.get((a, b), lone.get((b, a)))

def use(bounds):
    satprofile.upper = bounds; satfull.upper = bounds

def sha(clauses):
    buf = io.StringIO(); CNF(from_clauses=clauses).to_fp(buf); return hashlib.sha256(buf.getvalue().encode()).hexdigest()

PROFILES = {"A": [8, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], "B": [8, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5],
            "C": [7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5], "D": [7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6]}
STRICT = re.compile(r"^lrat-check-strict \(sha256 [0-9a-f]{16}\)")

def solver_ok(r):
    """A solver record counts only as UNSAT with drat-trim's VERIFIED, or with lrat-check-strict's (named by hash)."""
    return r.get("verdict") == "UNSAT" and (r.get("drat-trim") == "VERIFIED" or
                                            (r.get("lrat-check") == "VERIFIED" and bool(STRICT.match(r.get("checker", "")))))

def check_cube(args):
    """One cube of an anchor profile; returns (cube, problems, counts)."""
    key, cube, subs = args
    use(upper)
    prof = PROFILES[key]; pat = {int(d): tuple(ms) for d, ms in cube["pattern"].items()}; idx = cube["cube"]
    problems, counts = [], {"whole": 0, "farkas": 0, "sat": 0, "lrat": 0}
    if cube["route"] == "whole":
        r = cube["record"]; mx = r.get("encoding") == "lean+mixed"
        if not solver_ok(r): problems.append("whole cube not verified")
        if sha(cube_formula(M, N, T, prof, 3, pat, mixed=mx)[1]) != cube["cnf sha256"]: problems.append("whole cube CNF differs")
        counts["whole"] = 1
        return idx, problems, counts
    listed = {tuple(tuple(s) for s in sb["supports"]) for sb in subs}
    if len(listed) != cube["sub-cubes"]: problems.append("sub-cube count differs from the cube record")
    depth = max(len(s) for s in listed)
    uncovered = [o for o in subcubes.options(M, prof, pat, depth) if not any(o[:k] in listed for k in range(1, depth + 1))]
    if uncovered: problems.append(f"{len(uncovered)} options not covered")
    floor = subcube_lp.row_floor(M, N, T, prof, upper)
    base = {mx: list(cube_formula(M, N, T, prof, 3, pat, mixed=mx)[1]) for mx in (False, True)}
    for sb in subs:
        sup = [list(s) for s in sb["supports"]]
        if sb["route"] in ("farkas", "farkas-dense"):
            c = sb["certificate"]
            if sb["route"] == "farkas":
                cut1, vec = c["cut1"], c["certificate"]
                A, b, names, E, e = (lambda t: (t[1], t[2], t[3], t[4], t[5]))(subcube_lp.build(M, N, T, cut1, prof, pat, sup))
                good = cut1 == floor and subcube_lp.verify_sparse(A, b, E, e, vec)
            else:
                cut1 = c["cut1"]
                A, b, names, E, e = (lambda t: (t[1], t[2], t[3], t[4], t[5]))(subcube_lp.build(M, N, T, cut1, prof, pat, sup))
                good = cut1 == floor and subcube_lp.verify(A, b, E, e, c)
            if not good: problems.append(f"Farkas certificate refused at {sup}")
            counts["farkas"] += 1
        elif sb["route"] == "sat":
            r = sb["record"]; mx = r.get("encoding") == "lean+mixed"
            if not solver_ok(r): problems.append(f"sub-cube not verified at {sup}")
            if sha(base[mx] + [[u] for u in subcubes.units(M, N, sup)]) != sb["cnf sha256"]: problems.append(f"sub-cube CNF differs at {sup}")
            counts["sat"] += 1; counts["lrat"] += r.get("lrat-check") == "VERIFIED"
        else:
            problems.append(f"sub-cube without a certificate at {sup}")
    return idx, problems, counts

def resolve(parts, k, cadical, checker):
    """Solve k random parts again with CaDiCaL, its LRAT proof checked while written; the checker first must refuse a
    bogus proof of a satisfiable formula ("3 0 0" for {x1, x1 or x2})."""
    with tempfile.TemporaryDirectory() as tmp:
        t = pathlib.Path(tmp); (t / "s.cnf").write_text("p cnf 2 2\n1 0\n1 2 0\n"); (t / "p.lrat").write_text("3 0 0\n")
        d = subprocess.run([checker, str(t / "s.cnf"), str(t / "p.lrat")], capture_output=True, text=True)
        if d.returncode == 0 and re.search(r"^c VERIFIED$", d.stdout, re.M): return {"error": "the checker verifies a bogus proof: not the strict one"}
    out = {}
    for name, clauses in random.Random(1219).sample(parts, min(k, len(parts))):
        with tempfile.TemporaryDirectory() as tmp:
            t = pathlib.Path(tmp); cnf = t / "f.cnf"; CNF(from_clauses=clauses).to_file(str(cnf)); fifo = t / "p.lrat"; os.mkfifo(fifo)
            with open(t / "chk.txt", "w") as log:
                chk = subprocess.Popen([checker, str(cnf), str(fifo)], stdout=log, stderr=subprocess.STDOUT)
                sol = subprocess.run([cadical, "-q", "--lrat=true", "--binary=false", str(cnf), str(fifo)], stdout=subprocess.DEVNULL)
                chk.wait()
            said = (t / "chk.txt").read_text()
            out[name] = "VERIFIED" if sol.returncode == 20 and chk.returncode == 0 and re.search(r"^c VERIFIED$", said, re.M) else f"solver {sol.returncode}, checker {chk.returncode}"
        print(json.dumps({"re-solved": name, "result": out[name]}), flush=True)
    return out

if __name__ == "__main__":
    workers = int(sys.argv[sys.argv.index("--workers") + 1]) if "--workers" in sys.argv else os.cpu_count()
    only = sys.argv[sys.argv.index("--only") + 1].split(",") if "--only" in sys.argv else list(PROFILES)
    report, bad = {}, []
    def check(name, ok, detail=None):
        report[name] = {"ok": bool(ok), **({"detail": detail} if detail is not None else {})}
        print(("ok  " if ok else "FAIL"), name, "" if detail is None else json.dumps(detail), flush=True)
        if not ok: bad.append(name)
    # 1. the bounds the formulas use, from Collins's table and z(12,18) <= 108
    used = {"z(13,18)": 116, "z(13,17)": 110, "z(13,16)": 107, "z(12,19)": 114, "z(11,19)": 106, "z(10,19)": 98, "z(12,18)": 108, "z(11,17)": 96}
    got = {k: upper(*map(int, k[2:-1].split(","))) for k in used}
    check("1. bounds follow from Collins et al. + z(12,18) <= 108", got == used, got)
    # 2. the 12 x 18 link, with Collins's bounds alone
    use(collins_only)
    p12, _ = satprofile.column_profiles(12, 18, 109)
    link = json.loads((ROOT / "data" / "z12x18-109.json").read_text())[0]
    s12 = sha(satprofile.case_formula(12, 18, 109, tuple(p12[0]), 3)[1]) if len(p12) == 1 else None
    check("2. z(12,18) <= 108: one profile (7,6^17), CNF hash, drat-trim VERIFIED",
          [list(p) for p in p12] == [[7] + [6] * 17] and s12 == link["cnf sha256"] and link["record"].get("drat-trim") == "VERIFIED",
          {"profiles": [list(p) for p in p12]})
    # 3. the 30 profiles of 13 x 19 at 121; the 26 decided whole
    use(upper)
    profs, cuts = satprofile.column_profiles(M, N, T)
    whole = json.loads((ROOT / "data" / "profiles-whole.json").read_text())
    names = {tuple(r["profile"]) for r in whole} | {tuple(p) for p in PROFILES.values()}
    check("3a. 30 profiles, each certified whole or by anchor cubes", len(profs) == 30 and {tuple(p) for p in profs} == names, {"profiles": len(profs)})
    errs = [r["profile"] for r in whole if not (r["variant"] == "plain" and r["record"].get("drat-trim") == "VERIFIED"
            and sha(satprofile.case_formula(M, N, T, tuple(r["profile"]), 3)[1]) == r["cnf sha256"])]
    check("3b. the 26 whole profiles: CNF hashes equal, drat-trim VERIFIED", len(whole) == 26 and not errs, {"refused": errs})
    # 4. the four anchor profiles
    sat_parts = []
    with multiprocessing.Pool(workers, initializer=use, initargs=(upper,)) as pool:
        for key in only:
            d = ROOT / "data" / "anchor" / key; prof = PROFILES[key]; c = prof[0]
            ccuts = {k: T - upper(M - k, N) for k in (1, 2, 3)}; lo, hi = window(M, T, c, ccuts)
            listed = json.loads((d / "patterns.json").read_text())
            fresh = [{str(dd): list(ms) for dd, ms in p.items()} for p in patterns(M, prof, c, lo, hi)]
            check(f"4{key}. patterns enumerated here = the stored list", listed == fresh, {"patterns": len(fresh)})
            cubes = [json.loads(l) for l in open(d / "cubes.jsonl")]
            subs = {}
            for l in open(d / "subcubes.jsonl"):
                r = json.loads(l); subs.setdefault(r["cube"], []).append(r)
            with gzip.open(d / "farkas.jsonl.gz", "rt") as g:
                certs = {(x["cube"], tuple(tuple(s) for s in x["supports"])): x for x in map(json.loads, g)}
            for idx, rs in subs.items():
                for r in rs:
                    if r["route"] in ("farkas", "farkas-dense"):
                        x = certs.get((idx, tuple(tuple(s) for s in r["supports"])))
                        r["certificate"] = x["certificate"] if x else None
                        if x is None: r["route"] = "missing"
            pats_ok = [cb["pattern"] == listed[cb["cube"]] for cb in cubes]
            jobs = [(key, cb, subs.get(cb["cube"], [])) for cb in cubes]
            problems, totals = [], {"whole": 0, "farkas": 0, "sat": 0, "lrat": 0}
            for n_done, (idx, pr, cnt) in enumerate(pool.imap_unordered(check_cube, jobs, chunksize=1), start=1):
                problems += [(idx, p) for p in pr]
                for k2 in totals: totals[k2] += cnt[k2]
                if n_done % 100 == 0: print(f"   {key}: {n_done}/{len(jobs)} cubes", flush=True)
            check(f"4{key}. {len(cubes)} cubes: every one certified, covered and matching", len(cubes) == len(listed) and all(pats_ok) and not problems,
                  {**totals, "problems": problems[:20], "number of problems": len(problems)})
            if "--resolve" in sys.argv:
                for cb in cubes:
                    for r in subs.get(cb["cube"], []):
                        if r["route"] == "sat":
                            pat = {int(dd): tuple(ms) for dd, ms in cb["pattern"].items()}; mx = r["record"].get("encoding") == "lean+mixed"
                            sat_parts.append((f"{key}/cube-{cb['cube']}/{r['supports']}", (key, pat, mx, r["supports"])))
    # 5. the witnesses: the 120-matrix of 13 x 19, and the 18 neighbouring cells (witness/README.md)
    import itertools
    def admissible(path, m, n, ones):
        rows = [list(map(int, l.strip())) for l in open(path) if l.strip()]
        if len(rows) != m or any(len(r) != n or set(r) - {0, 1} for r in rows) or sum(map(sum, rows)) != ones: return False
        R_ = [frozenset(j for j, x in enumerate(r) if x) for r in rows]; C_ = [frozenset(i for i in range(m) if rows[i][j]) for j in range(n)]
        return all(len(a & b & c) < 3 for a, b, c in itertools.combinations(R_, 3)) and all(len(a & b & c) < 3 for a, b, c in itertools.combinations(C_, 3))
    check("5. witness: 13 x 19, 120 ones, no 3 x 3 block of ones", admissible(ROOT / "witness" / "z-13-19-120.txt", 13, 19, 120))
    others = sorted(p for p in (ROOT / "witness").glob("z-*.txt") if p.name != "z-13-19-120.txt")
    refused = [p.name for p in others if not admissible(p, *map(int, p.stem.split("-")[1:4]))]
    check(f"5b. {len(others)} witnesses of the neighbouring cells, each admissible with the stated number of ones", len(others) == 18 and not refused, {"refused": refused})
    if "--resolve" in sys.argv:
        k = int(sys.argv[sys.argv.index("--resolve") + 1]); tools = ROOT / "tools"
        drawn = random.Random(2610).sample(sat_parts, min(k, len(sat_parts)))
        built = [(name, list(cube_formula(M, N, T, PROFILES[key], 3, pat, mixed=mx)[1]) + [[u] for u in subcubes.units(M, N, sup)]) for name, (key, pat, mx, sup) in drawn]
        res = resolve(built, k, str(tools / "cadical"), str(tools / "lrat-check-strict"))
        check(f"6. {len(built)} random solver parts solved again and checked", res and all(v == "VERIFIED" for v in res.values()), res)
    (ROOT / "verify-report.json").write_text(json.dumps(report, indent=1))
    print("ALL CHECKS PASSED" if not bad else f"FAILED: {bad}", flush=True)
    sys.exit(0 if not bad else 1)
