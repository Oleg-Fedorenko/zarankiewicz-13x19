# The audit of one column profile certified by anchor cubes (certify_anchor.py, certify_subcubes.py,
# certify_deferred.py): the list of patterns is enumerated again and must equal the kept patterns.json; every cube has
# a result — UNSAT with drat-trim VERIFIED (a whole cube), or UNSAT by sub-cubes, or UNSAT with lrat-check VERIFIED;
# every kept CNF (case.cnf.gz) is rebuilt from the generator and compared byte for byte; for a cube split into
# sub-cubes, the options of the deepest depth used are enumerated again and every one of them must lie in a verified
# sub-cube (itself or a prefix). With --recheck N, drat-trim is run again on N kept proofs chosen at random (seeded);
# a sub-cube checked by streamed LRAT (certify_anchor.solve_lrat) kept no proof, and --recheck-lrat N solves N of them
# again (chosen at random, seeded) with the proof checked while it is written.
#   .venv/bin/python audit_anchor.py <m> <n> <T> <profile json> [--extra m,n,v ...] [--recheck N] [--recheck-lrat N]
#                                    [--root <dir>]
# --root (for tests): a tree standing for this folder; then only the cubes present there are looked at.
import gzip, hashlib, io, json, pathlib, random, re, shutil, subprocess, sys, tempfile
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from pysat.formula import CNF
import satprofile
from certify_anchor import patch, extra_from, solve_lrat, fingerprint, LRATCHECK
from anchor_cubes import patterns, window, cube_formula
import subcubes, subcube_lp

DRATTRIM = HERE / "tools" / "drat-trim" / "drat-trim"

def dimacs(clauses):
    buf = io.StringIO(); CNF(from_clauses=clauses).to_fp(buf); return buf.getvalue().encode()

def same_cnf(clauses, folder):
    with gzip.open(folder / "case.cnf.gz", "rb") as f: kept = f.read()
    return hashlib.sha256(dimacs(clauses)).digest() == hashlib.sha256(kept).digest()

def recheck(folder):
    with tempfile.TemporaryDirectory(dir=HERE / "symwork") as tmp:
        cnf = pathlib.Path(tmp) / "case.cnf"; proof = pathlib.Path(tmp) / "case.drat"
        for src, dst in ((folder / "case.cnf.gz", cnf), (folder / "case.drat.gz", proof)):
            with gzip.open(src, "rb") as a, open(dst, "wb") as b: shutil.copyfileobj(a, b, 1 << 20)
        d = subprocess.run([str(DRATTRIM), str(cnf), str(proof), "-t", "200000"], capture_output=True, text=True)
        return "VERIFIED" if re.search(r"^s VERIFIED", d.stdout, re.M) else ("NOT VERIFIED" if "NOT VERIFIED" in d.stdout else "no verdict")

def strict_checker():
    """The sha256 prefix of the streamed LRAT checker, after it has shown it is the strict one: it must refuse a bogus
    proof of a satisfiable formula (an empty clause with no conflict, which drat-trim's own lrat-check accepts) and
    accept a real refutation. None when it fails either test."""
    with tempfile.TemporaryDirectory(dir=HERE / "symwork") as tmp:
        t = pathlib.Path(tmp); runs = []
        for cnf, proof in (("p cnf 2 2\n1 0\n1 2 0\n", "3 0 0\n"), ("p cnf 1 2\n1 0\n-1 0\n", "3 0 1 2 0\n")):
            (t / "f.cnf").write_text(cnf); (t / "p.lrat").write_text(proof)
            d = subprocess.run([str(LRATCHECK), str(t / "f.cnf"), str(t / "p.lrat")], capture_output=True, text=True)
            runs.append(d.returncode == 0 and re.search(r"^c VERIFIED$", d.stdout, re.M) is not None)
    return fingerprint(LRATCHECK) if runs == [False, True] else None

def lrat_row_ok(row, strict):
    return strict is not None and row.get("checker", "").startswith(f"lrat-check-strict (sha256 {strict})")

def recheck_lrat(folder):
    with tempfile.TemporaryDirectory(dir=HERE / "symwork") as tmp:
        cnf = pathlib.Path(tmp) / "case.cnf"
        with gzip.open(folder / "case.cnf.gz", "rb") as a, open(cnf, "wb") as b: shutil.copyfileobj(a, b, 1 << 20)
        code, _, verdict, _, _ = solve_lrat(cnf)
        return verdict if code == 20 else f"solver exit {code}"

if __name__ == "__main__":
    patch()
    m, n, T = map(int, sys.argv[1:4]); profile = tuple(json.loads(sys.argv[4]))
    cuts = {k: T - satprofile.upper(m - k, n) for k in (1, 2, 3) if satprofile.upper(m - k, n) is not None}
    c = profile[0]; lo, hi = window(m, T, c, cuts); ps = patterns(m, profile, c, lo, hi)
    rel = pathlib.Path("certificates") / f"z{m}x{n}-ge{T}" / f"anchor-{'-'.join(map(str, profile))}"
    base = pathlib.Path(sys.argv[sys.argv.index("--root") + 1]) if "--root" in sys.argv else HERE
    folder = base / rel; subroot = base / f"{rel}-sub"
    listed = json.loads((folder / "patterns.json").read_text())
    same_list = listed == [{str(d): list(ms) for d, ms in p.items()} for p in ps]
    problems, kinds, proofs, streamed_parts = [], {"whole": 0, "sub-cubes": 0, "lrat": 0}, [], []
    strict = strict_checker()                                   # LRAT rows are trusted only from this tested binary
    sub_count = 0
    for idx, p in enumerate(ps):
        cube = folder / f"cube-{idx:05d}"; res_path = cube / "result.json"
        if "--root" in sys.argv and not cube.exists(): continue
        if not res_path.exists(): problems.append((idx, "no result")); continue
        res = json.loads(res_path.read_text())
        if json.loads((cube / "pattern.json").read_text()) != {str(d): list(ms) for d, ms in p.items()}:
            problems.append((idx, "pattern.json differs")); continue
        if res.get("verdict") != "UNSAT": problems.append((idx, f"verdict {res.get('verdict')}")); continue
        if res.get("route") == "sub-cubes":
            kinds["sub-cubes"] += 1
            subs = {tuple(tuple(s) for s in sub) for sub in res["sub-cubes"]}
            depth = max(len(s) for s in subs)
            uncovered = [o for o in subcubes.options(m, profile, p, depth) if not any(o[:k] in subs for k in range(1, depth + 1))]
            if uncovered: problems.append((idx, f"{len(uncovered)} options not covered")); continue
            base_cl = {mx: cube_formula(m, n, T, profile, 3, p, mixed=mx)[1] for mx in (False, True)}
            jl, fj = {}, subroot / f"cube-{idx:05d}" / "farkas.jsonl"
            if fj.exists():
                for line in fj.read_text().splitlines():
                    if line.strip():
                        rr = json.loads(line); jl[tuple(tuple(x) for x in rr["supports"])] = rr
            floor = subcube_lp.row_floor(m, n, T, profile, satprofile.upper)
            for sub in sorted(subs):
                sf = subroot / f"cube-{idx:05d}" / ("d{}-".format(len(sub)) + "_".join("-".join(map(str, s)) for s in sub))
                if not (sf / "result.json").exists() and sub in jl:
                    # a Farkas line: rebuild the sub-cube's linear system from the generator, check the sparse vector
                    rr = jl[sub]; var, A, b, names, E, e, groups, size = subcube_lp.build(m, n, T, rr["cut1"], profile, p, [list(x) for x in sub])
                    good = rr["cut1"] == floor and rr.get("farkas") == "VERIFIED" and subcube_lp.verify_sparse(A, b, E, e, rr["certificate"])
                    kinds["farkas sub-cubes"] = kinds.get("farkas sub-cubes", 0) + 1
                    if not good: problems.append((idx, f"sub-cube {sf.name} Farkas line refused"))
                    sub_count += 1; continue
                r = json.loads((sf / "result.json").read_text()) if (sf / "result.json").exists() else {}
                if r.get("verdict") == "UNSAT" and r.get("route") == "farkas":
                    # rebuild the sub-cube's linear system from the generator and check the stored vector exactly
                    cert = json.loads((sf / "farkas.json").read_text())
                    var, A, b, names, E, e, groups, size = subcube_lp.build(m, n, T, cert["cut1"], profile, p, [list(s) for s in sub])
                    good = cert["cut1"] == subcube_lp.row_floor(m, n, T, profile, satprofile.upper) and subcube_lp.verify(A, b, E, e, cert)
                    kinds["farkas sub-cubes"] = kinds.get("farkas sub-cubes", 0) + 1
                    if not good: problems.append((idx, f"sub-cube {sf.name} Farkas certificate refused"))
                    sub_count += 1; continue
                streamed = r.get("lrat-check") == "VERIFIED"           # CaDiCaL's LRAT checked while written: no proof kept
                if r.get("verdict") != "UNSAT" or not (r.get("drat-trim") == "VERIFIED" or streamed): problems.append((idx, f"sub-cube {sf.name} not verified")); continue
                if streamed and not lrat_row_ok(r, strict): problems.append((idx, f"sub-cube {sf.name} not checked by the tested strict checker")); continue
                mx = r.get("encoding") == "lean+mixed"; kinds["mixed sub-cubes"] = kinds.get("mixed sub-cubes", 0) + mx
                if not same_cnf(list(base_cl[mx]) + [[u] for u in subcubes.units(m, n, sub)], sf): problems.append((idx, f"sub-cube {sf.name} CNF differs"))
                if streamed: kinds["lrat sub-cubes"] = kinds.get("lrat sub-cubes", 0) + 1; streamed_parts.append(sf)
                else: proofs.append(sf)
                sub_count += 1
        elif res.get("drat-trim") == "VERIFIED":
            kinds["whole"] += 1; mx = res.get("encoding") == "lean+mixed"; kinds["mixed whole"] = kinds.get("mixed whole", 0) + mx
            if not same_cnf(cube_formula(m, n, T, profile, 3, p, mixed=mx)[1], cube): problems.append((idx, "CNF differs"))
            proofs.append(cube)
        elif res.get("lrat-check") == "VERIFIED":
            kinds["lrat"] += 1; mx = res.get("encoding") == "lean+mixed"
            if not lrat_row_ok(res, strict): problems.append((idx, "not checked by the tested strict checker"))
            if not same_cnf(cube_formula(m, n, T, profile, 3, p, mixed=mx)[1], cube): problems.append((idx, "CNF differs"))
            streamed_parts.append(cube)
        else:
            problems.append((idx, "not verified"))
    summary = {"cell": f"{m}x{n}", "T": T, "profile": list(profile), "window": [lo, hi], "cuts": cuts,
               "extra": {f"z({a},{b})": v for (a, b), v in extra_from(sys.argv).items()},
               "cubes": len(ps), "patterns.json equal to a fresh enumeration": same_list, "certified": kinds,
               "strict LRAT checker (sha256, after its self-test)": strict,
               "sub-cubes checked": sub_count, "problems": problems[:50], "number of problems": len(problems)}
    if "--recheck" in sys.argv:
        k = int(sys.argv[sys.argv.index("--recheck") + 1]); rng = random.Random(1219)
        picked = rng.sample(proofs, min(k, len(proofs)))
        summary["recheck"] = {str(f.relative_to(base)): recheck(f) for f in picked}
    if "--recheck-lrat" in sys.argv:                            # no proof was kept: solve again and check while it is written
        k = int(sys.argv[sys.argv.index("--recheck-lrat") + 1]); rng = random.Random(1219)
        summary["recheck lrat"] = {str(f.relative_to(base)): recheck_lrat(f) for f in rng.sample(streamed_parts, min(k, len(streamed_parts)))}
    print(json.dumps(summary), flush=True)
    (base / f"audit-anchor-{m}x{n}-{T}-{'-'.join(map(str, profile))}.json").write_text(json.dumps(summary, indent=1))
