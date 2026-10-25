# The audit of the upper bound z(13,19;3,3) <= 120 (or any cell): for every column profile the counting allows, that a
# certificate exists, that its CNF is exactly the formula the generator writes for that profile today (rebuilt here and
# compared byte for byte with the kept case.cnf.gz), and what drat-trim said. With --recheck, drat-trim is run again on
# every kept proof (unpacked to a temporary file one at a time: drat-trim rewinds the proof file, so a named pipe gives
# a false NOT VERIFIED — tested on 2026-10-17). A profile without such a certificate but with anchor cubes
# (certificates/<cell>/anchor-<profile>/: certify_anchor.py, certify_subcubes.py) is audited by audit_anchor.py, run
# afresh here: it must report no problem, its list of patterns must equal a fresh enumeration, and every cube must be
# certified. --anchor-recheck N passes --recheck N --recheck-lrat N to it.
#   .venv/bin/python audit_certificates.py <m> <n> <T> <k> [--recheck] [--only N] [--anchor-recheck N]
import gzip, hashlib, io, json, pathlib, re, shutil, subprocess, sys, tempfile
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from pysat.formula import CNF
from satprofile import column_profiles, case_formula
from satpairs import profile_formula_pairs

DRATTRIM = HERE / "tools" / "drat-trim" / "drat-trim"

def dimacs(clauses):
    buf = io.StringIO(); CNF(from_clauses=clauses).to_fp(buf); return buf.getvalue().encode()

def kept_cnf(folder):
    with gzip.open(folder / "case.cnf.gz", "rb") as f: return f.read()

def anchor_audit(m, n, T, p, argv):
    extra = ["--recheck", argv[argv.index("--anchor-recheck") + 1], "--recheck-lrat", argv[argv.index("--anchor-recheck") + 1]] if "--anchor-recheck" in argv else []
    d = subprocess.run([sys.executable, str(HERE / "audit_anchor.py"), str(m), str(n), str(T), json.dumps(list(p)), *extra], capture_output=True, text=True)
    lines = [l for l in d.stdout.splitlines() if l.startswith("{")]
    return json.loads(lines[-1]) if lines else {"error": (d.stderr or d.stdout)[-500:]}

def recheck(cnf_bytes, proof_gz):
    """drat-trim on the kept CNF and proof, both unpacked to a temporary folder that is removed afterwards."""
    with tempfile.TemporaryDirectory(dir=HERE / "symwork") as tmp:
        cnf = pathlib.Path(tmp) / "case.cnf"; cnf.write_bytes(cnf_bytes)
        proof = pathlib.Path(tmp) / "case.drat"
        with gzip.open(proof_gz, "rb") as src, open(proof, "wb") as dst: shutil.copyfileobj(src, dst, 1 << 20)
        d = subprocess.run([str(DRATTRIM), str(cnf), str(proof), "-t", "200000"], capture_output=True, text=True)
        return "VERIFIED" if re.search(r"^s VERIFIED", d.stdout, re.M) else ("NOT VERIFIED" if "NOT VERIFIED" in d.stdout else "no verdict")

if __name__ == "__main__":
    m, n, T, k = map(int, sys.argv[1:5])
    only = int(sys.argv[sys.argv.index("--only") + 1]) if "--only" in sys.argv else None
    profiles, cuts = column_profiles(m, n, T)
    base = HERE / "certificates" / f"z{m}x{n}-ge{T}"
    rows, missing = [], []
    for p in profiles[:only] if only else profiles:
        name = "-".join(map(str, p))
        found = None
        for variant, folder in (("plain", base / f"profile-{name}"), ("pairs", base / f"profile-pairs-{name}")):
            if (folder / "result.json").exists() and (folder / "case.cnf.gz").exists():
                res = json.loads((folder / "result.json").read_text())
                if res.get("verdict") == "UNSAT" and res.get("drat-trim") == "VERIFIED": found = (variant, folder, res); break
        if not found and (base / f"anchor-{name}" / "patterns.json").exists():
            a = anchor_audit(m, n, T, p, sys.argv); c = a.get("certified", {})
            rechecks = list(a.get("recheck", {}).values()) + list(a.get("recheck lrat", {}).values())
            ok = (a.get("number of problems") == 0 and a.get("patterns.json equal to a fresh enumeration") is True
                  and c.get("whole", 0) + c.get("sub-cubes", 0) + c.get("lrat", 0) == a.get("cubes") and all(v == "VERIFIED" for v in rechecks))
            row = {"profile": list(p), "variant": "anchor cubes", "ok": ok, "cubes": a.get("cubes"), "certified": c,
                   "problems": a.get("number of problems", a.get("error")), "rechecked": len(rechecks)}
            rows.append(row); print(json.dumps(row), flush=True); continue
        if not found:
            missing.append(list(p)); continue
        variant, folder, res = found
        clauses = (profile_formula_pairs(m, n, T, p, k)[1] if variant == "pairs" else case_formula(m, n, T, tuple(p), k)[1])
        same = hashlib.sha256(dimacs(clauses)).hexdigest() == hashlib.sha256(kept_cnf(folder)).hexdigest()
        row = {"profile": list(p), "variant": variant, "ok": same and res.get("drat-trim") == "VERIFIED", "cnf rebuilt identical": same, "drat-trim then": res.get("drat-trim"),
               "solve seconds": res.get("solve seconds"), "proof bytes": res.get("proof bytes")}
        if "--recheck" in sys.argv:
            row["drat-trim now"] = recheck(kept_cnf(folder), folder / "case.drat.gz"); row["ok"] = row["ok"] and row["drat-trim now"] == "VERIFIED"
        rows.append(row); print(json.dumps(row), flush=True)
    summary = {"cell": f"{m}x{n}", "T": T, "profiles": len(profiles), "certified": len(rows), "missing": missing,
               "all CNFs identical": all(r.get("cnf rebuilt identical", r["ok"]) for r in rows),
               "all verified": all(r["ok"] for r in rows), "by anchor cubes": [r["profile"] for r in rows if r["variant"] == "anchor cubes"]}
    print(json.dumps(summary), flush=True)
    # a partial run (--only) must not stand in for the cell's audit
    (HERE / f"audit-{m}x{n}-{T}{f'-only{only}' if only else ''}.json").write_text(json.dumps({**summary, "rows": rows}, indent=1))
