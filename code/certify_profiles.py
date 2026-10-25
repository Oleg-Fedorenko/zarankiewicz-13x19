# Certificates for the profile cases found impossible: for each column profile, the case formula in DIMACS, a DRAT
# proof written by Glucose 4.2.1 (-certified, -no-pre: its preprocessing made these formulas hundreds of times slower), and drat-trim's verdict on it; the proof is then compressed and kept.
#   .venv/bin/python certify_profiles.py <m> <n> <T> <k> <profiles.json> <out.json> [--binary] [--pairs]
# --pairs: the case formula also bounds how many columns two rows and how many rows two columns can share (satpairs.py;
#          implied by the case, nothing is lost); such certificates sit in profile-pairs-<profile>/.
# --lean:  the row cuts by one totalizer per row instead of one counter per k-subset of rows (satlean.py; the same
#          set of matrices, a formula ~14 times smaller); such certificates sit in profile-lean-<profile>/.
# --kissat: solve with Kissat 4.0.4 (--unsat configuration, binary DRAT proof) instead of Glucose; such certificates
#          sit in profile[-lean]-kissat-<profile>/. drat-trim checks the proof the same way.
import gzip, json, pathlib, re, shutil, subprocess, sys, time
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from pysat.formula import CNF
from satprofile import case_formula
from satpairs import profile_formula_pairs
from satlean import case_formula_lean

GLUCOSE = HERE / "tools" / "glucose-src" / "simp" / "glucose_release"
DRATTRIM = HERE / "tools" / "drat-trim" / "drat-trim"
KISSAT = HERE / "tools" / "kissat-src" / "arminbiere-kissat-8af8e56" / "build" / "kissat"
# binary proofs (-vbyte) are several times smaller; drat-trim reads them as well
BINARY = "--binary" in sys.argv
PAIRS = "--pairs" in sys.argv
LEAN = "--lean" in sys.argv
USE_KISSAT = "--kissat" in sys.argv

def certify(m, n, T, k, profile, folder):
    folder.mkdir(parents=True, exist_ok=True)
    if LEAN: pool, clauses, v, info = case_formula_lean(m, n, T, tuple(profile), k)
    elif PAIRS: pool, clauses, v, info = profile_formula_pairs(m, n, T, profile, k)
    else: pool, clauses, v, info = (*case_formula(m, n, T, tuple(profile), k), None)
    cnf, proof = folder / "case.cnf", folder / "case.drat"
    CNF(from_clauses=clauses).to_file(str(cnf))
    start = time.time()
    if USE_KISSAT:
        g = subprocess.run([str(KISSAT), "-q", "-n", "--unsat"] + ([] if BINARY else ["--no-binary"]) + [str(cnf), str(proof)], capture_output=True, text=True)   # binary DRAT to a file by default
    else:
        g = subprocess.run([str(GLUCOSE), "-no-pre", "-certified"] + (["-vbyte"] if BINARY else []) + [f"-certified-output={proof}", str(cnf)], capture_output=True, text=True)
    row = {"profile": list(profile), "solver": "kissat 4.0.4 --unsat" if USE_KISSAT else "glucose 4.2.1 -no-pre", "encoding": "lean" if LEAN else ("pairs" if PAIRS else "plain"), "pairs": info, "variables": pool.top, "clauses": len(clauses), "solve seconds": round(time.time() - start, 1), "solver exit": g.returncode}
    if g.returncode != 20:
        row["verdict"] = "SAT" if g.returncode == 10 else "unknown"
        return row
    row["verdict"] = "UNSAT"; row["proof bytes"] = proof.stat().st_size
    start = time.time()
    d = subprocess.run([str(DRATTRIM), str(cnf), str(proof), "-t", "200000"], capture_output=True, text=True)
    row["check seconds"] = round(time.time() - start, 1)
    row["drat-trim"] = "VERIFIED" if re.search(r"^s VERIFIED", d.stdout, re.M) else ("NOT VERIFIED" if "NOT VERIFIED" in d.stdout else "no verdict: " + d.stdout[-200:])
    with open(proof, "rb") as src, gzip.open(str(proof) + ".gz", "wb", compresslevel=6) as dst: shutil.copyfileobj(src, dst)
    proof.unlink()
    with open(cnf, "rb") as src, gzip.open(str(cnf) + ".gz", "wb", compresslevel=6) as dst: shutil.copyfileobj(src, dst)
    cnf.unlink()
    (folder / "result.json").write_text(json.dumps(row, indent=1))
    return row

if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if a not in ("--binary", "--pairs", "--lean", "--kissat")]
    m, n, T, k = map(int, args[0:4])
    profiles = json.loads(pathlib.Path(args[4]).read_text())
    out = HERE / args[5]
    results = json.loads(out.read_text()) if out.exists() else []
    done = {tuple(r["profile"]) for r in results}
    for i, p in enumerate(profiles):
        if tuple(p) in done: continue
        row = certify(m, n, T, k, p, HERE / "certificates" / f"z{m}x{n}-ge{T}" / f"profile{'-lean' if LEAN else '-pairs' if PAIRS else ''}{'-kissat' if USE_KISSAT else ''}-{'-'.join(map(str, p))}")
        results.append(row); out.write_text(json.dumps(results, indent=1))
        print(json.dumps(row), flush=True)
