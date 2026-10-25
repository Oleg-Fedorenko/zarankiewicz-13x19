# Certificates for one column-profile case by anchor cubes (anchor_cubes.py): every pattern is a cube; each cube's CNF
# (the lean formula + "B is the first c rows" + the pattern's counts) is solved by Kissat 4.0.4 --unsat writing a binary
# DRAT proof, which drat-trim checks against that CNF; CNF and proof are kept compressed with the pattern and the result.
# Coverage: every matrix of the case, in canonical form, has a first column B of the largest degree whose pattern
# satisfies (I)-(IV) and the window — and every such pattern is in the list (two independent enumerations agree: ours
# and GLM's, 2026-10-19). Resumable; cubes run in the order of the list.
# The machine has 16 GB and drat-trim takes about 1.3x the proof: a solve whose proof passes the cap (--cap-gb, default
# 7) or that leaves the internal disk under 5 GB is stopped and the cube is deferred (deferred.json, CNF kept) for the
# streamed LRAT route; a proof above 2 GB is checked only while no other such check runs. A resumed run leaves deferred
# cubes alone unless --retry-deferred.
#   .venv/bin/python certify_anchor.py <m> <n> <T> <profile json> <workers> <out.json> [--extra m,n,v ...]
#                                      [--cap-gb X] [--retry-deferred] [--order <json list of cube indices>] [--mixed] [--lrat]
# --order: run only these cubes, in this order (the others wait for another run; nothing is skipped for good).
# --external <dir>: each cube folder not yet made is made there (the same relative path) and linked from here, so the
#   proofs are written to the external disk; the mover leaves links alone. A cube whose folder already holds a
#   result.json (from any route: this one, certify_subcubes.py, certify_deferred.py) is not run again.
#   --lrat: CaDiCaL 3.0.1 instead of Kissat, its LRAT proof written into a FIFO that lrat-check-strict reads while it
#   is written: nothing goes to disk, so there is no size cap; the check ends with the solve. lrat-check-strict is
#   lrat-check of the drat-trim repository with every step required to be RUP through its hints (the original let an
#   empty clause with no conflict through: a satisfiable CNF with the proof "3 0 0" was VERIFIED) and numbers out of
#   int range refused (see tools/drat-trim/lrat-check-strict.c). UNSAT counts only with the checker's "c VERIFIED" and
#   exit 0, and only then is result.json written (otherwise unverified.json, and the cube is looked at again).
#   --time-cap-min X with it: a solve longer than X minutes is stopped and the cube deferred (deferred.json, CNF kept).
import gzip, hashlib, json, multiprocessing, os, pathlib, re, shutil, signal, subprocess, sys, tempfile, time
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import satprofile, satfull
from pysat.formula import CNF
from anchor_cubes import patterns, window, cube_formula
from satclass import k33_free

KISSAT = HERE / "tools" / "kissat-src" / "arminbiere-kissat-8af8e56" / "build" / "kissat"
DRATTRIM = HERE / "tools" / "drat-trim" / "drat-trim"
CADICAL = HERE / "tools" / "cadical-src" / "build" / "cadical"
LRATCHECK = HERE / "tools" / "drat-trim" / "lrat-check-strict"
CADICAL_OPTIONS = ["-q", "--lrat=true", "--binary=false"]

def fingerprint(path):
    """The first 16 hex digits of the program's sha256, so every row names the exact binaries that produced it."""
    try: return hashlib.sha256(path.read_bytes()).hexdigest()[:16]
    except OSError: return "missing"
BIG = 2 * 10**9           # a proof above this is checked in the single big-check slot
FLOOR = 5 * 2**30          # free bytes on the disk of the cube folder below which a solve is stopped
POLL = float(os.environ.get("ANCHOR_POLL", 10))   # seconds between looks at a running solve (tests set it lower)
BIGCHECK = None            # the big-check slot, a semaphore shared by the workers (init)

def extra_from(argv):
    out = {}
    if "--extra" in argv:
        for spec in argv[argv.index("--extra") + 1:]:
            if spec.startswith("--"): break
            a, b, c = map(int, spec.split(",")); out[a, b] = c
    return out

MIXED = False              # --mixed: the formula also has the mixed row-and-column deletion cuts (satlean.mixed_cut_clauses)
LRAT = False               # --lrat: CaDiCaL with the LRAT proof streamed into lrat-check (see the head of the file)
TIMECAP = None             # --time-cap-min X (with --lrat): a solve longer than X minutes is stopped and deferred

def patch():
    global MIXED, LRAT, TIMECAP
    MIXED = "--mixed" in sys.argv
    LRAT = "--lrat" in sys.argv
    TIMECAP = 60 * float(sys.argv[sys.argv.index("--time-cap-min") + 1]) if "--time-cap-min" in sys.argv else None
    if TIMECAP is not None and not LRAT: sys.exit("--time-cap-min works with --lrat only (Kissat runs are bounded by --cap-gb)")
    extra = extra_from(sys.argv)
    if extra:
        from collins import closure
        hi = closure(extra); satprofile.upper = lambda a, b: hi.get((a, b)); satfull.upper = satprofile.upper

def option(argv, name, default):
    return float(argv[argv.index(name) + 1]) if name in argv else default

def init(slot):
    global BIGCHECK
    BIGCHECK = slot
    patch()
    # a worker terminated in the middle of a solve (Pool.terminate sends SIGTERM) unwinds, so the finally blocks below
    # stop its solver and checker; an idle one (the pool's own shutdown) just exits
    signal.signal(signal.SIGTERM, lambda signum, frame: sys.exit(143) if SOLVING else os._exit(143))

SOLVING = False            # True while a solver runs in this process (solve, solve_lrat)

def stop(*procs):
    for p in procs:
        if p is not None and p.poll() is None: p.kill(); p.wait()

def solve(cmd, proof, cap):
    """Kissat with its proof watched: (exit code, stdout, None), or (None, "", reason) when it had to be stopped."""
    global SOLVING
    SOLVING = True
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    try:
        while True:
            try:
                out, _ = p.communicate(timeout=POLL)
                return p.returncode, out, None
            except subprocess.TimeoutExpired:
                size = proof.stat().st_size if proof.exists() else 0
                why = "proof over cap" if size > cap else ("disk low" if shutil.disk_usage(proof.parent).free < FLOOR else None)
                if why:
                    p.kill(); p.communicate()
                    return None, "", why
    finally:
        stop(p); SOLVING = False

def solve_lrat(cnf, limit=None):
    """CaDiCaL on `cnf` writing its LRAT proof into a FIFO that lrat-check-strict reads against the same `cnf` while it is
    written: (solver exit code, solver stdout, "VERIFIED" or "NOT VERIFIED", seconds the check ran on after the solver,
    the checker's verdict lines). VERIFIED needs exit 20, the checker's exit 0 and its "c VERIFIED" line. The two run
    watched together: a solve longer than `limit` seconds is stopped — (None, "", "time over cap", 0, []); a checker
    that ends while the solver still runs (a refused proof, or a FIFO it never opened) stops the solver — exit code
    "checker ended first"; and neither program outlives the call, however it ends."""
    global SOLVING
    with tempfile.TemporaryDirectory(dir=HERE / "symwork") as tmp:     # the internal disk: a FIFO, and the two logs
        tmp = pathlib.Path(tmp); fifo = tmp / "proof.lrat"; os.mkfifo(fifo)
        check = solver = None
        SOLVING = True
        try:
            with open(tmp / "checker.txt", "w") as said_to, open(tmp / "solver.txt", "w") as told:   # files: a full pipe could stall
                check = subprocess.Popen([str(LRATCHECK), str(cnf), str(fifo)], stdout=said_to, stderr=subprocess.STDOUT)
                solver = subprocess.Popen([str(CADICAL), *CADICAL_OPTIONS, str(cnf), str(fifo)], stdout=told, stderr=subprocess.DEVNULL)
            start = time.time()
            while solver.poll() is None:
                if limit is not None and time.time() - start > limit: return None, "", "time over cap", 0.0, []
                if check.poll() is not None:     # the checker is done: the solver ends soon (it closes the proof before
                    # it frees its memory, which can take a while, so a checker that verified waits long), or never (it
                    # waits on a FIFO the checker never opened)
                    done = check.returncode == 0 and re.search(r"^c VERIFIED$", (tmp / "checker.txt").read_text(errors="replace"), re.M)
                    try: solver.wait(timeout=3600 if done else 60)
                    except subprocess.TimeoutExpired: pass
                    break
                try: solver.wait(timeout=1)
                except subprocess.TimeoutExpired: pass
            code = solver.poll()
            if code is None: stop(solver); code = "checker ended first"
            solved = time.time()
            if code == 20:
                try: check.wait(timeout=600)                           # the rest of the proof is at most a FIFO's buffer
                except subprocess.TimeoutExpired: pass
            stop(check)
            said = (tmp / "checker.txt").read_text(errors="replace")
            verified = (code == 20 and check.returncode == 0 and re.search(r"^c VERIFIED$", said, re.M) is not None
                        and "NOT VERIFIED" not in said)
            lines = [l for l in said.splitlines() if re.search(r"VERIFIED|FAIL|fail|ERROR|error", l)][:3]
            return code, (tmp / "solver.txt").read_text(), "VERIFIED" if verified else "NOT VERIFIED", round(time.time() - solved, 1), lines
        finally:
            stop(solver, check); SOLVING = False

def matrix_from(stdout, m, n):
    values = {int(x) for line in stdout.splitlines() if line.startswith("v ") for x in line[2:].split() if x != "0"}
    return [[1 if i * n + j + 1 in values else 0 for j in range(n)] for i in range(m)]

def gz(path):
    with open(path, "rb") as src, gzip.open(str(path) + ".gz", "wb", compresslevel=6) as dst: shutil.copyfileobj(src, dst)
    path.unlink()

def claim(work):
    """Take the folder for this process: an exclusive lock file holding the pid. A lock whose process is gone is taken
    over; a live one, or a folder that already holds a result, means another run has (or had) this cube."""
    if (work / "result.json").exists(): return False
    lock = work / "running.lock"
    for _ in range(2):
        try:
            fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY); os.write(fd, str(os.getpid()).encode()); os.close(fd); return True
        except FileExistsError:
            try: pid = int(lock.read_text() or "0"); os.kill(pid, 0); return False
            except (ValueError, ProcessLookupError, FileNotFoundError): lock.unlink(missing_ok=True)
            except PermissionError: return False
    return False

def certify_cube(args):
    patch()
    m, n, T, profile, idx, pattern, folder, cap = args
    work = pathlib.Path(folder) / f"cube-{idx:05d}"; work.mkdir(parents=True, exist_ok=True)
    if not claim(work): return {"cube": idx, "verdict": "skipped", "reason": "another run has this cube or it is done"}
    try:
        (work / "pattern.json").write_text(json.dumps(pattern))
        return certify_work(m, n, T, profile, pattern, [], work, cap, {"cube": idx})
    finally:
        (work / "running.lock").unlink(missing_ok=True)

def certify_work(m, n, T, profile, pattern, units, work, cap, row):
    """The cube's formula plus the unit clauses `units` (literals of cells, x(r,j) = r*n + j + 1), solved, proven and
    checked in the folder `work`; the result is also written to work/result.json (or deferred.json)."""
    pool, clauses = cube_formula(m, n, T, profile, 3, {int(d): tuple(ms) for d, ms in pattern.items()}, mixed=MIXED)
    clauses = list(clauses) + [[u] for u in units]
    cnf, proof = work / "case.cnf", work / "case.drat"
    CNF(from_clauses=clauses).to_file(str(cnf))
    row = {**row, "variables": pool.top, "clauses": len(clauses), "encoding": "lean+mixed" if MIXED else "lean"}
    start = time.time()
    if LRAT:
        row.update(solver=f"cadical 3.0.1 {' '.join(CADICAL_OPTIONS)} (sha256 {fingerprint(CADICAL)})",
                   checker=f"{LRATCHECK.name} (sha256 {fingerprint(LRATCHECK)}), reading the proof from a FIFO")
        code, stdout, verdict, after, lines = solve_lrat(cnf, TIMECAP)
        row["solve seconds"] = round(time.time() - start, 1)
        if code is None:
            row.update(verdict="deferred", reason="time over cap"); gz(cnf); (work / "deferred.json").write_text(json.dumps(row)); return row
        if code == 10:
            M = matrix_from(stdout, m, n)
            row.update(verdict="SAT", checked=k33_free(M) and sum(map(sum, M)) == T, matrix=M)
            gz(cnf); (work / "result.json").write_text(json.dumps(row)); return row
        if code != 20:                     # also a proof the checker refused mid-stream (the solver then dies of SIGPIPE)
            row.update(verdict="unknown", **{"solver exit": code, "checker says": lines})
            gz(cnf); (work / "unverified.json").write_text(json.dumps(row)); return row
        row.update(verdict="UNSAT", **{"lrat-check": verdict, "check seconds after the solve": after})
        gz(cnf)
        if verdict != "VERIFIED":
            row["checker says"] = lines; (work / "unverified.json").write_text(json.dumps(row)); return row
        (work / "unverified.json").unlink(missing_ok=True)
        (work / "result.json").write_text(json.dumps(row)); return row
    code, stdout, why = solve([str(KISSAT), "-q", "--unsat", str(cnf), str(proof)], proof, cap)
    row["solve seconds"] = round(time.time() - start, 1)
    if why:
        row.update(verdict="deferred", reason=why, **{"proof bytes at stop": proof.stat().st_size if proof.exists() else 0})
        proof.unlink(missing_ok=True); gz(cnf); (work / "deferred.json").write_text(json.dumps(row)); return row
    if code == 10:
        M = matrix_from(stdout, m, n)
        row.update(verdict="SAT", checked=k33_free(M) and sum(map(sum, M)) == T, matrix=M)
        proof.unlink(missing_ok=True); gz(cnf); (work / "result.json").write_text(json.dumps(row)); return row
    if code != 20:
        row["verdict"] = "unknown"; row["solver exit"] = code; return row
    row["verdict"] = "UNSAT"; row["proof bytes"] = proof.stat().st_size
    big = row["proof bytes"] > BIG
    if big: BIGCHECK.acquire()
    try:
        start = time.time()
        d = subprocess.run([str(DRATTRIM), str(cnf), str(proof), "-t", "200000"], capture_output=True, text=True)
        row["check seconds"] = round(time.time() - start, 1)
    finally:
        if big: BIGCHECK.release()
    row["drat-trim"] = "VERIFIED" if re.search(r"^s VERIFIED", d.stdout, re.M) else ("NOT VERIFIED" if "NOT VERIFIED" in d.stdout else "no verdict")
    gz(proof); gz(cnf)
    (work / "result.json").write_text(json.dumps(row))
    return row

if __name__ == "__main__":
    patch()
    m, n, T = map(int, sys.argv[1:4]); profile = tuple(json.loads(sys.argv[4])); workers = int(sys.argv[5]); out = HERE / sys.argv[6]
    cuts = {k: T - satprofile.upper(m - k, n) for k in (1, 2, 3) if satprofile.upper(m - k, n) is not None}
    c = profile[0]; lo, hi = window(m, T, c, cuts)
    ps = patterns(m, profile, c, lo, hi)
    cap = int(option(sys.argv, "--cap-gb", 7) * 10**9); retry = "--retry-deferred" in sys.argv
    folder = HERE / "certificates" / f"z{m}x{n}-ge{T}" / f"anchor-{'-'.join(map(str, profile))}"
    folder.mkdir(parents=True, exist_ok=True)
    (folder / "patterns.json").write_text(json.dumps([{str(d): list(ms) for d, ms in p.items()} for p in ps]))
    head = {"cell": f"{m}x{n}", "T": T, "profile": list(profile), "anchor degree": c, "window": [lo, hi], "cuts": cuts,
            "extra": {f"z({a},{b})": v for (a, b), v in extra_from(sys.argv).items()}, "cubes": len(ps),
            "solver": ("cadical 3.0.1, LRAT streamed" if LRAT else "kissat 4.0.4 --unsat") + ", lean formula",
            "checker": "lrat-check-strict" if LRAT else "drat-trim", "proof cap bytes": cap}
    print(json.dumps(head), flush=True)
    results = json.loads(out.read_text())["results"] if out.exists() else []
    def verified(r): return r.get("verdict") == "UNSAT" and (r.get("drat-trim") == "VERIFIED" or r.get("lrat-check") == "VERIFIED")
    def settled(r): return verified(r) or (r.get("verdict") == "SAT" and r.get("checked")) or (r.get("verdict") == "deferred" and not retry)
    done = {r["cube"] for r in results if settled(r)}  # "skipped" and unverified rows are not kept: such a cube is looked at again
    results = [r for r in results if r["cube"] in done]
    done |= {i for i in range(len(ps)) if (folder / f"cube-{i:05d}" / "result.json").exists()}
    order = json.loads(pathlib.Path(sys.argv[sys.argv.index("--order") + 1]).read_text()) if "--order" in sys.argv else range(len(ps))
    todo = [(m, n, T, profile, i, {str(d): list(ms) for d, ms in ps[i].items()}, str(folder), cap) for i in order if i not in done]
    if "--external" in sys.argv:
        ext = pathlib.Path(sys.argv[sys.argv.index("--external") + 1]) / folder.relative_to(HERE)
        for t in todo:
            local = folder / f"cube-{t[4]:05d}"
            if not (local.exists() or local.is_symlink()):
                (ext / local.name).mkdir(parents=True, exist_ok=True); os.symlink(ext / local.name, local)
    with multiprocessing.Pool(workers, initializer=init, initargs=(multiprocessing.Semaphore(1),)) as pool:
        for r in pool.imap_unordered(certify_cube, todo):
            results.append(r); out.write_text(json.dumps({**head, "results": results}))
            if not verified(r) or r.get("solve seconds", 0) > 300:
                print(json.dumps({k: v for k, v in r.items() if k != "matrix"}), flush=True)
            if r["verdict"] == "SAT" and r.get("checked"):
                (HERE / "symwork" / f"ANCHOR-SAT-{m}x{n}-{T}.json").write_text(json.dumps(r["matrix"]))
    print(json.dumps({"done": len(results), "UNSAT": sum(r["verdict"] == "UNSAT" for r in results),
                      "verified": sum(1 for r in results if verified(r)),
                      "SAT": sum(r["verdict"] == "SAT" for r in results), "unknown": sum(r["verdict"] == "unknown" for r in results),
                      "deferred": sum(r["verdict"] == "deferred" for r in results),
                      "solve seconds": round(sum(r.get("solve seconds", 0) for r in results)),
                      "max": max([r.get("solve seconds", 0) for r in results] or [0])}), flush=True)
