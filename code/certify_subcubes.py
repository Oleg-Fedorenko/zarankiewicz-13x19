# Certificates for anchor cubes whose Kissat proof passed the cap (certify_anchor.py deferred them): the cube is split
# by fixing columns 1..depth in canonical form (subcubes.py; the sub-cubes together cover the cube), and every
# sub-cube is solved, proven and checked like a cube (certify_anchor.certify_work: Kissat 4.0.4 --unsat with a binary
# DRAT proof under the same cap, drat-trim). A sub-cube that passes the cap again is split one column deeper among the
# options that extend it. When every sub-cube of a cube is UNSAT and VERIFIED, the cube's own result.json says so and
# lists them. The sub-cube folders live on the external disk: certificates/<cell>/anchor-<profile>-sub/cube-XXXXX/.
#   .venv/bin/python certify_subcubes.py <m> <n> <T> <profile json> <depth> <workers> <out.json> [--cubes i,j,...]
#                                        [--extra m,n,v ...] [--cap-gb X] [--root <dir>] [--lp] [--deeper] [--mixed] [--lrat]
# --lrat: the solver is CaDiCaL with its LRAT proof streamed into lrat-check (certify_anchor.solve_lrat): no proof on
# disk, no size cap; a depth's run with --lrat also takes the sub-cubes of that depth that an earlier Kissat run
# deferred. --time-cap-min X with it: a solve longer than X minutes is stopped and the sub-cube deferred, for --deeper.
# --skip-deferred: sub-cubes of this depth that an earlier run deferred are not taken (a --deeper run has them).
# --lp: before the solver, the sub-cube's linear relaxation (subcube_lp.py, Afrasyab's block polytope with the fixed
# columns as anchors) is tried; when it is infeasible the sub-cube is closed by an exact Farkas certificate (a sparse
# rational vector, checked exactly) and no SAT run is needed. Such certificates are kept one line each in
# cube-XXXXX/farkas.jsonl, written by this process alone (the external disk is exFAT: every file there takes 512 KB,
# so a folder per sub-cube would not fit); with --lp the depths 1..depth-1 are tried first, a refuted shallow sub-cube
# closing all its extensions.
# Without --cubes: every cube of the anchor run with deferred.json and no result.json. --deeper: run only the options
# whose parent (the same columns but the last) is a deferred sub-cube — so a deeper run can go on beside a run that is
# still working through the shallower sub-cubes of the same cube. --root (for tests): a tree that stands for this
# folder, its "external" subfolder for the external disk.
import json, multiprocessing, os, pathlib, sys, time
from collections import defaultdict
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import certify_anchor
from certify_anchor import certify_work, extra_from, option, patch
import subcubes, subcube_lp, satprofile
LP = False

EXTERNAL = pathlib.Path("/Volumes/KINGSTON/zarankiewicz33-2026-10-13/structure")

def name(supports):
    return "d{}-".format(len(supports)) + "_".join("-".join(map(str, s)) for s in supports)

def lp_try(m, n, T, profile, idx, pattern, supports):
    cut1 = subcube_lp.row_floor(m, n, T, profile, satprofile.upper); t0 = time.time()
    ok, cert, meta = subcube_lp.refute(m, n, T, cut1, profile, {int(d): tuple(ms) for d, ms in pattern.items()}, supports)
    row = {"cube": idx, "depth": len(supports), "supports": [list(s) for s in supports], "lp seconds": round(time.time() - t0, 3)}
    if ok: row.update(verdict="UNSAT", route="farkas", farkas="VERIFIED", cut1=cut1, lp=meta, certificate=cert)
    else: row.update(verdict="lp feasible")
    return row

def run(args):
    m, n, T, profile, idx, pattern, supports, root, cap = args
    if LP:
        row = lp_try(m, n, T, profile, idx, pattern, supports)
        if row["verdict"] == "UNSAT": return row
    work = pathlib.Path(root) / f"cube-{idx:05d}" / name(supports); work.mkdir(parents=True, exist_ok=True)
    if not certify_anchor.claim(work):
        return {"cube": idx, "depth": len(supports), "supports": [list(s) for s in supports], "verdict": "skipped"}
    try:
        (work / "sub.json").write_text(json.dumps({"cube": idx, "pattern": pattern, "supports": [list(s) for s in supports]}))
        return certify_work(m, n, T, profile, pattern, subcubes.units(m, n, supports), work, cap,
                            {"cube": idx, "depth": len(supports), "supports": [list(s) for s in supports]})
    finally:
        (work / "running.lock").unlink(missing_ok=True)

def lp_only(args):
    """The linear relaxation alone for a sub-cube of a smaller depth (no files: the main process records)."""
    m, n, T, profile, idx, pattern, supports, root = args
    return lp_try(m, n, T, profile, idx, pattern, supports)

def init(slot):
    global LP
    certify_anchor.init(slot); LP = "--lp" in sys.argv

if __name__ == "__main__":
    patch()
    m, n, T = map(int, sys.argv[1:4]); profile = tuple(json.loads(sys.argv[4])); depth = int(sys.argv[5])
    workers = int(sys.argv[6]); out = HERE / sys.argv[7]; cap = int(option(sys.argv, "--cap-gb", 7) * 10**9)
    base = pathlib.Path(sys.argv[sys.argv.index("--root") + 1]) if "--root" in sys.argv else HERE
    external = base / "external" if "--root" in sys.argv else EXTERNAL
    rel = pathlib.Path("certificates") / f"z{m}x{n}-ge{T}" / f"anchor-{'-'.join(map(str, profile))}"
    folder = base / rel; pats = json.loads((folder / "patterns.json").read_text())
    subroot = base / f"{rel}-sub"
    if not subroot.exists():                                    # the sub-cube tree sits on the external disk
        (external / f"{rel}-sub").mkdir(parents=True, exist_ok=True); os.symlink(external / f"{rel}-sub", subroot)
    if "--cubes" in sys.argv:
        cubes = [int(x) for x in sys.argv[sys.argv.index("--cubes") + 1].split(",")]
    else:
        cubes = [int(p.name.split("-")[1]) for p in sorted(folder.glob("cube-*")) if (p / "deferred.json").exists() and not (p / "result.json").exists()]
    results = json.loads(out.read_text())["results"] if out.exists() else []
    head = {"cell": f"{m}x{n}", "T": T, "profile": list(profile), "depth": depth, "cubes": cubes, "proof cap bytes": cap,
            "extra": {f"z({a},{b})": v for (a, b), v in extra_from(sys.argv).items()}, "lp": "--lp" in sys.argv,
            "solver": ("cadical 3.0.1 " + " ".join(certify_anchor.CADICAL_OPTIONS) if "--lrat" in sys.argv else "kissat 4.0.4 --unsat")
                      + ", lean formula + pattern + fixed columns",
            "checker": (certify_anchor.LRATCHECK.name + ", streamed" if "--lrat" in sys.argv else "drat-trim") + "; Farkas vectors exactly"}
    print(json.dumps(head), flush=True)
    def finished(r):                                            # a streamed LRAT check counts only from the strict checker
        lrat = r.get("lrat-check") == "VERIFIED" and r.get("checker", "").startswith("lrat-check-strict ")
        return r["verdict"] == "UNSAT" and (r.get("drat-trim") == "VERIFIED" or lrat or r.get("farkas") == "VERIFIED")
    def key(r): return (r["cube"], tuple(tuple(s) for s in r["supports"]))
    # what is verified is read from the sub-cube tree itself — folders with result.json (solver route, and the older
    # one-folder Farkas records) and the lines of farkas.jsonl — so runs with other out files and other depths count
    verified, deferred, by_cube = {}, set(), defaultdict(set)
    def mark(r):
        verified[key(r)] = {k: v for k, v in r.items() if k not in ("certificate", "lp")}; by_cube[r["cube"]].add(key(r)[1])
    for idx in cubes:
        croot = subroot / f"cube-{idx:05d}"
        for res in sorted(croot.glob("d*/result.json")):
            r = json.loads(res.read_text())
            if finished(r): mark(r)
        for dj in sorted(croot.glob("d*/deferred.json")):
            if not (dj.parent / "result.json").exists(): deferred.add(key(json.loads(dj.read_text())))
        if (croot / "farkas.jsonl").exists():
            for line in (croot / "farkas.jsonl").read_text().splitlines():
                if line.strip():
                    r = json.loads(line)
                    if finished(r): mark(r)
    for r in results:
        if finished(r): mark(r)
    done = set(verified)
    covered = lambda idx, o: any((idx, o[:k]) in done for k in range(1, len(o) + 1))
    def record(r):
        """The main process alone writes the Farkas lines."""
        croot = subroot / f"cube-{r['cube']:05d}"; croot.mkdir(parents=True, exist_ok=True)
        with open(croot / "farkas.jsonl", "a") as f: f.write(json.dumps(r) + "\n")
        mark(r); done.add(key(r))
    opts = {idx: subcubes.options(m, profile, {int(d): tuple(ms) for d, ms in pats[idx].items()}, depth) for idx in cubes}
    deeper = "--deeper" in sys.argv
    if "--lp" in sys.argv and not deeper:
        for k in range(1, depth):
            shallow = [(m, n, T, profile, idx, pats[idx], o, str(subroot)) for idx in cubes
                       for o in subcubes.options(m, profile, {int(d): tuple(ms) for d, ms in pats[idx].items()}, k) if not covered(idx, o)]
            closed = 0
            with multiprocessing.Pool(workers, initializer=init, initargs=(multiprocessing.Semaphore(1),)) as pool:
                for r in pool.imap_unordered(lp_only, shallow, chunksize=8):
                    if r.get("farkas") == "VERIFIED": record(r); closed += 1
            print(json.dumps({"lp phase depth": k, "sub-cubes": len(shallow), "closed by Farkas": closed}), flush=True)
    # an option of this depth is also covered when every extension of it one column deeper is verified (work left by
    # a deeper run); checked only for options with at least one verified extension
    deeper_keys = {(i, s[:depth]) for i, s in done if len(s) == depth + 1}
    def covered_below(idx, o):
        if (idx, o) not in deeper_keys: return False
        return all((idx, x) in done for x in subcubes.extensions(m, profile, {int(d): tuple(ms) for d, ms in pats[idx].items()}, o, depth + 1))
    for idx in cubes:
        for o in opts[idx]:
            if not covered(idx, o) and covered_below(idx, o):
                done.add((idx, o)); verified[(idx, o)] = {"cube": idx, "supports": [list(x) for x in o], "verdict": "UNSAT", "route": "extensions"}
    skip = "--skip-deferred" in sys.argv                        # leave sub-cubes deferred before to a --deeper run
    todo = [(m, n, T, profile, idx, pats[idx], o, str(subroot), cap) for idx in cubes for o in opts[idx]
            if not covered(idx, o) and (not deeper or (idx, o[:-1]) in deferred) and not (skip and (idx, o) in deferred)]
    pending = defaultdict(int)
    for t in todo: pending[t[4]] += 1
    for idx in cubes:                                           # the cube's own folder holds its pattern, as for a whole cube
        cube = folder / f"cube-{idx:05d}"; cube.mkdir(parents=True, exist_ok=True)
        if not (cube / "pattern.json").exists(): (cube / "pattern.json").write_text(json.dumps(pats[idx]))
    print(json.dumps({"sub-cubes to run": len(todo)}), flush=True)
    def complete(idx):                                          # a cube every option of which is covered is certified
        if (folder / f"cube-{idx:05d}" / "result.json").exists() or not all(covered(idx, o) for o in opts[idx]): return
        subs = sorted(by_cube[idx]); rows = [verified[(idx, s)] for s in subs]   # by_cube holds real records only
        (folder / f"cube-{idx:05d}" / "result.json").write_text(json.dumps({
            "cube": idx, "verdict": "UNSAT", "route": "sub-cubes", "depth": max(len(s) for s in subs),
            "drat-trim": "VERIFIED (every sub-cube: drat-trim, lrat-check or an exact Farkas certificate)",
            "farkas sub-cubes": sum(1 for r in rows if r.get("farkas") == "VERIFIED"),
            "sub-cubes": [[list(s) for s in sub] for sub in subs], "folder": str((subroot / f"cube-{idx:05d}").relative_to(base)),
            "encodings": sorted({r.get("encoding", "lean") for r in rows if r.get("route") != "farkas"}),
            "solve seconds": round(sum(r.get("solve seconds", 0) for r in rows), 1)}))
        print(json.dumps({"cube": idx, "certified by sub-cubes": len(subs)}), flush=True)
    for idx in cubes:
        if pending[idx] == 0: complete(idx)                     # cubes whose sub-cubes were all verified already
    counts = defaultdict(int); last = time.time()
    def save():
        out.write_text(json.dumps({**head, "counts": dict(counts), "results": results}))
    with multiprocessing.Pool(workers, initializer=init, initargs=(multiprocessing.Semaphore(1),)) as pool:
        for r in pool.imap_unordered(run, todo, chunksize=4 if "--lp" in sys.argv else 1):
            counts[r.get("route", r["verdict"])] += 1
            if r.get("route") == "farkas": record(r)
            else:
                results.append(r)
                if finished(r): mark(r); done.add(key(r))
                if not finished(r) or r.get("solve seconds", 0) > 600:
                    print(json.dumps({k: v for k, v in r.items() if k != "matrix"}), flush=True)
                if r["verdict"] == "SAT" and r.get("checked"):
                    (HERE / "symwork" / f"SUBCUBE-SAT-{m}x{n}-{T}-{r['cube']}.json").write_text(json.dumps(r["matrix"]))
            pending[r["cube"]] -= 1
            if pending[r["cube"]] == 0: complete(r["cube"])
            if time.time() - last > 60: save(); last = time.time()
    save()
    print(json.dumps({"done": sum(counts.values()), "counts": dict(counts),
                      "deferred": sum(r["verdict"] == "deferred" for r in results), "SAT": sum(r["verdict"] == "SAT" for r in results)}), flush=True)
