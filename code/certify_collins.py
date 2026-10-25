# z(m, n; 3, 3) < T with certificates, the cuts resting on Collins et al.'s Table 4 only (collins.py, closed under the
# deletion lemma) plus the bounds proven here that are named with --extra: the column profiles of satprofile and the
# case formula of each, every k-line cut taken from that closure instead of table.py; each profile certified as in
# certify_profiles.py (Glucose 4.2.1 -no-pre -certified -vbyte, drat-trim). The result file records the bounds used.
#   .venv/bin/python certify_collins.py <m> <n> <T> <k> <workers> <out.json> --binary [--extra m,n,v ...] [--part i/K] [--lean]
# --part i/K: only every K-th profile from the i-th on, so that several processes can share a cell as cores free up;
#             each part writes its own out.json.
import json, multiprocessing, pathlib, sys
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import satprofile, satfull
from collins import closure

def parse_extra(argv):
    out = {}
    if "--extra" in argv:
        for spec in argv[argv.index("--extra") + 1:]:
            if spec.startswith("--"): break
            m, n, v = map(int, spec.split(",")); out[m, n] = v
    return out

EXTRA = parse_extra(sys.argv)
HI = closure(EXTRA)

def upper(m, n):
    return HI.get((m, n))

def patch():
    satprofile.upper = upper
    satfull.upper = upper

def run(args):
    patch()
    from certify_profiles import certify
    m, n, T, k, profile = args
    variant = "-lean" if "--lean" in sys.argv else ""   # --lean: certify_profiles builds the satlean formula
    return certify(m, n, T, k, profile, HERE / "certificates" / f"z{m}x{n}-ge{T}" / f"profile{variant}-{'-'.join(map(str, profile))}")

if __name__ == "__main__":
    patch()
    nums = [a for a in sys.argv[1:7]]
    m, n, T, k, workers = map(int, nums[0:5]); out = HERE / nums[5]
    profiles, cuts = satprofile.column_profiles(m, n, T)
    part = None
    if "--part" in sys.argv:
        i, K = map(int, sys.argv[sys.argv.index("--part") + 1].split("/")); part = f"{i}/{K}"
        profiles = profiles[i::K]
    used = {f"z({m},{n - j})": upper(m, n - j) for j in range(1, k + 1)}
    used.update({f"z({m - j},{n})": upper(m - j, n) for j in range(1, k + 1)})
    head = {"cell": f"{m}x{n}", "T": T, "k": k, "source": "Collins et al. 2016, Table 4, closed under the deletion lemma",
            "proven here and used": {f"z({a},{b})": v for (a, b), v in EXTRA.items()}, "cut values": used,
            "column cuts": cuts, "profiles": len(profiles), "part": part}
    print(json.dumps(head), flush=True)
    results = json.loads(out.read_text())["results"] if out.exists() else []
    done = {tuple(r["profile"]) for r in results if r.get("verdict") in ("UNSAT", "SAT")}
    todo = [(m, n, T, k, tuple(p)) for p in profiles if tuple(p) not in done]
    with multiprocessing.Pool(workers, initializer=patch) as pool:
        for r in pool.imap_unordered(run, todo):
            results.append(r); out.write_text(json.dumps({**head, "results": results}, indent=1))
            print(json.dumps(r), flush=True)
    tally = {x: sum(1 for r in results if r.get("verdict") == x) for x in ("UNSAT", "SAT", "unknown")}
    print(json.dumps({"done": len(results), **tally, "verified": sum(1 for r in results if r.get("drat-trim") == "VERIFIED")}), flush=True)
