#!/usr/bin/env python3
"""Benchmark every decoder on every test image.

    python3 bench/run.py [--cpu N] [--only name,name] [--images a,b] [--seconds S] [--json out.json]

Each (decoder, image) pair runs in one process for at least --seconds of decoding (min 5 iterations)
pinned to one core; we report the median and the min, and check the output hash against qoi.h.
"""
import argparse, json, os, shutil, struct, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DECODERS = {
    "c-qoi.h": "build/qoi-ref",
    "zig-simple": "zig/zig-out/bin/qoi-zig-simple",
    "zig-fast": "zig/zig-out/bin/qoi-zig-fast",
    "lean-fast": "lean/.lake/build/bin/qoi-lean-fast",
    "lean-spec": "lean/.lake/build/bin/qoi-lean-spec",
}
IMAGES = ["edgecase", "qoi_logo", "testcard", "testcard_rgba", "dice", "kodim10", "kodim23", "wikipedia_008",
          "synth_flat", "synth_photo"]


def dims(path):
    with open(path, "rb") as f:
        h = f.read(14)
    return struct.unpack(">II", h[4:12])


def bench(exe, img, iters, cpu):
    cmd = [exe, "bench", img, str(iters)]
    if cpu is not None and shutil.which("taskset"):
        cmd = ["taskset", "-c", str(cpu)] + cmd
    out = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
    if out.returncode != 0:
        return None
    mn, med, h = out.stdout.split()
    return int(mn), int(med), h


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cpu", type=int, default=None)
    ap.add_argument("--only", default=None)
    ap.add_argument("--images", default=None)
    ap.add_argument("--seconds", type=float, default=1.0)
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    names = a.only.split(",") if a.only else [n for n in DECODERS if n != "lean-spec"]
    images = a.images.split(",") if a.images else IMAGES
    results = {}
    print(f"{'image':<15}{'Mpx':>7}" + "".join(f"{n:>14}" for n in names) + "   (median MPx/s)")
    for im in images:
        path = os.path.join(ROOT, "testdata", im + ".qoi")
        if not os.path.exists(path):
            continue
        w, h = dims(path)
        ref = bench(os.path.join(ROOT, DECODERS["c-qoi.h"]), path, 3, a.cpu)
        row = {}
        for n in names:
            exe = os.path.join(ROOT, DECODERS[n])
            if not os.path.exists(exe):
                row[n] = None
                continue
            probe = bench(exe, path, 3, a.cpu)
            if probe is None:
                row[n] = {"error": "failed"}
                continue
            iters = max(5, min(2000, int(a.seconds * 1e9 / max(probe[1], 1))))
            r = bench(exe, path, iters, a.cpu)
            ok = r[2] == ref[2]
            row[n] = {"min_ns": r[0], "median_ns": r[1], "iters": iters, "hash_ok": ok,
                      "mpx_s": w * h / r[1] * 1e3}
        results[im] = {"width": w, "height": h, "decoders": row}
        cells = []
        for n in names:
            c = row.get(n)
            if c is None:
                cells.append("-")
            elif "error" in c:
                cells.append("FAIL")
            else:
                cells.append(f"{c['mpx_s']:.1f}" + ("" if c["hash_ok"] else " BADHASH"))
        print(f"{im:<15}{w*h/1e6:>7.2f}" + "".join(f"{c:>14}" for c in cells), flush=True)
    # geometric mean of speed relative to qoi.h
    if "c-qoi.h" in names:
        print("\ngeomean speed vs qoi.h:")
        for n in names:
            rs = [r["decoders"][n]["mpx_s"] / r["decoders"]["c-qoi.h"]["mpx_s"] for r in results.values()
                  if r["decoders"].get(n) and "mpx_s" in r["decoders"][n]]
            if rs:
                g = 1.0
                for x in rs:
                    g *= x
                print(f"  {n:<12} {g ** (1 / len(rs)):.3f}x")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(results, f, indent=1)


if __name__ == "__main__":
    main()
