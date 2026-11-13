#!/usr/bin/env python3
"""Differential fuzzer: every decoder must agree with the executable Lean spec on every input.

    python3 bench/fuzz.py [--n 3000] [--seed S] [--only zig-fast,lean-fast]

Inputs: random chunk streams behind valid headers (biased toward each opcode and toward
truncation at chunk boundaries), mutated and truncated real files, and broken headers.
"Agree" means: same accept/reject decision, and identical RGBA bytes when accepted.
zig-simple does no validation by design and is not fuzzed.
"""
import argparse, os, random, struct, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXES = {
    "zig-fast": "zig/zig-out/bin/qoi-zig-fast",
    "lean-fast": "lean/.lake/build/bin/qoi-lean-fast",
}
SPEC = "lean/.lake/build/bin/qoi-lean-spec"
END = bytes([0, 0, 0, 0, 0, 0, 0, 1])


def header(w, h, ch=4, cs=0):
    return b"qoif" + struct.pack(">II", w, h) + bytes([ch, cs])


def rand_chunk(r):
    k = r.random()
    if k < 0.15:
        return bytes([0xFE, r.randrange(256), r.randrange(256), r.randrange(256)])
    if k < 0.25:
        return bytes([0xFF] + [r.randrange(256) for _ in range(4)])
    if k < 0.45:
        return bytes([r.randrange(64)])  # INDEX
    if k < 0.65:
        return bytes([0x40 | r.randrange(64)])  # DIFF
    if k < 0.85:
        return bytes([0x80 | r.randrange(64), r.randrange(256)])  # LUMA
    return bytes([0xC0 | r.randrange(62)])  # RUN (62, 63 are RGB/RGBA tags)


def gen(r, seeds):
    k = r.random()
    if k < 0.55:  # random stream behind a valid header
        w, h = r.randrange(0, 24), r.randrange(0, 24)
        body = b"".join(rand_chunk(r) for _ in range(r.randrange(0, w * h + 8)))
        if r.random() < 0.3:
            body = body[: r.randrange(0, len(body) + 1)]
        tail = END if r.random() < 0.8 else bytes(r.randrange(256) for _ in range(r.randrange(0, 12)))
        return header(w, h, r.choice([3, 4]), r.choice([0, 1])) + body + tail
    if k < 0.85 and seeds:  # mutate a real file
        b = bytearray(r.choice(seeds))
        for _ in range(r.randrange(1, 6)):
            op = r.random()
            if op < 0.5 and len(b) > 14:
                b[r.randrange(14, len(b))] = r.randrange(256)
            elif op < 0.7:
                b = b[: r.randrange(0, len(b) + 1)]
            elif op < 0.85 and len(b) > 14:
                i = r.randrange(14, len(b))
                del b[i: i + r.randrange(1, 4)]
            else:
                i = r.randrange(min(14, len(b)), len(b) + 1)
                b[i:i] = bytes(r.randrange(256) for _ in range(r.randrange(1, 4)))
        return bytes(b)
    # broken / extreme headers
    w = r.choice([0, 1, 2, 20000, 20001, 65536, 2**31, 2**32 - 1, r.randrange(2**32)])
    h = r.choice([0, 1, 2, 20000, 20001, 65536, 2**31, 2**32 - 1, r.randrange(2**32)])
    b = bytearray(header(w, h, r.choice([3, 4, 0, 5, 255]), r.choice([0, 1, 2, 255])))
    if r.random() < 0.2:
        b[r.randrange(4)] ^= 1 << r.randrange(8)
    b += bytes([0xC0 | 61] * r.randrange(0, 40)) + END
    return bytes(b[: r.randrange(0, len(b) + 1)] if r.random() < 0.2 else b)


def decode(exe, path, out):
    if os.path.exists(out):
        os.remove(out)
    p = subprocess.run([exe, "decode", path, out], capture_output=True, timeout=60)
    if p.returncode == 0:
        with open(out, "rb") as f:
            return ("ok", f.read())
    if p.returncode == 1 and b"invalid" in p.stderr:
        return ("invalid", b"")
    return ("crash", f"rc={p.returncode} {p.stderr[-300:]!r}".encode())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=3000)
    ap.add_argument("--seed", type=int, default=None)
    ap.add_argument("--only", default=None)
    a = ap.parse_args()
    seed = a.seed if a.seed is not None else random.randrange(2**32)
    r = random.Random(seed)
    names = a.only.split(",") if a.only else list(EXES)
    names = [n for n in names if os.path.exists(os.path.join(ROOT, EXES[n]))]
    seeds = [open(os.path.join(ROOT, "testdata", f), "rb").read()
             for f in ["edgecase.qoi", "testcard.qoi", "testcard_rgba.qoi", "qoi_logo.qoi"]]
    tmp = tempfile.mkdtemp(prefix="qoifuzz")
    inp = os.path.join(tmp, "in.qoi")
    fails = 0
    stats = {"ok": 0, "invalid": 0}
    print(f"seed {seed}; decoders {names}")
    for i in range(a.n):
        data = gen(r, seeds)
        with open(inp, "wb") as f:
            f.write(data)
        want = decode(os.path.join(ROOT, SPEC), inp, os.path.join(tmp, "spec.rgba"))
        if want[0] == "crash":
            print(f"spec crashed on case {i}: {want[1]!r}")
            continue
        stats[want[0]] += 1
        for n in names:
            got = decode(os.path.join(ROOT, EXES[n]), inp, os.path.join(tmp, n + ".rgba"))
            if got != want:
                fails += 1
                keep = os.path.join(tmp, f"fail_{n}_{i}.qoi")
                with open(keep, "wb") as f:
                    f.write(data)
                print(f"MISMATCH {n} case {i}: want {want[0]} got {got[0]} "
                      f"{got[1][:80]!r} -> saved {keep}")
        if (i + 1) % 500 == 0:
            print(f"  {i + 1} cases, {fails} mismatches, spec accepted {stats['ok']} / rejected {stats['invalid']}",
                  flush=True)
    print(f"done: {a.n} cases, {fails} mismatches (seed {seed})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
