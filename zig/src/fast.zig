//! Fast, safe QOI decoder.
//!
//! Matches `lean/QOI/Spec.lean` on every input (see bench/PROTOCOL.md): same accept/reject,
//! identical RGBA bytes, no out-of-bounds access. Single-threaded, safe Zig apart from a few
//! raw-pointer vector stores and one empty `asm volatile` used as an optimization barrier
//! (both explained where they occur). The optimization log is in zig/NOTES.md.
//!
//! Shape of the decoder:
//!
//! * A **fast loop** that runs while at least 5 chunk bytes (the longest chunk) and 64 output
//!   pixels are left, so it needs no per-chunk bounds checks, followed by a **careful tail** that
//!   checks every chunk exactly like the spec.
//! * The fast loop is **branch-free per opcode**: a table indexed by the tag byte turns every
//!   chunk into `px = ((prev & keep) | index[tag]) + add + pdep(payload, pmask)`, plus a length
//!   and a pixel count. Photo-like images have ~1 chunk per pixel with an unpredictable opcode
//!   sequence, so any `switch` on the opcode mispredicts constantly.
//! * Pixels are kept **"spread"**: r,g,b,a in the low byte of four 16-bit lanes of a u64, so the
//!   mod-256 per-channel add is a single 64-bit add (each lane's high byte absorbs the carry), and
//!   RGB/RGBA payload bytes are moved into lanes with one BMI2 `pdep`.
//! * The **next tag comes out of the 8-byte window already in a register** (`bextr` by a
//!   per-tag shift), so the sequential parse chain per chunk is one table load + one 1-cycle op.
//! * The **index write is delayed by one chunk** so its address (a hash of a pixel that was
//!   just computed) is never on the critical path of the following loads; an INDEX chunk that
//!   names the still-pending slot (never produced by an encoder) takes a cold branch.
//! * **Runs are overlapping 32-byte stores**: every chunk stores 8 copies of its pixel and
//!   advances by its count, so runs up to 8 cost nothing extra.
const std = @import("std");
const builtin = @import("builtin");
const Allocator = std.mem.Allocator;
const readInt = std.mem.readInt;

comptime {
    std.debug.assert(builtin.cpu.arch.endian() == .little);
}

pub const Image = struct {
    pixels: []u32,
    width: u32,
    height: u32,
};

const max_pixels: u64 = 400_000_000;

/// Lane mask of a spread pixel: r at bits 0..7, g at 16..23, b at 32..39, a at 48..55.
const LANE: u64 = 0x00FF_00FF_00FF_00FF;

fn spreadRgba(r: u8, g: u8, b: u8, a: u8) u64 {
    return @as(u64, r) | @as(u64, g) << 16 | @as(u64, b) << 32 | @as(u64, a) << 48;
}

// ---------------------------------------------------------------------------------------------
// BMI1/BMI2 (with portable fallbacks, so the file also builds for other targets).

const has_bmi = builtin.cpu.arch == .x86_64 and
    std.Target.x86.featureSetHas(builtin.cpu.features, .bmi2) and
    std.Target.x86.featureSetHas(builtin.cpu.features, .bmi);
extern fn @"llvm.x86.bmi.pdep.64"(u64, u64) u64;
extern fn @"llvm.x86.bmi.bextr.64"(u64, u64) u64;

/// Deposit the low bits of `x` into the set bits of `mask` (BMI2 `pdep`).
inline fn pdep(x: u64, mask: u64) u64 {
    if (has_bmi) return @"llvm.x86.bmi.pdep.64"(x, mask);
    var r: u64 = 0;
    var m = mask;
    var bit: u64 = 1;
    while (m != 0) : (m &= m - 1) {
        if (x & bit != 0) r |= m & (~m +% 1);
        bit <<= 1;
    }
    return r;
}

/// The byte of `w` starting at bit `ctrl & 0xFF` (BMI1 `bextr`; ctrl bits 8..15 hold the
/// length, always 8 here).
inline fn bextr(w: u64, ctrl: u64) u64 {
    if (has_bmi) return @"llvm.x86.bmi.bextr.64"(w, ctrl);
    return (w >> @intCast(ctrl & 63)) & 0xFF;
}

// ---------------------------------------------------------------------------------------------
// The opcode table.
//
// Structure-of-arrays: field F of tag t lives at table[F * 256 + t], so every field is a load
// from `base + F*2048 + t*8` (one base register, no index arithmetic on the tag chain).

const F_KEEP = 0; // lanes of prev that survive (LANE; alpha only for RGB; 0 for INDEX/RGBA)
const F_ADD = 1; // constant per-lane delta (DIFF, LUMA's dg part)
const F_PMASK = 2; // pdep mask placing payload bytes into lanes (RGB, RGBA), else 0
const F_LMASK = 3; // selects the LUMA nibble deltas (LUMA only)
const F_LEN = 4; // chunk length in bytes
const F_CTRL = 5; // bextr control picking the byte after this chunk: (8 << 8) | 8*len
const F_CNT = 6; // pixels produced (run length for RUN, else 1)
const NF = 7;
const LUMA = NF * 256; // then 256 entries: LUMA second byte -> spread (dr_dg, 0, db_dg, 0)

const table: [NF * 256 + 256]u64 = blk: {
    @setEvalBranchQuota(20000);
    var t: [NF * 256 + 256]u64 = undefined;
    for (0..256) |i| {
        const tag: u8 = i;
        var e = [NF]u64{ LANE, 0, 0, 0, 1, 0, 1 };
        if (tag == 0xFE) { // QOI_OP_RGB: keep alpha, r,g,b from the payload
            e[F_KEEP] = 0x00FF << 48;
            e[F_PMASK] = 0x0000_00FF_00FF_00FF;
            e[F_LEN] = 4;
        } else if (tag == 0xFF) { // QOI_OP_RGBA
            e[F_KEEP] = 0;
            e[F_PMASK] = LANE;
            e[F_LEN] = 5;
        } else switch (tag >> 6) {
            0 => e[F_KEEP] = 0, // QOI_OP_INDEX: the pixel is index[tag] (see `index` below)
            1 => e[F_ADD] = spreadRgba(((tag >> 4) & 3) -% 2, ((tag >> 2) & 3) -% 2, (tag & 3) -% 2, 0),
            2 => { // QOI_OP_LUMA: dg from the tag, (dr-dg, db-dg) nibbles from the next byte
                const dg: u8 = (tag & 63) -% 32;
                e[F_ADD] = spreadRgba(dg -% 8, dg, dg -% 8, 0);
                e[F_LMASK] = 0x0000_000F_0000_000F;
                e[F_LEN] = 2;
            },
            else => e[F_CNT] = (tag & 63) + 1, // QOI_OP_RUN (tags 0xFE/0xFF handled above)
        }
        e[F_CTRL] = (8 << 8) | (8 * e[F_LEN]);
        for (0..NF) |f| t[f * 256 + i] = e[f];
    }
    for (0..256) |i| t[LUMA + i] = (i >> 4) | ((i & 15) << 32);
    break :blk t;
};

inline fn field(comptime f: usize, tag: u64) u64 {
    return table[f * 256 + tag];
}

// ---------------------------------------------------------------------------------------------
// Pixel helpers.

/// Index slot of a spread pixel: one multiply puts r*3 + g*5 + b*7 + a*11 at bits 58..63.
/// Lanes of a freshly computed pixel may hold carries above bit 7 (each lane is a sum of at
/// most four bytes, so < 1024). Then every lower partial sum stays < 2^57 (cannot reach bit 58)
/// and the extra multiples of 256 in a lane vanish mod 64, so no masking is needed.
inline fn hash(px: u64) u64 {
    return (px *% (0x0003_0005_0007_000B << 10)) >> 58;
}

/// Spread pixel -> RGBA u32 (the low byte of each lane).
inline fn pack(px: u64) u32 {
    const v: @Vector(8, u8) = @bitCast(px);
    return @bitCast(@shuffle(u8, v, undefined, [4]i32{ 0, 2, 4, 6 }));
}

/// RGBA u32 -> spread pixel.
inline fn spread(c: u32) u64 {
    return pdep(c, LANE);
}

inline fn rgba32(r: u8, g: u8, b: u8, a: u8) u32 {
    return @as(u32, r) | @as(u32, g) << 8 | @as(u32, b) << 16 | @as(u32, a) << 24;
}

/// Store 8 copies of `px` at out[o..o+8]. The caller guarantees o + 8 <= n.
inline fn fill8(out: [*]u32, o: usize, px: u32) void {
    @as(*align(4) @Vector(8, u32), @ptrCast(out + o)).* = @splat(px);
}

// ---------------------------------------------------------------------------------------------

pub fn decode(allocator: Allocator, bytes: []const u8) !Image {
    // Header, exactly as the spec: magic, dimensions, channels, colorspace, pixel limit, and
    // room for the 8-byte end marker (which is not inspected).
    if (bytes.len < 14 + 8) return error.Invalid;
    if (!std.mem.eql(u8, bytes[0..4], "qoif")) return error.Invalid;
    const width = readInt(u32, bytes[4..8], .big);
    const height = readInt(u32, bytes[8..12], .big);
    const channels = bytes[12];
    const colorspace = bytes[13];
    if (channels != 3 and channels != 4) return error.Invalid;
    if (colorspace > 1) return error.Invalid;
    const n64 = @as(u64, width) * height; // both < 2^32: no overflow
    if (n64 > max_pixels) return error.Invalid;
    const n: usize = @intCast(n64);
    const end = bytes.len - 8; // chunks live in bytes[14..end]
    // Every chunk byte yields at most 62 pixels; if even that cannot reach n the spec runs out
    // of chunks, so reject now instead of allocating up to 1.6 GB for a tiny file.
    if ((n + 61) / 62 > end - 14) return error.Invalid;

    const pixels = try allocator.alloc(u32, n);
    errdefer allocator.free(pixels);
    const out = pixels.ptr;

    // index[0..64] is the QOI index. index[64..256] stay zero forever, so the hot loop can load
    // index[tag] for any tag without masking: non-INDEX tags read 0, which ORs away. index[256]
    // is a scratch slot that no tag can name (see `hp`).
    var index: [257]u64 = @splat(0);
    var prev: u64 = spreadRgba(0, 0, 0, 255);
    var p: usize = 14; // next chunk
    var o: usize = 0; // next output pixel

    // Fast loop: runs while p <= end - 5 (the whole chunk at p, up to 5 bytes, is inside the
    // chunk area, and so is every 8-byte load at p since p + 8 <= end + 8 = bytes.len) and
    // o <= n - 64 (the longest run, 62, plus rounding up to whole 8-pixel stores fits).
    if (end >= 14 + 5 and n >= 64) {
        const p_lim = end - 5;
        const o_lim = n - 64;
        var w = readInt(u64, bytes[p..][0..8], .little); // window starting at the current chunk
        var tag: u64 = w & 0xFF;
        // The index write for `prev` is held back one chunk: `hp` is its slot. The initial
        // prev is not in the index, so it starts out "pending" at the scratch slot.
        var hp: u64 = 256;
        while (p <= p_lim and o <= o_lim) {
            // Each chunk consumes >= 1 byte and produces <= 62 pixels, so as long as every chunk
            // starts at or before p_blk, both limits above hold for it: the inner loop needs
            // a single compare per chunk.
            const p_blk = p + @min(p_lim - p, (o_lim - o) / 62);
            while (p <= p_blk) {
                // Parse chain first, so its loads issue ahead of the pixel math's: the next tag
                // is a byte of the window we already hold (len <= 5 < 8), and the next window
                // load only needs this chunk's length.
                const t = tag;
                const cur = w;
                tag = bextr(cur, field(F_CTRL, t));
                p += field(F_LEN, t);
                w = readInt(u64, bytes[p..][0..8], .little);

                // Payload bytes 1..4 of this chunk (bits 32..63 never matter: pmask and the
                // LUMA byte only look at the low 32).
                const x = std.math.rotr(u64, cur, 8);
                const d = field(F_ADD, t) +% pdep(x, field(F_PMASK, t)) +%
                    (table[LUMA + (x & 0xFF)] & field(F_LMASK, t));

                // The index write of the previous pixel is delayed by one chunk, so its store
                // address (a hash of a pixel just computed) is not on the critical path of this
                // chunk's loads. An INDEX chunk naming that still-pending slot must see `prev`;
                // encoder output never does that (it would be a RUN), so it is a cold branch.
                // The empty asm keeps LLVM from if-converting it into a cmov, which would put
                // the hash back on the critical path.
                var ix = index[t];
                if (t == hp) {
                    @branchHint(.cold);
                    asm volatile ("" ::: .{ .memory = true });
                    ix = prev;
                }
                const px = ((prev & field(F_KEEP, t)) | ix) +% d;

                const px32 = pack(px);
                fill8(out, o, px32);
                const cnt = field(F_CNT, t);
                if (cnt > 8) {
                    @branchHint(.unlikely);
                    inline for (1..8) |k| fill8(out, o + 8 * k, px32);
                }
                o += cnt;
                index[hp] = prev;
                hp = hash(px);
                prev = px;
            }
        }
        index[hp] = prev;
    }

    // Careful tail: one chunk at a time with every bounds check of the spec. Runs are truncated
    // to the pixels still missing; running out of chunk bytes is an error.
    var cur = pack(prev);
    var idx32: [64]u32 = undefined;
    for (&idx32, index[0..64]) |*a, b| a.* = pack(b);
    while (o < n) {
        if (p >= end) return error.Invalid;
        const tag = bytes[p];
        var cnt: usize = 1;
        if (tag == 0xFE) {
            if (end - p < 4) return error.Invalid;
            cur = rgba32(bytes[p + 1], bytes[p + 2], bytes[p + 3], @truncate(cur >> 24));
            p += 4;
        } else if (tag == 0xFF) {
            if (end - p < 5) return error.Invalid;
            cur = rgba32(bytes[p + 1], bytes[p + 2], bytes[p + 3], bytes[p + 4]);
            p += 5;
        } else switch (tag >> 6) {
            0 => {
                cur = idx32[tag];
                p += 1;
            },
            1 => {
                cur = pack(spread(cur) +% field(F_ADD, tag));
                p += 1;
            },
            2 => {
                if (end - p < 2) return error.Invalid;
                cur = pack(spread(cur) +% field(F_ADD, tag) +% table[LUMA + @as(usize, bytes[p + 1])]);
                p += 2;
            },
            else => {
                cnt = @min(@as(usize, tag & 63) + 1, n - o);
                p += 1;
            },
        }
        @memset(pixels[o..][0..cnt], cur);
        o += cnt;
        idx32[hash(spread(cur))] = cur;
    }

    return .{ .pixels = pixels, .width = width, .height = height };
}
