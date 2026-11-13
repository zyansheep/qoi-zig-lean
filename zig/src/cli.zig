//! Shared command-line driver for the Zig decoders. Protocol (bench/PROTOCOL.md):
//!   <exe> decode <in.qoi> <out.rgba>   write raw RGBA8 pixels; exit 1 + "invalid" on rejected input
//!   <exe> bench  <in.qoi> <iters>      print "<min_ns> <median_ns> <fnv1a64 of RGBA hex>"
const std = @import("std");

fn fnv1a(bytes: []const u8) u64 {
    var h: u64 = 0xcbf29ce484222325;
    for (bytes) |b| {
        h ^= b;
        h *%= 0x100000001b3;
    }
    return h;
}

pub fn run(comptime decoder: type, init: std.process.Init) !u8 {
    const gpa = std.heap.c_allocator;
    const io = init.io;
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    if (args.len != 4) {
        std.debug.print("usage: {s} decode <in.qoi> <out.rgba> | bench <in.qoi> <iters>\n", .{args[0]});
        return 2;
    }
    const cwd = std.Io.Dir.cwd();
    const data = try cwd.readFileAlloc(io, args[2], gpa, .unlimited);
    defer gpa.free(data);

    if (std.mem.eql(u8, args[1], "decode")) {
        const img = decoder.decode(gpa, data) catch {
            std.debug.print("invalid\n", .{});
            return 1;
        };
        defer gpa.free(img.pixels);
        try cwd.writeFile(io, .{ .sub_path = args[3], .data = std.mem.sliceAsBytes(img.pixels) });
        return 0;
    }
    if (std.mem.eql(u8, args[1], "bench")) {
        const iters = try std.fmt.parseInt(usize, args[3], 10);
        const times = try gpa.alloc(u64, iters);
        defer gpa.free(times);
        var hash: u64 = 0;
        for (0..iters) |i| {
            const t0 = std.Io.Timestamp.now(io, .awake);
            const img = decoder.decode(gpa, data) catch {
                std.debug.print("invalid\n", .{});
                return 1;
            };
            const t1 = std.Io.Timestamp.now(io, .awake);
            times[i] = @intCast(t0.durationTo(t1).nanoseconds);
            std.mem.doNotOptimizeAway(img.pixels.ptr);
            if (i == iters - 1) hash = fnv1a(std.mem.sliceAsBytes(img.pixels));
            gpa.free(img.pixels);
        }
        std.mem.sort(u64, times, {}, std.sort.asc(u64));
        var buf: [128]u8 = undefined;
        const line = try std.fmt.bufPrint(&buf, "{d} {d} {x:0>16}\n", .{ times[0], times[iters / 2], hash });
        try std.Io.File.stdout().writeStreamingAll(io, line);
        return 0;
    }
    return 2;
}
