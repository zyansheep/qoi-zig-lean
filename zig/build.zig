const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{ .preferred_optimize_mode = .ReleaseFast });

    inline for (.{ .{ "qoi-zig-simple", "src/main_simple.zig" }, .{ "qoi-zig-fast", "src/main_fast.zig" } }) |e| {
        const exe = b.addExecutable(.{
            .name = e[0],
            .root_module = b.createModule(.{
                .root_source_file = b.path(e[1]),
                .target = target,
                .optimize = optimize,
                .link_libc = true,
            }),
        });
        b.installArtifact(exe);
    }
}
