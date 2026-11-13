const std = @import("std");

pub fn main(init: std.process.Init) !u8 {
    return @import("cli.zig").run(@import("simple.zig"), init);
}
