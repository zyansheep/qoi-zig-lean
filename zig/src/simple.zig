//! The "conceptual" QOI decoder: a near-verbatim copy of the screenshot that
//! started this project. It is deliberately naive and does not validate input.
const std = @import("std");
const Allocator = std.mem.Allocator;
const readInt = std.mem.readInt;

pub const Color = extern struct {
    r: u8,
    g: u8,
    b: u8,
    a: u8,

    fn hash(c: Color) u6 {
        return @truncate(c.r *% 3 +% c.g *% 5 +% c.b *% 7 +% c.a *% 11);
    }
};

pub const Image = struct {
    pixels: []Color,
    width: u32,
    height: u32,
};

/// Decodes an image encoded in the Quite OK Image Format (https://qoiformat.org/).
///
/// Do not use this on untrusted data. This function makes no attempt to
/// validate its input.
pub fn decode(allocator: Allocator, bytes: []const u8) !Image {
    const width = readInt(u32, bytes[4..8], .big);
    const height = readInt(u32, bytes[8..12], .big);

    const pixels = try allocator.alloc(Color, @as(usize, width) * height);
    errdefer allocator.free(pixels);

    var color_table = std.mem.zeroes([64]Color);
    var color: Color = .{ .r = 0, .g = 0, .b = 0, .a = 255 };

    var pixel_index: usize = 0;
    var byte_index: usize = 14;

    while (pixel_index < pixels.len) {
        var run_length: usize = 1;
        switch (bytes[byte_index]) {
            0b11111110 => {
                color.r = bytes[byte_index + 1];
                color.g = bytes[byte_index + 2];
                color.b = bytes[byte_index + 3];
                byte_index += 3;
            },
            0b11111111 => {
                color.r = bytes[byte_index + 1];
                color.g = bytes[byte_index + 2];
                color.b = bytes[byte_index + 3];
                color.a = bytes[byte_index + 4];
                byte_index += 4;
            },
            else => |byte| {
                switch (@as(u2, @truncate(byte >> 6))) {
                    0b00 => color = color_table[byte & 0b111111],
                    0b01 => {
                        color.r = color.r +% ((byte >> 4) & 0b11) -% 2;
                        color.g = color.g +% ((byte >> 2) & 0b11) -% 2;
                        color.b = color.b +% (byte & 0b11) -% 2;
                    },
                    0b10 => {
                        const dg = byte & 0b111111;
                        const byte2 = bytes[byte_index + 1];
                        color.r = color.r +% dg +% (byte2 >> 4) -% 40;
                        color.g = color.g +% dg -% 32;
                        color.b = color.b +% dg +% (byte2 & 0b1111) -% 40;
                        byte_index += 1;
                    },
                    0b11 => run_length = (byte & 0b111111) + 1,
                }
            },
        }
        byte_index += 1;

        @memset(pixels[pixel_index .. pixel_index + run_length], color);
        pixel_index += run_length;

        color_table[color.hash()] = color;
    }

    return .{
        .pixels = pixels,
        .width = width,
        .height = height,
    };
}
