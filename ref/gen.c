// Generates the large synthetic benchmark images with qoi.h's encoder.
//   gen photo  out.qoi   4096x4096 RGB smooth gradients + noise (DIFF/LUMA/RGB heavy)
//   gen flat   out.qoi   4096x4096 RGBA flat UI-like rectangles (RUN/INDEX heavy)
#define QOI_IMPLEMENTATION
#include "qoi.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint32_t rng = 0x12345678u;
static uint32_t next(void) { rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5; return rng; }

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: gen photo|flat out.qoi\n"); return 2; }
    const int w = 4096, h = 4096;
    int channels = strcmp(argv[1], "flat") == 0 ? 4 : 3;
    unsigned char *px = malloc((size_t)w * h * channels);
    if (channels == 3) {
        for (int y = 0; y < h; y++)
            for (int x = 0; x < w; x++) {
                unsigned char *p = px + ((size_t)y * w + x) * 3;
                int n = (int)(next() % 7) - 3;
                int r = (x * 255 / w) + n, g = (y * 255 / h) + n, b = ((x + y) * 127 / w) + (int)(next() % 5) - 2;
                if ((x / 512 + y / 512) % 3 == 0) { r += (int)(next() % 41) - 20; }
                p[0] = r < 0 ? 0 : r > 255 ? 255 : r;
                p[1] = g < 0 ? 0 : g > 255 ? 255 : g;
                p[2] = b < 0 ? 0 : b > 255 ? 255 : b;
            }
    } else {
        static const uint32_t palette[] = {0xffffffff, 0xff202020, 0xff3070e0, 0xfff0f0f0, 0x80000000,
                                           0xff40c060, 0xffe04040, 0x00000000, 0xffc0c0c0, 0xff1a1a2e};
        for (size_t i = 0; i < (size_t)w * h; i++) memcpy(px + i * 4, &palette[0], 4);
        for (int k = 0; k < 6000; k++) {
            int x0 = next() % w, y0 = next() % h, rw = 4 + next() % 400, rh = 2 + next() % 120;
            uint32_t c = palette[next() % 10];
            for (int y = y0; y < y0 + rh && y < h; y++)
                for (int x = x0; x < x0 + rw && x < w; x++) memcpy(px + ((size_t)y * w + x) * 4, &c, 4);
        }
        // text-like noise: short runs of 1-3 px glyph strokes
        for (int k = 0; k < 400000; k++) {
            int x = next() % w, y = next() % h;
            uint32_t c = palette[1 + next() % 3];
            memcpy(px + ((size_t)y * w + x) * 4, &c, 4);
        }
    }
    qoi_desc desc = {.width = w, .height = h, .channels = channels, .colorspace = QOI_SRGB};
    if (!qoi_write(argv[2], px, &desc)) { fprintf(stderr, "write failed\n"); return 1; }
    return 0;
}
