// Reference decoder: phoboslab's qoi.h behind the shared CLI protocol (see bench/PROTOCOL.md).
// Used as an independent oracle for valid images and as a well-known speed reference.
#define QOI_IMPLEMENTATION
#define QOI_NO_STDIO
#include "qoi.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static unsigned char *read_file(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); exit(2); }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    unsigned char *buf = malloc(n > 0 ? n : 1);
    if (n > 0 && fread(buf, 1, n, f) != (size_t)n) { perror("read"); exit(2); }
    fclose(f);
    *len = (size_t)n;
    return buf;
}

static uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ull + ts.tv_nsec;
}

static uint64_t fnv1a(const unsigned char *p, size_t n) {
    uint64_t h = 0xcbf29ce484222325ull;
    for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 0x100000001b3ull; }
    return h;
}

static int cmp_u64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return (x > y) - (x < y);
}

int main(int argc, char **argv) {
    if (argc != 4) {
        fprintf(stderr, "usage: %s decode <in.qoi> <out.rgba> | bench <in.qoi> <iters>\n", argv[0]);
        return 2;
    }
    size_t len;
    unsigned char *data = read_file(argv[2], &len);
    qoi_desc desc;
    if (strcmp(argv[1], "decode") == 0) {
        unsigned char *px = qoi_decode(data, (int)len, &desc, 4);
        if (!px) { fprintf(stderr, "invalid\n"); return 1; }
        FILE *f = fopen(argv[3], "wb");
        fwrite(px, 1, (size_t)desc.width * desc.height * 4, f);
        fclose(f);
        return 0;
    }
    if (strcmp(argv[1], "bench") == 0) {
        int iters = atoi(argv[3]);
        uint64_t *t = malloc(sizeof(uint64_t) * iters);
        uint64_t sink = 0;
        for (int i = 0; i < iters; i++) {
            uint64_t t0 = now_ns();
            unsigned char *px = qoi_decode(data, (int)len, &desc, 4);
            t[i] = now_ns() - t0;
            if (!px) { fprintf(stderr, "invalid\n"); return 1; }
            sink += px[(size_t)i * 7919 % ((size_t)desc.width * desc.height * 4)];
            if (i == iters - 1) {
                qsort(t, iters, sizeof(uint64_t), cmp_u64);
                printf("%llu %llu %016llx\n", (unsigned long long)t[0], (unsigned long long)t[iters / 2],
                       (unsigned long long)fnv1a(px, (size_t)desc.width * desc.height * 4));
            }
            free(px);
        }
        fprintf(stderr, "sink %llu\n", (unsigned long long)sink);
        return 0;
    }
    return 2;
}
