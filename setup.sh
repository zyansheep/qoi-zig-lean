#!/usr/bin/env sh
# Fetch the test images, build the C reference + synthetic images, the Zig decoders and the Lean decoders.
# Run inside `nix-shell` (zig 0.16, lean 4.34, gcc, python3).
set -e
cd "$(dirname "$0")"
mkdir -p build testdata
if [ ! -f testdata/kodim10.qoi ]; then
  curl -sSL -o build/qoi_test_images.zip https://qoiformat.org/qoi_test_images.zip
  (cd testdata && unzip -q -o -j ../build/qoi_test_images.zip 'qoi_test_images/*.qoi')
fi
gcc -O3 -march=native -o build/qoi-ref ref/qoi_ref.c
gcc -O2 -o build/gen ref/gen.c
[ -f testdata/synth_photo.qoi ] || build/gen photo testdata/synth_photo.qoi
[ -f testdata/synth_flat.qoi ] || build/gen flat testdata/synth_flat.qoi
(cd zig && zig build --release=fast -Dcpu=native)
(cd lean && lake build)
