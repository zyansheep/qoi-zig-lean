{ pkgs ? import <nixpkgs> { } }:
pkgs.mkShell {
  packages = [ pkgs.zig pkgs.lean4 pkgs.gcc pkgs.hyperfine pkgs.python3 ];
  # The cc wrapper drops -march=native unless told otherwise; every decoder here is built for the host CPU.
  shellHook = "export NIX_ENFORCE_NO_NATIVE=0 NIX_ENFORCE_NO_NATIVE_x86_64_unknown_linux_gnu=0";
}
