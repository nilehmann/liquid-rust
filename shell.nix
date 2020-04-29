let
  moz_overlay = import (builtins.fetchTarball https://github.com/mozilla/nixpkgs-mozilla/archive/master.tar.gz);
  nixpkgs = import <nixpkgs> { overlays = [ moz_overlay ]; };
in
  with nixpkgs;
  stdenv.mkDerivation {
    name = "lr_shell";
    buildInputs = [
      z3
      rust-analyzer
      # to use a specific nighly:
      ((nixpkgs.rustChannelOf { date = "2020-04-22"; channel = "nightly"; }).rust.override { extensions = [ "rust-src" "rust-analysis" "rustc-dev" ]; })
    ];
  }