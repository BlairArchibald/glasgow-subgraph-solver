{ pkgs ? import <nixpkgs> {} }:

with pkgs;

mkShell {
  buildInputs = [
    boost
    cmake
    cmakeCurses
  ];
}
