# This uses haskell.nix: https://input-output-hk.github.io/haskell.nix
let
  sources = import ./nix/sources.nix;
  haskellNix = import sources.haskell-nix {};
  nixpkgsSrc = haskellNix.sources.nixpkgs-2003;
  nixpkgsArgs = haskellNix.nixpkgsArgs;
in
{ pkgs ? import nixpkgsSrc nixpkgsArgs }:

{
  inherit pkgs;
  project = pkgs.haskell-nix.project {
    src = pkgs.haskell-nix.haskellLib.cleanGit {
      name = "stridi";
      src = ./.;
    };
  };
}
