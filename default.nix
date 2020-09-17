# This uses haskell.nix: https://input-output-hk.github.io/haskell.nix
let
  sources = import ./nix/sources.nix;
  haskellNix = import sources.haskell-nix {};
  all-hies = import sources.all-hies {};
  nixpkgsSrc = haskellNix.sources.nixpkgs-2003;
  nixpkgsArgs = haskellNix.nixpkgsArgs // {
    overlays = haskellNix.nixpkgsArgs.overlays ++ [ all-hies.overlay ];
  };
in
{ pkgs ? import nixpkgsSrc nixpkgsArgs }:

{
  inherit pkgs;
  project = pkgs.haskell-nix.stackProject {
    src = pkgs.haskell-nix.haskellLib.cleanGit {
      name = "stridi";
      src = ./.;
    };
  };
}
