let
  default = import ./default.nix {};
  hsPkgs = default.project;
  pkgs = default.pkgs;
in
  hsPkgs.shellFor {
    packages = ps: with ps; [
      stridi
    ];

    withHoogle = false;
    # Prevents cabal from choosing alternate plans, so that
    # *all* dependencies are provided by Nix.
    exactDeps = true;

    # See overlays/tools.nix for more details
    tools = {
      cabal = "3.2.0.0";
      hlint = "2.2.11";
      hie = "unstable";
    };

    buildInputs = with pkgs.haskellPackages; [
      pkgs.texlive.combined.scheme-medium
      ghcid
    ];
  }
