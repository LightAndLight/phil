let pkgs = import <nixpkgs> { };
in pkgs.haskell.packages.ghc802.callPackage ./hindley-milner.nix { }
