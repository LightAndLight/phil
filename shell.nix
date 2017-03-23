{ nixpkgs ? import <nixpkgs> {}, compiler ? "default" }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, alex, array, base, bifunctors, containers
      , directory, dlist, filepath, free, happy, haskeline, hspec, lens
      , mtl, optparse-applicative, QuickCheck, semigroups, stdenv
      }:
      mkDerivation {
        pname = "hindley-milner";
        version = "0.1.0.0";
        src = ./.;
        isLibrary = true;
        isExecutable = true;
        libraryHaskellDepends = [
          array base bifunctors containers dlist lens mtl semigroups
        ];
        libraryToolDepends = [ alex happy ];
        executableHaskellDepends = [
          base bifunctors containers directory filepath free haskeline lens
          mtl optparse-applicative semigroups
        ];
        testHaskellDepends = [
          base containers hspec lens mtl QuickCheck semigroups
        ];
        testToolDepends = [ alex happy ];
        homepage = "https://github.com/githubuser/hindley-milner#readme";
        description = "Initial project template from stack";
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  drv = haskellPackages.callPackage f {};

in

  if pkgs.lib.inNixShell then drv.env else drv
