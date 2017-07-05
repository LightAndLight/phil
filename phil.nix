{ mkDerivation, alex, array, base, bifunctors, containers
, directory, dlist, filepath, free, happy, haskeline, hspec, lens
, mtl, optparse-applicative, pretty, QuickCheck, semigroups, stdenv
}:
mkDerivation {
  pname = "phil";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    array base bifunctors containers dlist free lens mtl pretty
    semigroups
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
  homepage = "https://gitlab.com/lightandlight/phil";
  description = "A pure functional language that compiles to PHP";
  license = stdenv.lib.licenses.bsd3;

  doHaddock = false; # Haddock template haskell bug
}
