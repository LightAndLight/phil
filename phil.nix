{ mkDerivation, ansi-wl-pprint, array, base, bifunctors, containers
, directory, dlist, filepath, free, haskeline, hspec
, indentation-trifecta, lens, mtl, optparse-applicative, parsers
, QuickCheck, semigroups, stdenv, text, trifecta
, unordered-containers
}:
mkDerivation {
  pname = "phil";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    ansi-wl-pprint array base bifunctors containers dlist free
    indentation-trifecta lens mtl parsers semigroups text trifecta
    unordered-containers
  ];
  executableHaskellDepends = [
    ansi-wl-pprint base bifunctors containers directory filepath free
    haskeline lens mtl optparse-applicative semigroups text trifecta
  ];
  testHaskellDepends = [
    base containers hspec lens mtl QuickCheck semigroups text
  ];
  homepage = "https://gitlab.com/lightandlight/phil";
  description = "Initial project template from stack";
  license = stdenv.lib.licenses.bsd3;
}
