{ mkDerivation, attoparsec, base, base-orphans, bytestring, Cabal
, cabal-doctest, charset, containers, directory, doctest, filepath
, mtl, parsec, QuickCheck, quickcheck-instances, scientific
, semigroups, stdenv, text, transformers, unordered-containers
}:
mkDerivation {
  pname = "parsers";
  version = "0.12.7";
  sha256 = "032dgh0ydy4cbvnjhgp0krnqnvlibphvm30gvmqvpxk9l4pmn435";
  setupHaskellDepends = [ base Cabal cabal-doctest ];
  libraryHaskellDepends = [
    attoparsec base base-orphans charset containers mtl parsec
    scientific semigroups text transformers unordered-containers
  ];
  testHaskellDepends = [
    attoparsec base bytestring containers directory doctest filepath
    parsec QuickCheck quickcheck-instances
  ];
  homepage = "http://github.com/ekmett/parsers/";
  description = "Parsing combinators";
  license = stdenv.lib.licenses.bsd3;
}
