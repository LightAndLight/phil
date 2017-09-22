{ mkDerivation, ansi-terminal, ansi-wl-pprint, array, base
, blaze-builder, blaze-html, blaze-markup, bytestring, Cabal
, cabal-doctest, charset, comonad, containers, deepseq, doctest
, fingertree, ghc-prim, hashable, lens, mtl, parsers, profunctors
, QuickCheck, reducers, semigroups, stdenv, transformers
, unordered-containers, utf8-string
}:
mkDerivation {
  pname = "trifecta";
  version = "1.7.1.1";
  sha256 = "13n6a3fdxngnzsjnhfrzigv1c2g0xm6lqkjcnirpc37sd0rpby31";
  revision = "1";
  editedCabalFile = "cf6e18b4eb5611a7c00fdf7b89f9ff031539cb63d336fe9126a7325ccf08299e";
  setupHaskellDepends = [ base Cabal cabal-doctest ];
  libraryHaskellDepends = [
    ansi-terminal ansi-wl-pprint array base blaze-builder blaze-html
    blaze-markup bytestring charset comonad containers deepseq
    fingertree ghc-prim hashable lens mtl parsers profunctors reducers
    semigroups transformers unordered-containers utf8-string
  ];
  testHaskellDepends = [ base doctest parsers QuickCheck ];
  homepage = "http://github.com/ekmett/trifecta/";
  description = "A modern parser combinator library with convenient diagnostics";
  license = stdenv.lib.licenses.bsd3;
}
