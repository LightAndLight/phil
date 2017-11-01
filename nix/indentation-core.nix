{ mkDerivation, base, mtl, stdenv }:
mkDerivation {
  pname = "indentation-core";
  version = "0.0.0.1";
  sha256 = "136skn3parvsyfii0ywm8cqfmsysi562944fbb0xsgckx0sq1dr1";
  libraryHaskellDepends = [ base mtl ];
  homepage = "https://bitbucket.org/adamsmd/indentation";
  description = "Indentation sensitive parsing combinators core library";
  license = stdenv.lib.licenses.bsd3;
}
