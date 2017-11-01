{ mkDerivation, base, indentation-core, mtl, parsers, stdenv, tasty
, tasty-hunit, trifecta
}:
mkDerivation {
  pname = "indentation-trifecta";
  version = "0.0.2";
  sha256 = "0d2mxd1cdcr0zfz618dh4grin4z2bjfv4659i2zsddxm9li0dqis";
  libraryHaskellDepends = [
    base indentation-core mtl parsers trifecta
  ];
  testHaskellDepends = [ base tasty tasty-hunit trifecta ];
  homepage = "https://bitbucket.org/adamsmd/indentation";
  description = "Indentation sensitive parsing combinators for Trifecta";
  license = stdenv.lib.licenses.bsd3;
}
