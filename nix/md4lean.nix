{
  lib,
  buildLakePackage,
  fetchFromGitHub,
}:
let
  src = fetchFromGitHub {
    owner = "acmepjz";
    repo = "md4lean";
    rev = "6a3fb240133bcb7e1a066fdc784b3fdc304e3fc5";
    hash = "sha256-sPSMZd9J8IN3OLj/E2sLxgqM1jMq7b3+5ReFkMBpQcw=";
  };
in
buildLakePackage {
  pname = "lean4-md4lean";
  version = "main";
  inherit src;

  leanPackageName = "MD4Lean";

  passthru.tests.md4lean-test = buildLakePackage {
    pname = "lean4-md4lean-test";
    version = "main";
    inherit src;

    leanPackageName = "MD4LeanTest";

    buildTargets = [ "MD4LeanTest" ];
  };

  # Verso tries to build these and fails to write to nix store
  postPatch = ''
    substituteInPlace lakefile.lean \
      --replace-fail 'lean_lib MD4Lean where' 'lean_lib MD4Lean where
      defaultFacets := #[LeanLib.staticFacet, LeanLib.sharedFacet]'
  '';

  lakeHash = null;
}
