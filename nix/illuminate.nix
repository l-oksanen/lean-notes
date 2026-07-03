{
  lib,
  buildLakePackage,
  fetchFromGitHub,
}:
let
  src = fetchFromGitHub {
    owner = "leanprover";
    repo = "illuminate";
    rev = "99ada816d9929a51132d5b5dc4f43c51f16d67d8";
    hash = "sha256-pc6vgkmC8E70/vj7b5v2cd2eLig0Gtbj0kTL6fgu+U4=";
  };
in
buildLakePackage {
  pname = "lean4-illuminate";
  version = "main";
  inherit src;

  leanPackageName = "illuminate";

  postPatch = ''
    substituteInPlace lakefile.lean \
      --replace-fail 'lean_lib «Illuminate» where' 'lean_lib «Illuminate» where
      defaultFacets := #[LeanLib.staticFacet]'
  '';

  lakeHash = null;
}
