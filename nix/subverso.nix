{
  lib,
  buildLakePackage,
  fetchFromGitHub,
}:
let
  src = fetchFromGitHub {
    owner = "leanprover";
    repo = "subverso";
    rev = "ce893b9042128037e2d3c0158b9567fab9fae268";
    hash = "sha256-uUmLu/zIataPnSxh3v8Wej5PGnrNaSkLszltJoT7FrQ=";
  };
in
buildLakePackage {
  pname = "lean4-subverso";
  version = "main";
  inherit src;

  leanPackageName = "subverso";

  lakeHash = null;
}
