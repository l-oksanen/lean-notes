{
  lib,
  buildLakePackage,
  fetchFromGitHub,
  plausible,
  md4lean,
  subverso,
}:
let
  version = "4.29.0";
  src = fetchFromGitHub {
    owner = "leanprover";
    repo = "verso";
    tag = "v${version}";
    hash = "sha256-5eo/xbPNbS9/Bv7tfnXz52mUo/CXG6mnLWg8h6mg6FE=";
  };
in
buildLakePackage {
  pname = "lean4-verso";
  inherit src version;

  leanPackageName = "verso";

  patches = [ ./verso-remove-default-targets-add-static-facets-and-fix-globs.patch ];

  leanDeps = [
    plausible
    md4lean
    subverso
  ];
}
