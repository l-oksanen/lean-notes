{
  lib,
  buildLakePackage,
  fetchFromGitHub,
}:
let
  src = fetchFromGitHub {
    owner = "leanprover";
    repo = "subverso";
    rev = "52b9dfbd2658408e37ae6e8b72601ddeaaa25a0c";
    hash = "sha256-mIfgh7xIo8dpUhR9IMwkGJZqVFKoRNJBC960hEkeevQ=";
  };
in
buildLakePackage {
  pname = "lean4-subverso";
  version = "main";
  inherit src;

  leanPackageName = "subverso";

  lakeHash = null;
}
