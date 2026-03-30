{ pkgs, ... }:
let
  lib = pkgs.lib;

  # This is a utility not exposed by nixpkgs.leanPackages
  # Generate the overrides from a list of lean packages
  mkOverridesFile =
    allLeanDeps:
    pkgs.writeText "lake-overrides.json" (
      builtins.toJSON {
        schemaVersion = "1.2.0";
        packages = map (dep: {
          type = "path";
          name = dep.passthru.lakePackageName or dep.pname;
          inherited = false;
          dir = "${dep}";
        }) allLeanDeps;
      }
    );
in
{
  inherit mkOverridesFile;
}
