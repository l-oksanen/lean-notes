{
  sources ? import ./npins,
  system ? builtins.currentSystem,
  pkgs ? import sources.nixpkgs {
    inherit system;
    config = { };
    overlays = [ (import sources.lean-blog { inherit pkgs; }).overlay ];
  },
}:
let
  lib = pkgs.lib;
  inherit (import ./util.nix { inherit pkgs; }) mkOverridesFile;

  pythonWithDeps = pkgs.python3.withPackages (
    ps: with ps; [
      beautifulsoup4
      html5lib
    ]
  );
in
rec {
  shell = pkgs.mkShell {
    inputsFrom = [ notes ];
    packages = with pkgs; [
      pkgs.leanPackages.lean4
      npins
      jq
      preprocess-document
      postprocess-document
      generate-document
    ];
    LAKE_PACKAGES = mkOverridesFile notes.passthru.allLeanDeps;
  };

  # We don't use init.fish because `lake init Document math` needs internet access plus it's unnecessary.
  # Instead we provide our own lakefile.toml and lake-manifest.json.
  # As the lake-manifest.json is empty, it only works if lake gets package-overrides through `--packages=...` as done in `generate-document` and buildLakePackage internally.
  preprocess-document = pkgs.writeShellScriptBin "preprocess-document" ''
    rm -rf generated
    mkdir -p generated/Document
    for file in Document/*.lean; do
      echo "Preprocessing $file"

      name=$(basename "''${file%.*}")
      jq -Rsr -f scripts/preprocess.jq <$file >generated/Document/$(basename "$file")
      echo "import Document.$name" >>generated/Document.lean
    done

    echo 'import Infra.Preamble' >>generated/Document.lean
    cat Document.md >>generated/Document.lean

    cp lean-toolchain generated/
    cp -rfv verso/* generated/
    cp ${./lakefile.toml} generated/lakefile.toml
    # Copy empty manifest, lake must be used with --packages
    cp ${./lake-manifest.json} generated/lake-manifest.json
  '';

  postprocess-document = pkgs.writeShellScriptBin "postprocess-document" ''
    for file in $(find . -type f -name "index.html"); do
      echo "Postprocessing $file"

      ${lib.getExe pythonWithDeps} scripts/postprocess.py <$file >"$file"_pp
      mv "$file"_pp $file
    done
  '';

  # This is just for manual use
  generate-document = pkgs.writeShellScriptBin "generate-document" ''
    pushd generated
    lake build --packages=${mkOverridesFile notes.passthru.allLeanDeps} Document
    lake --no-ansi --packages=${mkOverridesFile notes.passthru.allLeanDeps} env lean --run Infra/Main.lean --output _out --verbose
    cp -rfv ../assets/* _out/html-multi/
    cp -rfv ../custom/* _out/html-multi/
    popd
  '';

  notes =
    let
      # Recursively get lean deps
      overridesFile = mkOverridesFile notes.passthru.allLeanDeps;
    in
    pkgs.leanPackages.buildLakePackage {
      pname = "lean-notes";
      version = "0.1.0";
      src = pkgs.nix-gitignore.gitignoreSource [ ] ../.;

      leanPackageName = "Document";

      buildTargets = [ "Document" ];

      preBuild = ''
        ${lib.getExe preprocess-document}

        # Move everything from generated back to root for building with buildLakePackage
        cp -r generated/. .
      '';

      postBuild = ''
        # Generate the HTML
        lake --no-ansi --packages=${overridesFile} env lean --run Infra/Main.lean --output _out --verbose

        cp -rfv ./assets/* _out/html-multi/
        cp -rfv ./custom/* _out/html-multi/

        ${lib.getExe postprocess-document}
      '';

      installPhase = ''
        runHook preInstall
        mkdir -p $out
        cp -r _out/html-multi/. $out/
        runHook postInstall
      '';

      leanDeps = [
        pkgs.leanPackages.verso
        pkgs.leanPackages.mathlib
      ];
    };

  # TODO homework/exercises
}
