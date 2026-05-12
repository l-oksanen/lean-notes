let
  overlay = final: prev: {
    leanPackages = prev.leanPackages.overrideScope (
      lean-final: lean-prev: {
        md4lean = lean-final.callPackage ./md4lean.nix { };
        subverso = lean-final.callPackage ./subverso.nix { };
        verso = lean-final.callPackage ./verso.nix { };
      }
    );
  };
in
{
  sources ? import ./npins,
  system ? builtins.currentSystem,
  pkgs ? import sources.nixpkgs {
    inherit system;
    config = { };
    overlays = [ overlay ];
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
    rm -rf _out
    mkdir -p _out/Document
    for file in Document/*.lean; do
      echo "Preprocessing $file"

      name=$(basename "''${file%.*}")
      jq -Rsr -f scripts/preprocess.jq <$file >_out/Document/$(basename "$file")
      echo "import Document.$name" >>_out/Document.lean
    done

    echo 'import Infra.Preamble' >>_out/Document.lean
    cat Document.md >>_out/Document.lean

    cp lean-toolchain _out/
    cp -rfv verso/* _out/
    cp ${./lakefile.toml} _out/lakefile.toml
    # Copy empty manifest, lake must be used with --packages
    cp ${./lake-manifest.json} _out/lake-manifest.json
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
    pushd _out
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

        # Move everything from _out back to root for building with buildLakePackage
        cp -r _out/. .
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
        mkdir $out
        cp -r _out/html-multi/. $out/
        runHook postInstall
      '';

      leanDeps = [
        pkgs.leanPackages.verso
        pkgs.leanPackages.mathlib
      ];
    };

  hw =
    let
      header = builtins.toFile "header.lean" ''
        /-
        Exercises
        ---------

        Fill in the parts labeled with __TODO__.

        -/
      '';
    in
    pkgs.stdenv.mkDerivation {
      pname = "hw";
      version = "0.1.0";

      src = ../Examples;

      buildPhase = ''
        mkdir $out
        for file in *.lean; do
          echo "Processing $file"

          cat ${header} > $out/$file
          awk -f ${../scripts/hw-process.awk} <$file \
          | awk -f ${../scripts/hw-process-blank.awk} \
          >>$out/$file
        done
      '';
    };

  notes-with-hw = pkgs.runCommand "notes-with-hw" { nativeBuildInputs = [ pkgs.lndir ]; } ''
    mkdir -p $out/hw
    lndir ${notes}/ $out/
    cp -r ${hw}/. $out/hw/
  '';
}
