# Nix

Nix is a package manager and a build system.
It's an alternative to installing dependencies and building the document.
The goal is to be hermetic and reproducible.

## Developing locally

[default.nix](./default.nix) provides required dependencies as well as convenience scripts `*-document`:

```
nix-shell nix -A shell
preprocess-document
generate-document
postprocess-document
python -m http.server -d _out/_out/html-multi
```

> Notice that entering the shell for the first time requires downloading (or building) mathlib and other artifacts.

Alternatively one can use [direnv](https://github.com/nix-community/nix-direnv) to load the shell upon entering the repository.

## Building the document

`default.nix` provides a `notes` attribute which is the full generated HTML page.

```
nix-build nix -A notes
python -m http.server -d result/
```

## Generating HW

The `hw` attribute generates the homework files from `Examples`.

```
nix-build nix -A hw
```

## Bundling HW with the document

The `notes-with-hw` attribute joins `notes` and `hw` together such that the generated homework files are found under the `/hw` subdirectory.

```
nix-build nix -A notes-with-hw
```