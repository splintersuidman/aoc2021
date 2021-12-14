{
  description = "Solutions for Advent of Code 2021 in Agda";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        agdaPackages = pkgs.agdaPackages;

        version = "0";
        everythingFile = "./index.agda";
      in {
        packages.aoc2021 = agdaPackages.mkDerivation {
          inherit version;
          pname = "aoc2021";
          src = ./.;
          buildInputs = [ agdaPackages.standard-library agdaPackages.agdarsec ];
          inherit everythingFile;
          meta = { };
        };

        packages.aoc2021-doc = agdaPackages.mkDerivation {
          inherit version;
          pname = "aoc2021-doc";
          src = ./.;
          buildInputs = [ agdaPackages.standard-library agdaPackages.agdarsec ];
          meta = { };

          buildPhase = ''
            runHook preBuild
            agda -i ${
              dirOf everythingFile
            } --html ${everythingFile} --html-dir html
            runHook postBuild
          '';

          installPhase = ''
            runHook preInstall
            mkdir -p $out
            mkdir -p $out/doc
            cp html/* $out/doc
            runHook postInstall
          '';
        };

        defaultPackage = self.packages.${system}.aoc2021;
      });
}
