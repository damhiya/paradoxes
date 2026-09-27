{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs =
    {
      self,
      nixpkgs,
    }:
    let
      forAllSystems =
        function:
        nixpkgs.lib.genAttrs nixpkgs.lib.systems.flakeExposed (
          system: function nixpkgs.legacyPackages.${system}
        );
    in
    {
      devShells = forAllSystems (
        pkgs:
        let
          agda = pkgs.agda.withPackages (pkgs: [ pkgs.standard-library ]);
        in
        {
          default = pkgs.mkShell {
            buildInputs = [
              agda
            ];
          };
        }
      );
    };
}
