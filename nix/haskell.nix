############################################################################
# Builds Haskell packages with Haskell.nix
############################################################################
{ lib
, stdenv
, pkgs
, haskell-nix
, buildPackages
, config ? {}
# GHC attribute name
, compiler ? config.haskellNix.compiler or "ghc8104"
# Enable profiling
, profiling ? config.haskellNix.profiling or false
}:
let

  src = haskell-nix.haskellLib.cleanGit {
      name = "cardano-ledger-specs";
      src = ../.;
  };

  # The cardano-mainnet-mirror used during testing
  cardano-mainnet-mirror = import ./cardano-mainnet-mirror.nix {inherit pkgs;};

  # This creates the Haskell package set.
  # https://input-output-hk.github.io/haskell.nix/user-guide/projects/
  pkgSet = haskell-nix.cabalProject {
    inherit src;
    compiler-nix-name = compiler;
    modules = [
      {
        packages.plutus-core.components.library.ghcOptions = [ "-fexternal-interpreter" ];
        packages.byron-spec-chain.configureFlags = [ "--ghc-option=-Werror" ];
        packages.byron-spec-ledger.configureFlags = [ "--ghc-option=-Werror" ];
        packages.delegation.configureFlags = [ "--ghc-option=-Werror" ];
        packages.shelley-spec-non-integral.configureFlags = [ "--ghc-option=-Werror" ];
        packages.shelley-spec-ledger.configureFlags = [ "--ghc-option=-Werror" ];
        packages.cardano-ledger-shelley-ma.configureFlags = [ "--ghc-option=-Werror" ];
        packages.cardano-ledger-shelley-ma-test.configureFlags = [ "--ghc-option=-Werror" ];
        packages.cardano-ledger-shelley-ma-test.components.tests.cardano-ledger-shelley-ma-test.build-tools = [pkgs.cddl pkgs.cbor-diag];
        packages.small-steps.configureFlags = [ "--ghc-option=-Werror" ];
        packages.shelley-spec-ledger-test.components.tests.shelley-spec-ledger-test.build-tools = [pkgs.cddl pkgs.cbor-diag];
        packages.cardano-ledger-alonzo-test.components.tests.cardano-ledger-alonzo-test.build-tools = [pkgs.cddl pkgs.cbor-diag];
        enableLibraryProfiling = profiling;
        # Disable doctests for now (waiting for https://github.com/input-output-hk/haskell.nix/pull/427):
        packages.small-steps.components.tests.doctests.buildable = lib.mkForce false;
        packages.small-steps-test.components.tests.doctests.buildable = lib.mkForce false;
        packages.byron-spec-ledger.components.tests.doctests.buildable = lib.mkForce false;

        packages.cardano-ledger-byron = {
          configureFlags = [ "--ghc-option=-Werror" ];
          components = {
            tests.cardano-ledger-byron-test = {
              preCheck = ''
                export CARDANO_MAINNET_MIRROR="${cardano-mainnet-mirror}/epochs"
                cp ${../byron/ledger/impl/mainnet-genesis.json} ./mainnet-genesis.json
              '';
              build-tools = [ pkgs.makeWrapper ];
              testFlags = [ "--scenario=ContinuousIntegration" ];
            };
          };
        };

      }
    ];
  };
in
  pkgSet
