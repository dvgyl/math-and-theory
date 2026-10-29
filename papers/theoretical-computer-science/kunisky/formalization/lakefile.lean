import Lake
open Lake DSL

package kunisky_counterexample where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c44e0c8ee63ca166450922a373c7409c5d26b00b"

@[default_target]
lean_lib KuniskyCounterexample where
  roots := #[
    `Absorption,
    `CertificateAnalysis,
    `Completion,
    `Concentration,
    `Conjecture,
    `Counterexample,
    `Family,
    `FinalAudit,
    `FiniteCertificate,
    `FullFormulaProperties,
    `GeneralResult,
    `MinimalMass,
    `NoTautologies,
    `Policy,
    `Resolution,
    `SourceMass
  ]
