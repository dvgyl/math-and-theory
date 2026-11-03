import Lake
open Lake DSL

package ellipsoidWitnessCertificate where
  version := v!"0.2.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c44e0c8ee63ca166450922a373c7409c5d26b00b"

lean_lib EllipsoidCounterexample

lean_lib SameChirality

lean_lib ParametricFamily
lean_lib ClassCComparison
lean_lib NormalFormCertificates
lean_lib MirrorComparison
lean_lib GeometryCertificates
lean_lib ProductVector
lean_lib OptimalityReduction

@[default_target]
lean_lib Main

-- Whole-project axiom audit added for the public release (see VERIFICATION.md).
lean_lib ProjectAxiomAudit
