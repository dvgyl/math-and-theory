import Lake
open Lake DSL

package ppt_cone_counterexample where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c44e0c8ee63ca166450922a373c7409c5d26b00b"

@[default_target]
lean_lib PPTCone where
  roots := #[`CoreDefs, `TilesBase, `TilesTensor, `CESTensor, `ConeExclusion, `Main,
    `GeneralDefs, `CESTensorGeneral, `TensorProjection, `GenericCone, `Hierarchy, `AllK,
    `RankBridge, `BlockRank, `UPBRank, `TensorProductProjection, `TilesUPB,
    `SchmidtUpper, `StrongTensor, `PowerFamily, `Normalization, `NormalizedPower]
