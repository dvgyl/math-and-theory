import Lake
open Lake DSL
package quarticRankings where
  moreLeanArgs := #["-j1", "-DwarningAsError=true"]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c44e0c8ee63ca166450922a373c7409c5d26b00b"
@[default_target]
lean_lib PermEntropy where
  globs := #[.one `PermEntropy, .submodules `PermEntropy]
