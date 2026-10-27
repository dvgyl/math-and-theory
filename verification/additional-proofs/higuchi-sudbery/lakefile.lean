import Lake
open Lake DSL

package hs_research where
  moreLeanArgs := #["-j1", "-DwarningAsError=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib HS
