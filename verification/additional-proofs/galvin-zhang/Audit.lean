import DominationULC

/-!
Run `lake env lean Audit.lean` after `lake build`.
Expected dependencies for every theorem below:
  [propext, Classical.choice, Quot.sound]
In particular there should be no `sorryAx` or project-defined axiom.
-/

#check DominationULC.galvin_zhang_conjecture
#check DominationULC.galvin_zhang_normalized
#check DominationULC.path_domination_weighted
#check DominationULC.cycle_domination_weighted

#print axioms DominationULC.galvin_zhang_conjecture
#print axioms DominationULC.galvin_zhang_normalized
#print axioms DominationULC.path_domination_weighted
#print axioms DominationULC.cycle_domination_weighted
