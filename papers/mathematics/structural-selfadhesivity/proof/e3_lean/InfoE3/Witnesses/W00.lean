import InfoE3.DirectSum
import InfoE3.Witnesses.W31

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InfoE3

/-- At the empty overlap, the gluing is the direct sum of two copies. -/
def witness00 (S : Mask (groundSize 0)) : ℤ :=
  witness31 (sliceMask 5 0 S) + witness31 (sliceMask 5 5 S)

theorem witness00_pm : PMInt (groundSize 0) witness00 :=
  (witness31_pm.slice 0).add (witness31_pm.slice 5)

theorem witness00_first : MatchesInt (fun S => witness00 (origMask 0 S)) := by
  unfold MatchesInt
  decide +kernel

theorem witness00_second : MatchesInt (fun S => witness00 (copyMask 0 S)) := by
  unfold MatchesInt
  decide +kernel

theorem witness00_adhesive : AdhesiveInt 0 witness00 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_00 : ∃ g : Mask (groundSize 0) → ℝ,
    PM (groundSize 0) g ∧ Matches (firstRestrict 0 g) ∧
    Matches (secondRestrict 0 g) ∧ Adhesive 0 g :=
  positive_of_int 0 witness00 witness00_pm witness00_first witness00_second witness00_adhesive

#print axioms structural_at_00

end InfoE3
