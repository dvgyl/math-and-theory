import InfoE3.PositiveBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InfoE3

def table31 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2309, 2310, 3460, 1155, 2309, 2310, 3460, 2308, 3462, 3460, 4610,
  1155, 2309, 2310, 3460, 2307, 3461, 3460, 4610, 2310, 3460, 3460, 4610, 3460, 4610, 4610, 5758
]

def witness31 (S : Mask (groundSize 31)) : ℤ := table31[S.val]!

theorem witness31_pm : PMInt (groundSize 31) witness31 := by
  constructor
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem witness31_first : MatchesInt (fun S => witness31 (origMask 31 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness31_second : MatchesInt (fun S => witness31 (copyMask 31 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness31_adhesive : AdhesiveInt 31 witness31 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_31 : ∃ g : Mask (groundSize 31) → ℝ,
    PM (groundSize 31) g ∧ Matches (firstRestrict 31 g) ∧
    Matches (secondRestrict 31 g) ∧ Adhesive 31 g :=
  positive_of_int 31 witness31 witness31_pm witness31_first witness31_second witness31_adhesive

end InfoE3
