import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table29 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2309, 2310, 3460, 1155, 2309, 2310, 3460, 2308, 3462, 3460, 4610,
  1155, 2309, 2310, 3460, 2307, 3461, 3460, 4610, 2310, 3460, 3460, 4610, 3460, 4610, 4610, 5758,
  1155, 2310, 2303, 3458, 2310, 3460, 3458, 4608, 2310, 3460, 3458, 4608, 3460, 4610, 4608, 5758,
  2310, 3460, 3458, 4608, 3460, 4610, 4608, 5758, 3460, 4610, 4608, 5758, 4610, 5758, 5758, 6906
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup29 (s : Nat) : ℤ := (if s < 32 then (if s < 16 then (if s < 8 then (if s < 4 then (if s < 2 then (if s < 1 then 0 else 1155) else (if s < 3 then 1155 else 2310)) else (if s < 6 then (if s < 5 then 1155 else 2309) else (if s < 7 then 2310 else 3460))) else (if s < 12 then (if s < 10 then (if s < 9 then 1155 else 2309) else (if s < 11 then 2310 else 3460)) else (if s < 14 then (if s < 13 then 2308 else 3462) else (if s < 15 then 3460 else 4610)))) else (if s < 24 then (if s < 20 then (if s < 18 then (if s < 17 then 1155 else 2309) else (if s < 19 then 2310 else 3460)) else (if s < 22 then (if s < 21 then 2307 else 3461) else (if s < 23 then 3460 else 4610))) else (if s < 28 then (if s < 26 then (if s < 25 then 2310 else 3460) else (if s < 27 then 3460 else 4610)) else (if s < 30 then (if s < 29 then 3460 else 4610) else (if s < 31 then 4610 else 5758))))) else (if s < 48 then (if s < 40 then (if s < 36 then (if s < 34 then (if s < 33 then 1155 else 2310) else (if s < 35 then 2303 else 3458)) else (if s < 38 then (if s < 37 then 2310 else 3460) else (if s < 39 then 3458 else 4608))) else (if s < 44 then (if s < 42 then (if s < 41 then 2310 else 3460) else (if s < 43 then 3458 else 4608)) else (if s < 46 then (if s < 45 then 3460 else 4610) else (if s < 47 then 4608 else 5758)))) else (if s < 56 then (if s < 52 then (if s < 50 then (if s < 49 then 2310 else 3460) else (if s < 51 then 3458 else 4608)) else (if s < 54 then (if s < 53 then 3460 else 4610) else (if s < 55 then 4608 else 5758))) else (if s < 60 then (if s < 58 then (if s < 57 then 3460 else 4610) else (if s < 59 then 4608 else 5758)) else (if s < 62 then (if s < 61 then 4610 else 5758) else (if s < 63 then 5758 else 6906))))))
def witness29 (S : Mask (groundSize 29)) : ℤ := lookup29 S.val

theorem witness29_table : ∀ S : Mask (groundSize 29),
    witness29 S = table29[S.val]! := by decide +kernel

theorem witness29_local_mono : MaskLocalMono witness29 := by
  unfold MaskLocalMono
  decide +kernel

theorem witness29_local_squares : MaskLocalSquares witness29 := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness29_pm : PMInt (groundSize 29) witness29 :=
  PMInt.of_local encoding_ok_6 (by decide +kernel)
    witness29_local_mono witness29_local_squares

theorem witness29_first : MatchesInt (fun S => witness29 (origMask 29 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness29_second : MatchesInt (fun S => witness29 (copyMask 29 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness29_adhesive : AdhesiveInt 29 witness29 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_29 : ∃ g : Mask (groundSize 29) → ℝ,
    PM (groundSize 29) g ∧ Matches (firstRestrict 29 g) ∧
    Matches (secondRestrict 29 g) ∧ Adhesive 29 g :=
  positive_of_int 29 witness29 witness29_pm witness29_first witness29_second witness29_adhesive

#print axioms witness29_pm
end InfoE3
