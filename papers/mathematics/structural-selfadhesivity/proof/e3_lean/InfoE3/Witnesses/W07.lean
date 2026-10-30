import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table07 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2308, 2310, 3458, 1155, 2308, 2310, 3458, 2307, 3460, 3458, 4606,
  1155, 2308, 2310, 3458, 2306, 3459, 3458, 4606, 2310, 3458, 3458, 4606, 3458, 4606, 4606, 5752,
  1155, 2308, 2310, 3458, 2307, 3460, 3458, 4606, 2310, 3461, 3458, 4606, 3459, 4610, 4606, 5754,
  2308, 3459, 3458, 4606, 3458, 4609, 4606, 5754, 3461, 4609, 4606, 5754, 4609, 5756, 5754, 6900,
  1155, 2308, 2310, 3458, 2306, 3459, 3458, 4606, 2310, 3461, 3458, 4606, 3458, 4609, 4606, 5754,
  2306, 3459, 3458, 4606, 3457, 4608, 4606, 5754, 3461, 4609, 4606, 5754, 4609, 5755, 5754, 6900,
  2310, 3458, 3458, 4606, 3458, 4606, 4606, 5752, 3461, 4609, 4606, 5754, 4609, 5756, 5754, 6900,
  3459, 4607, 4606, 5754, 4607, 5755, 5754, 6900, 4610, 5757, 5754, 6901, 5758, 6902, 6902, 8046
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup07 (s : Nat) : ℤ := (if s < 64 then (if s < 32 then (if s < 16 then (if s < 8 then (if s < 4 then (if s < 2 then (if s < 1 then 0 else 1155) else (if s < 3 then 1155 else 2310)) else (if s < 6 then (if s < 5 then 1155 else 2308) else (if s < 7 then 2310 else 3458))) else (if s < 12 then (if s < 10 then (if s < 9 then 1155 else 2308) else (if s < 11 then 2310 else 3458)) else (if s < 14 then (if s < 13 then 2307 else 3460) else (if s < 15 then 3458 else 4606)))) else (if s < 24 then (if s < 20 then (if s < 18 then (if s < 17 then 1155 else 2308) else (if s < 19 then 2310 else 3458)) else (if s < 22 then (if s < 21 then 2306 else 3459) else (if s < 23 then 3458 else 4606))) else (if s < 28 then (if s < 26 then (if s < 25 then 2310 else 3458) else (if s < 27 then 3458 else 4606)) else (if s < 30 then (if s < 29 then 3458 else 4606) else (if s < 31 then 4606 else 5752))))) else (if s < 48 then (if s < 40 then (if s < 36 then (if s < 34 then (if s < 33 then 1155 else 2308) else (if s < 35 then 2310 else 3458)) else (if s < 38 then (if s < 37 then 2307 else 3460) else (if s < 39 then 3458 else 4606))) else (if s < 44 then (if s < 42 then (if s < 41 then 2310 else 3461) else (if s < 43 then 3458 else 4606)) else (if s < 46 then (if s < 45 then 3459 else 4610) else (if s < 47 then 4606 else 5754)))) else (if s < 56 then (if s < 52 then (if s < 50 then (if s < 49 then 2308 else 3459) else (if s < 51 then 3458 else 4606)) else (if s < 54 then (if s < 53 then 3458 else 4609) else (if s < 55 then 4606 else 5754))) else (if s < 60 then (if s < 58 then (if s < 57 then 3461 else 4609) else (if s < 59 then 4606 else 5754)) else (if s < 62 then (if s < 61 then 4609 else 5756) else (if s < 63 then 5754 else 6900)))))) else (if s < 96 then (if s < 80 then (if s < 72 then (if s < 68 then (if s < 66 then (if s < 65 then 1155 else 2308) else (if s < 67 then 2310 else 3458)) else (if s < 70 then (if s < 69 then 2306 else 3459) else (if s < 71 then 3458 else 4606))) else (if s < 76 then (if s < 74 then (if s < 73 then 2310 else 3461) else (if s < 75 then 3458 else 4606)) else (if s < 78 then (if s < 77 then 3458 else 4609) else (if s < 79 then 4606 else 5754)))) else (if s < 88 then (if s < 84 then (if s < 82 then (if s < 81 then 2306 else 3459) else (if s < 83 then 3458 else 4606)) else (if s < 86 then (if s < 85 then 3457 else 4608) else (if s < 87 then 4606 else 5754))) else (if s < 92 then (if s < 90 then (if s < 89 then 3461 else 4609) else (if s < 91 then 4606 else 5754)) else (if s < 94 then (if s < 93 then 4609 else 5755) else (if s < 95 then 5754 else 6900))))) else (if s < 112 then (if s < 104 then (if s < 100 then (if s < 98 then (if s < 97 then 2310 else 3458) else (if s < 99 then 3458 else 4606)) else (if s < 102 then (if s < 101 then 3458 else 4606) else (if s < 103 then 4606 else 5752))) else (if s < 108 then (if s < 106 then (if s < 105 then 3461 else 4609) else (if s < 107 then 4606 else 5754)) else (if s < 110 then (if s < 109 then 4609 else 5756) else (if s < 111 then 5754 else 6900)))) else (if s < 120 then (if s < 116 then (if s < 114 then (if s < 113 then 3459 else 4607) else (if s < 115 then 4606 else 5754)) else (if s < 118 then (if s < 117 then 4607 else 5755) else (if s < 119 then 5754 else 6900))) else (if s < 124 then (if s < 122 then (if s < 121 then 4610 else 5757) else (if s < 123 then 5754 else 6901)) else (if s < 126 then (if s < 125 then 5758 else 6902) else (if s < 127 then 6902 else 8046)))))))
def witness07 (S : Mask (groundSize 7)) : ℤ := lookup07 S.val

theorem witness07_table : ∀ S : Mask (groundSize 7),
    witness07 S = table07[S.val]! := by decide +kernel

theorem witness07_local_mono : MaskLocalMono witness07 := by
  unfold MaskLocalMono
  decide +kernel

theorem witness07_local_squares : MaskLocalSquares witness07 := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness07_pm : PMInt (groundSize 7) witness07 :=
  PMInt.of_local encoding_ok_7 (by decide +kernel)
    witness07_local_mono witness07_local_squares

theorem witness07_first : MatchesInt (fun S => witness07 (origMask 7 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness07_second : MatchesInt (fun S => witness07 (copyMask 7 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness07_adhesive : AdhesiveInt 7 witness07 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_07 : ∃ g : Mask (groundSize 7) → ℝ,
    PM (groundSize 7) g ∧ Matches (firstRestrict 7 g) ∧
    Matches (secondRestrict 7 g) ∧ Adhesive 7 g :=
  positive_of_int 7 witness07 witness07_pm witness07_first witness07_second witness07_adhesive

#print axioms witness07_pm
end InfoE3
