import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table13 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2309, 2310, 3460, 1155, 2309, 2310, 3460, 2308, 3462, 3460, 4610,
  1155, 2309, 2310, 3460, 2307, 3461, 3460, 4610, 2310, 3460, 3460, 4610, 3460, 4610, 4610, 5758,
  1155, 2310, 2310, 3464, 2310, 3460, 3465, 4611, 2310, 3460, 3465, 4611, 3460, 4610, 4612, 5758,
  2310, 3463, 3465, 4614, 3462, 4610, 4615, 5759, 3465, 4611, 4615, 5761, 4612, 5758, 5762, 6906,
  1155, 2309, 2310, 3464, 2307, 3461, 3462, 4611, 2310, 3460, 3465, 4611, 3460, 4610, 4612, 5758,
  2310, 3462, 3465, 4613, 3459, 4611, 4612, 5759, 3465, 4611, 4615, 5760, 4612, 5758, 5762, 6906,
  2310, 3460, 3465, 4614, 3460, 4610, 4615, 5759, 3460, 4610, 4615, 5761, 4610, 5758, 5762, 6906,
  3465, 4613, 4618, 5763, 4612, 5759, 5765, 6907, 4615, 5761, 5765, 6910, 5762, 6906, 6912, 8054
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup13 (s : Nat) : ℤ := (if s < 64 then (if s < 32 then (if s < 16 then (if s < 8 then (if s < 4 then (if s < 2 then (if s < 1 then 0 else 1155) else (if s < 3 then 1155 else 2310)) else (if s < 6 then (if s < 5 then 1155 else 2309) else (if s < 7 then 2310 else 3460))) else (if s < 12 then (if s < 10 then (if s < 9 then 1155 else 2309) else (if s < 11 then 2310 else 3460)) else (if s < 14 then (if s < 13 then 2308 else 3462) else (if s < 15 then 3460 else 4610)))) else (if s < 24 then (if s < 20 then (if s < 18 then (if s < 17 then 1155 else 2309) else (if s < 19 then 2310 else 3460)) else (if s < 22 then (if s < 21 then 2307 else 3461) else (if s < 23 then 3460 else 4610))) else (if s < 28 then (if s < 26 then (if s < 25 then 2310 else 3460) else (if s < 27 then 3460 else 4610)) else (if s < 30 then (if s < 29 then 3460 else 4610) else (if s < 31 then 4610 else 5758))))) else (if s < 48 then (if s < 40 then (if s < 36 then (if s < 34 then (if s < 33 then 1155 else 2310) else (if s < 35 then 2310 else 3464)) else (if s < 38 then (if s < 37 then 2310 else 3460) else (if s < 39 then 3465 else 4611))) else (if s < 44 then (if s < 42 then (if s < 41 then 2310 else 3460) else (if s < 43 then 3465 else 4611)) else (if s < 46 then (if s < 45 then 3460 else 4610) else (if s < 47 then 4612 else 5758)))) else (if s < 56 then (if s < 52 then (if s < 50 then (if s < 49 then 2310 else 3463) else (if s < 51 then 3465 else 4614)) else (if s < 54 then (if s < 53 then 3462 else 4610) else (if s < 55 then 4615 else 5759))) else (if s < 60 then (if s < 58 then (if s < 57 then 3465 else 4611) else (if s < 59 then 4615 else 5761)) else (if s < 62 then (if s < 61 then 4612 else 5758) else (if s < 63 then 5762 else 6906)))))) else (if s < 96 then (if s < 80 then (if s < 72 then (if s < 68 then (if s < 66 then (if s < 65 then 1155 else 2309) else (if s < 67 then 2310 else 3464)) else (if s < 70 then (if s < 69 then 2307 else 3461) else (if s < 71 then 3462 else 4611))) else (if s < 76 then (if s < 74 then (if s < 73 then 2310 else 3460) else (if s < 75 then 3465 else 4611)) else (if s < 78 then (if s < 77 then 3460 else 4610) else (if s < 79 then 4612 else 5758)))) else (if s < 88 then (if s < 84 then (if s < 82 then (if s < 81 then 2310 else 3462) else (if s < 83 then 3465 else 4613)) else (if s < 86 then (if s < 85 then 3459 else 4611) else (if s < 87 then 4612 else 5759))) else (if s < 92 then (if s < 90 then (if s < 89 then 3465 else 4611) else (if s < 91 then 4615 else 5760)) else (if s < 94 then (if s < 93 then 4612 else 5758) else (if s < 95 then 5762 else 6906))))) else (if s < 112 then (if s < 104 then (if s < 100 then (if s < 98 then (if s < 97 then 2310 else 3460) else (if s < 99 then 3465 else 4614)) else (if s < 102 then (if s < 101 then 3460 else 4610) else (if s < 103 then 4615 else 5759))) else (if s < 108 then (if s < 106 then (if s < 105 then 3460 else 4610) else (if s < 107 then 4615 else 5761)) else (if s < 110 then (if s < 109 then 4610 else 5758) else (if s < 111 then 5762 else 6906)))) else (if s < 120 then (if s < 116 then (if s < 114 then (if s < 113 then 3465 else 4613) else (if s < 115 then 4618 else 5763)) else (if s < 118 then (if s < 117 then 4612 else 5759) else (if s < 119 then 5765 else 6907))) else (if s < 124 then (if s < 122 then (if s < 121 then 4615 else 5761) else (if s < 123 then 5765 else 6910)) else (if s < 126 then (if s < 125 then 5762 else 6906) else (if s < 127 then 6912 else 8054)))))))
def witness13 (S : Mask (groundSize 13)) : ℤ := lookup13 S.val

theorem witness13_table : ∀ S : Mask (groundSize 13),
    witness13 S = table13[S.val]! := by decide +kernel

theorem witness13_local_mono : MaskLocalMono witness13 := by
  unfold MaskLocalMono
  decide +kernel

theorem witness13_local_squares : MaskLocalSquares witness13 := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness13_pm : PMInt (groundSize 13) witness13 :=
  PMInt.of_local encoding_ok_7 (by decide +kernel)
    witness13_local_mono witness13_local_squares

theorem witness13_first : MatchesInt (fun S => witness13 (origMask 13 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness13_second : MatchesInt (fun S => witness13 (copyMask 13 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness13_adhesive : AdhesiveInt 13 witness13 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_13 : ∃ g : Mask (groundSize 13) → ℝ,
    PM (groundSize 13) g ∧ Matches (firstRestrict 13 g) ∧
    Matches (secondRestrict 13 g) ∧ Adhesive 13 g :=
  positive_of_int 13 witness13 witness13_pm witness13_first witness13_second witness13_adhesive

#print axioms witness13_pm
end InfoE3
