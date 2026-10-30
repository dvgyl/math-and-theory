import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table28 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2305, 2310, 3443, 1155, 2305, 2310, 3443, 2301, 3451, 3443, 4576,
  1155, 2305, 2310, 3443, 2297, 3447, 3443, 4576, 2310, 3443, 3443, 4576, 3443, 4576, 4576, 5701,
  1155, 2310, 2310, 3451, 2305, 3446, 3455, 4584, 2305, 3448, 3451, 4584, 3451, 4584, 4584, 5709,
  2305, 3446, 3451, 4584, 3447, 4582, 4584, 5711, 3443, 4576, 4576, 5709, 4576, 5709, 5709, 6834,
  1155, 2301, 2310, 3453, 2310, 3451, 3457, 4586, 2310, 3451, 3451, 4584, 3443, 4584, 4584, 5709,
  2310, 3451, 3451, 4584, 3443, 4584, 4584, 5713, 3443, 4576, 4576, 5709, 4576, 5709, 5709, 6834,
  2310, 3451, 3451, 4586, 3443, 4578, 4584, 5713, 3443, 4584, 4584, 5709, 4576, 5709, 5709, 6834,
  3443, 4584, 4584, 5711, 4576, 5711, 5711, 6838, 4576, 5709, 5709, 6834, 5701, 6834, 6834, 7959
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup28 (s : Nat) : ℤ := (if s < 64 then (if s < 32 then (if s < 16 then (if s < 8 then (if s < 4 then (if s < 2 then (if s < 1 then 0 else 1155) else (if s < 3 then 1155 else 2310)) else (if s < 6 then (if s < 5 then 1155 else 2305) else (if s < 7 then 2310 else 3443))) else (if s < 12 then (if s < 10 then (if s < 9 then 1155 else 2305) else (if s < 11 then 2310 else 3443)) else (if s < 14 then (if s < 13 then 2301 else 3451) else (if s < 15 then 3443 else 4576)))) else (if s < 24 then (if s < 20 then (if s < 18 then (if s < 17 then 1155 else 2305) else (if s < 19 then 2310 else 3443)) else (if s < 22 then (if s < 21 then 2297 else 3447) else (if s < 23 then 3443 else 4576))) else (if s < 28 then (if s < 26 then (if s < 25 then 2310 else 3443) else (if s < 27 then 3443 else 4576)) else (if s < 30 then (if s < 29 then 3443 else 4576) else (if s < 31 then 4576 else 5701))))) else (if s < 48 then (if s < 40 then (if s < 36 then (if s < 34 then (if s < 33 then 1155 else 2310) else (if s < 35 then 2310 else 3451)) else (if s < 38 then (if s < 37 then 2305 else 3446) else (if s < 39 then 3455 else 4584))) else (if s < 44 then (if s < 42 then (if s < 41 then 2305 else 3448) else (if s < 43 then 3451 else 4584)) else (if s < 46 then (if s < 45 then 3451 else 4584) else (if s < 47 then 4584 else 5709)))) else (if s < 56 then (if s < 52 then (if s < 50 then (if s < 49 then 2305 else 3446) else (if s < 51 then 3451 else 4584)) else (if s < 54 then (if s < 53 then 3447 else 4582) else (if s < 55 then 4584 else 5711))) else (if s < 60 then (if s < 58 then (if s < 57 then 3443 else 4576) else (if s < 59 then 4576 else 5709)) else (if s < 62 then (if s < 61 then 4576 else 5709) else (if s < 63 then 5709 else 6834)))))) else (if s < 96 then (if s < 80 then (if s < 72 then (if s < 68 then (if s < 66 then (if s < 65 then 1155 else 2301) else (if s < 67 then 2310 else 3453)) else (if s < 70 then (if s < 69 then 2310 else 3451) else (if s < 71 then 3457 else 4586))) else (if s < 76 then (if s < 74 then (if s < 73 then 2310 else 3451) else (if s < 75 then 3451 else 4584)) else (if s < 78 then (if s < 77 then 3443 else 4584) else (if s < 79 then 4584 else 5709)))) else (if s < 88 then (if s < 84 then (if s < 82 then (if s < 81 then 2310 else 3451) else (if s < 83 then 3451 else 4584)) else (if s < 86 then (if s < 85 then 3443 else 4584) else (if s < 87 then 4584 else 5713))) else (if s < 92 then (if s < 90 then (if s < 89 then 3443 else 4576) else (if s < 91 then 4576 else 5709)) else (if s < 94 then (if s < 93 then 4576 else 5709) else (if s < 95 then 5709 else 6834))))) else (if s < 112 then (if s < 104 then (if s < 100 then (if s < 98 then (if s < 97 then 2310 else 3451) else (if s < 99 then 3451 else 4586)) else (if s < 102 then (if s < 101 then 3443 else 4578) else (if s < 103 then 4584 else 5713))) else (if s < 108 then (if s < 106 then (if s < 105 then 3443 else 4584) else (if s < 107 then 4584 else 5709)) else (if s < 110 then (if s < 109 then 4576 else 5709) else (if s < 111 then 5709 else 6834)))) else (if s < 120 then (if s < 116 then (if s < 114 then (if s < 113 then 3443 else 4584) else (if s < 115 then 4584 else 5711)) else (if s < 118 then (if s < 117 then 4576 else 5711) else (if s < 119 then 5711 else 6838))) else (if s < 124 then (if s < 122 then (if s < 121 then 4576 else 5709) else (if s < 123 then 5709 else 6834)) else (if s < 126 then (if s < 125 then 5701 else 6834) else (if s < 127 then 6834 else 7959)))))))
def witness28 (S : Mask (groundSize 28)) : ℤ := lookup28 S.val

theorem witness28_table : ∀ S : Mask (groundSize 28),
    witness28 S = table28[S.val]! := by decide +kernel

theorem witness28_local_mono : MaskLocalMono witness28 := by
  unfold MaskLocalMono
  decide +kernel

theorem witness28_local_squares : MaskLocalSquares witness28 := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness28_pm : PMInt (groundSize 28) witness28 :=
  PMInt.of_local encoding_ok_7 (by decide +kernel)
    witness28_local_mono witness28_local_squares

theorem witness28_first : MatchesInt (fun S => witness28 (origMask 28 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness28_second : MatchesInt (fun S => witness28 (copyMask 28 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness28_adhesive : AdhesiveInt 28 witness28 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_28 : ∃ g : Mask (groundSize 28) → ℝ,
    PM (groundSize 28) g ∧ Matches (firstRestrict 28 g) ∧
    Matches (secondRestrict 28 g) ∧ Adhesive 28 g :=
  positive_of_int 28 witness28 witness28_pm witness28_first witness28_second witness28_adhesive

#print axioms witness28_pm
end InfoE3
