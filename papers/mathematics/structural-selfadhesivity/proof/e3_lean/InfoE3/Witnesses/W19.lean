import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table19 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2307, 2310, 3456, 1155, 2307, 2310, 3456, 2306, 3458, 3456, 4602,
  1155, 2307, 2310, 3456, 2305, 3457, 3456, 4602, 2310, 3456, 3456, 4602, 3456, 4602, 4602, 5746,
  1155, 2307, 2310, 3456, 2308, 3459, 3456, 4602, 2310, 3459, 3456, 4602, 3459, 4606, 4602, 5748,
  2305, 3457, 3456, 4602, 3455, 4605, 4602, 5748, 3459, 4605, 4602, 5748, 4605, 5750, 5748, 6892,
  1155, 2307, 2310, 3456, 2308, 3455, 3456, 4602, 2307, 3459, 3456, 4602, 3458, 4605, 4602, 5748,
  2310, 3456, 3456, 4602, 3458, 4604, 4602, 5748, 3459, 4605, 4602, 5748, 4605, 5749, 5748, 6892,
  2306, 3458, 3456, 4602, 3458, 4605, 4602, 5748, 3457, 4606, 4602, 5748, 4605, 5752, 5748, 6894,
  3456, 4602, 4602, 5746, 4604, 5749, 5748, 6892, 4605, 5750, 5748, 6892, 5751, 6894, 6894, 8036
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup19 (s : Nat) : ℤ := (if s < 64 then (if s < 32 then (if s < 16 then (if s < 8 then (if s < 4 then (if s < 2 then (if s < 1 then 0 else 1155) else (if s < 3 then 1155 else 2310)) else (if s < 6 then (if s < 5 then 1155 else 2307) else (if s < 7 then 2310 else 3456))) else (if s < 12 then (if s < 10 then (if s < 9 then 1155 else 2307) else (if s < 11 then 2310 else 3456)) else (if s < 14 then (if s < 13 then 2306 else 3458) else (if s < 15 then 3456 else 4602)))) else (if s < 24 then (if s < 20 then (if s < 18 then (if s < 17 then 1155 else 2307) else (if s < 19 then 2310 else 3456)) else (if s < 22 then (if s < 21 then 2305 else 3457) else (if s < 23 then 3456 else 4602))) else (if s < 28 then (if s < 26 then (if s < 25 then 2310 else 3456) else (if s < 27 then 3456 else 4602)) else (if s < 30 then (if s < 29 then 3456 else 4602) else (if s < 31 then 4602 else 5746))))) else (if s < 48 then (if s < 40 then (if s < 36 then (if s < 34 then (if s < 33 then 1155 else 2307) else (if s < 35 then 2310 else 3456)) else (if s < 38 then (if s < 37 then 2308 else 3459) else (if s < 39 then 3456 else 4602))) else (if s < 44 then (if s < 42 then (if s < 41 then 2310 else 3459) else (if s < 43 then 3456 else 4602)) else (if s < 46 then (if s < 45 then 3459 else 4606) else (if s < 47 then 4602 else 5748)))) else (if s < 56 then (if s < 52 then (if s < 50 then (if s < 49 then 2305 else 3457) else (if s < 51 then 3456 else 4602)) else (if s < 54 then (if s < 53 then 3455 else 4605) else (if s < 55 then 4602 else 5748))) else (if s < 60 then (if s < 58 then (if s < 57 then 3459 else 4605) else (if s < 59 then 4602 else 5748)) else (if s < 62 then (if s < 61 then 4605 else 5750) else (if s < 63 then 5748 else 6892)))))) else (if s < 96 then (if s < 80 then (if s < 72 then (if s < 68 then (if s < 66 then (if s < 65 then 1155 else 2307) else (if s < 67 then 2310 else 3456)) else (if s < 70 then (if s < 69 then 2308 else 3455) else (if s < 71 then 3456 else 4602))) else (if s < 76 then (if s < 74 then (if s < 73 then 2307 else 3459) else (if s < 75 then 3456 else 4602)) else (if s < 78 then (if s < 77 then 3458 else 4605) else (if s < 79 then 4602 else 5748)))) else (if s < 88 then (if s < 84 then (if s < 82 then (if s < 81 then 2310 else 3456) else (if s < 83 then 3456 else 4602)) else (if s < 86 then (if s < 85 then 3458 else 4604) else (if s < 87 then 4602 else 5748))) else (if s < 92 then (if s < 90 then (if s < 89 then 3459 else 4605) else (if s < 91 then 4602 else 5748)) else (if s < 94 then (if s < 93 then 4605 else 5749) else (if s < 95 then 5748 else 6892))))) else (if s < 112 then (if s < 104 then (if s < 100 then (if s < 98 then (if s < 97 then 2306 else 3458) else (if s < 99 then 3456 else 4602)) else (if s < 102 then (if s < 101 then 3458 else 4605) else (if s < 103 then 4602 else 5748))) else (if s < 108 then (if s < 106 then (if s < 105 then 3457 else 4606) else (if s < 107 then 4602 else 5748)) else (if s < 110 then (if s < 109 then 4605 else 5752) else (if s < 111 then 5748 else 6894)))) else (if s < 120 then (if s < 116 then (if s < 114 then (if s < 113 then 3456 else 4602) else (if s < 115 then 4602 else 5746)) else (if s < 118 then (if s < 117 then 4604 else 5749) else (if s < 119 then 5748 else 6892))) else (if s < 124 then (if s < 122 then (if s < 121 then 4605 else 5750) else (if s < 123 then 5748 else 6892)) else (if s < 126 then (if s < 125 then 5751 else 6894) else (if s < 127 then 6894 else 8036)))))))
def witness19 (S : Mask (groundSize 19)) : ℤ := lookup19 S.val

theorem witness19_table : ∀ S : Mask (groundSize 19),
    witness19 S = table19[S.val]! := by decide +kernel

theorem witness19_local_mono : MaskLocalMono witness19 := by
  unfold MaskLocalMono
  decide +kernel

theorem witness19_local_squares : MaskLocalSquares witness19 := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness19_pm : PMInt (groundSize 19) witness19 :=
  PMInt.of_local encoding_ok_7 (by decide +kernel)
    witness19_local_mono witness19_local_squares

theorem witness19_first : MatchesInt (fun S => witness19 (origMask 19 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness19_second : MatchesInt (fun S => witness19 (copyMask 19 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness19_adhesive : AdhesiveInt 19 witness19 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_19 : ∃ g : Mask (groundSize 19) → ℝ,
    PM (groundSize 19) g ∧ Matches (firstRestrict 19 g) ∧
    Matches (secondRestrict 19 g) ∧ Adhesive 19 g :=
  positive_of_int 19 witness19 witness19_pm witness19_first witness19_second witness19_adhesive

#print axioms witness19_pm
end InfoE3
