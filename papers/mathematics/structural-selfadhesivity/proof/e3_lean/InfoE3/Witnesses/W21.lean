import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table21 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2307, 2310, 3450, 1155, 2307, 2310, 3450, 2304, 3456, 3450, 4590,
  1155, 2307, 2310, 3450, 2301, 3453, 3450, 4590, 2310, 3450, 3450, 4590, 3450, 4590, 4590, 5724,
  1155, 2310, 2310, 3457, 2310, 3450, 3464, 4592, 2310, 3456, 3462, 4595, 3456, 4596, 4602, 5730,
  2310, 3450, 3460, 4592, 3450, 4590, 4599, 5727, 3461, 4593, 4600, 5727, 4595, 5727, 5734, 6861,
  1155, 2307, 2310, 3458, 2304, 3456, 3459, 4598, 2310, 3459, 3461, 4598, 3453, 4602, 4599, 5736,
  2310, 3450, 3465, 4593, 3450, 4590, 4599, 5727, 3461, 4593, 4601, 5728, 4595, 5727, 5735, 6861,
  2310, 3450, 3464, 4597, 3450, 4590, 4604, 5732, 3456, 4596, 4604, 5735, 4596, 5736, 5742, 6870,
  3450, 4590, 4600, 5727, 4590, 5724, 5734, 6861, 4596, 5728, 5735, 6862, 5730, 6861, 6869, 7995
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup21 (s : Nat) : ℤ := (if s < 64 then (if s < 32 then (if s < 16 then (if s < 8 then (if s < 4 then (if s < 2 then (if s < 1 then 0 else 1155) else (if s < 3 then 1155 else 2310)) else (if s < 6 then (if s < 5 then 1155 else 2307) else (if s < 7 then 2310 else 3450))) else (if s < 12 then (if s < 10 then (if s < 9 then 1155 else 2307) else (if s < 11 then 2310 else 3450)) else (if s < 14 then (if s < 13 then 2304 else 3456) else (if s < 15 then 3450 else 4590)))) else (if s < 24 then (if s < 20 then (if s < 18 then (if s < 17 then 1155 else 2307) else (if s < 19 then 2310 else 3450)) else (if s < 22 then (if s < 21 then 2301 else 3453) else (if s < 23 then 3450 else 4590))) else (if s < 28 then (if s < 26 then (if s < 25 then 2310 else 3450) else (if s < 27 then 3450 else 4590)) else (if s < 30 then (if s < 29 then 3450 else 4590) else (if s < 31 then 4590 else 5724))))) else (if s < 48 then (if s < 40 then (if s < 36 then (if s < 34 then (if s < 33 then 1155 else 2310) else (if s < 35 then 2310 else 3457)) else (if s < 38 then (if s < 37 then 2310 else 3450) else (if s < 39 then 3464 else 4592))) else (if s < 44 then (if s < 42 then (if s < 41 then 2310 else 3456) else (if s < 43 then 3462 else 4595)) else (if s < 46 then (if s < 45 then 3456 else 4596) else (if s < 47 then 4602 else 5730)))) else (if s < 56 then (if s < 52 then (if s < 50 then (if s < 49 then 2310 else 3450) else (if s < 51 then 3460 else 4592)) else (if s < 54 then (if s < 53 then 3450 else 4590) else (if s < 55 then 4599 else 5727))) else (if s < 60 then (if s < 58 then (if s < 57 then 3461 else 4593) else (if s < 59 then 4600 else 5727)) else (if s < 62 then (if s < 61 then 4595 else 5727) else (if s < 63 then 5734 else 6861)))))) else (if s < 96 then (if s < 80 then (if s < 72 then (if s < 68 then (if s < 66 then (if s < 65 then 1155 else 2307) else (if s < 67 then 2310 else 3458)) else (if s < 70 then (if s < 69 then 2304 else 3456) else (if s < 71 then 3459 else 4598))) else (if s < 76 then (if s < 74 then (if s < 73 then 2310 else 3459) else (if s < 75 then 3461 else 4598)) else (if s < 78 then (if s < 77 then 3453 else 4602) else (if s < 79 then 4599 else 5736)))) else (if s < 88 then (if s < 84 then (if s < 82 then (if s < 81 then 2310 else 3450) else (if s < 83 then 3465 else 4593)) else (if s < 86 then (if s < 85 then 3450 else 4590) else (if s < 87 then 4599 else 5727))) else (if s < 92 then (if s < 90 then (if s < 89 then 3461 else 4593) else (if s < 91 then 4601 else 5728)) else (if s < 94 then (if s < 93 then 4595 else 5727) else (if s < 95 then 5735 else 6861))))) else (if s < 112 then (if s < 104 then (if s < 100 then (if s < 98 then (if s < 97 then 2310 else 3450) else (if s < 99 then 3464 else 4597)) else (if s < 102 then (if s < 101 then 3450 else 4590) else (if s < 103 then 4604 else 5732))) else (if s < 108 then (if s < 106 then (if s < 105 then 3456 else 4596) else (if s < 107 then 4604 else 5735)) else (if s < 110 then (if s < 109 then 4596 else 5736) else (if s < 111 then 5742 else 6870)))) else (if s < 120 then (if s < 116 then (if s < 114 then (if s < 113 then 3450 else 4590) else (if s < 115 then 4600 else 5727)) else (if s < 118 then (if s < 117 then 4590 else 5724) else (if s < 119 then 5734 else 6861))) else (if s < 124 then (if s < 122 then (if s < 121 then 4596 else 5728) else (if s < 123 then 5735 else 6862)) else (if s < 126 then (if s < 125 then 5730 else 6861) else (if s < 127 then 6869 else 7995)))))))
def witness21 (S : Mask (groundSize 21)) : ℤ := lookup21 S.val

theorem witness21_table : ∀ S : Mask (groundSize 21),
    witness21 S = table21[S.val]! := by decide +kernel

theorem witness21_local_mono : MaskLocalMono witness21 := by
  unfold MaskLocalMono
  decide +kernel

theorem witness21_local_squares : MaskLocalSquares witness21 := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness21_pm : PMInt (groundSize 21) witness21 :=
  PMInt.of_local encoding_ok_7 (by decide +kernel)
    witness21_local_mono witness21_local_squares

theorem witness21_first : MatchesInt (fun S => witness21 (origMask 21 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness21_second : MatchesInt (fun S => witness21 (copyMask 21 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness21_adhesive : AdhesiveInt 21 witness21 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_21 : ∃ g : Mask (groundSize 21) → ℝ,
    PM (groundSize 21) g ∧ Matches (firstRestrict 21 g) ∧
    Matches (secondRestrict 21 g) ∧ Adhesive 21 g :=
  positive_of_int 21 witness21 witness21_pm witness21_first witness21_second witness21_adhesive

#print axioms witness21_pm
end InfoE3
