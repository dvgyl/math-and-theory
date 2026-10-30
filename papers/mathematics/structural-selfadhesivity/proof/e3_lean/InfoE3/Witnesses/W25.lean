import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table25 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2306, 2310, 3454, 1155, 2306, 2310, 3454, 2305, 3456, 3454, 4598,
  1155, 2306, 2310, 3454, 2304, 3455, 3454, 4598, 2310, 3454, 3454, 4598, 3454, 4598, 4598, 5740,
  1155, 2310, 2310, 3458, 2310, 3458, 3458, 4600, 2310, 3454, 3458, 4602, 3458, 4602, 4602, 5744,
  2310, 3454, 3458, 4602, 3458, 4602, 4602, 5744, 3454, 4598, 4598, 5742, 4598, 5742, 5742, 6884,
  1155, 2306, 2310, 3458, 2307, 3457, 3458, 4600, 2305, 3456, 3458, 4602, 3453, 4602, 4602, 5744,
  2304, 3455, 3458, 4602, 3452, 4601, 4602, 5744, 3454, 4598, 4598, 5742, 4598, 5742, 5742, 6884,
  2310, 3454, 3458, 4600, 3458, 4600, 4602, 5742, 3454, 4598, 4602, 5744, 4602, 5744, 5746, 6886,
  3454, 4598, 4602, 5744, 4602, 5744, 5746, 6886, 4598, 5740, 5742, 6884, 5742, 6884, 6886, 8026
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup25 (s : Nat) : ℤ := (if s < 64 then (if s < 32 then (if s < 16 then (if s < 8 then (if s < 4 then (if s < 2 then (if s < 1 then 0 else 1155) else (if s < 3 then 1155 else 2310)) else (if s < 6 then (if s < 5 then 1155 else 2306) else (if s < 7 then 2310 else 3454))) else (if s < 12 then (if s < 10 then (if s < 9 then 1155 else 2306) else (if s < 11 then 2310 else 3454)) else (if s < 14 then (if s < 13 then 2305 else 3456) else (if s < 15 then 3454 else 4598)))) else (if s < 24 then (if s < 20 then (if s < 18 then (if s < 17 then 1155 else 2306) else (if s < 19 then 2310 else 3454)) else (if s < 22 then (if s < 21 then 2304 else 3455) else (if s < 23 then 3454 else 4598))) else (if s < 28 then (if s < 26 then (if s < 25 then 2310 else 3454) else (if s < 27 then 3454 else 4598)) else (if s < 30 then (if s < 29 then 3454 else 4598) else (if s < 31 then 4598 else 5740))))) else (if s < 48 then (if s < 40 then (if s < 36 then (if s < 34 then (if s < 33 then 1155 else 2310) else (if s < 35 then 2310 else 3458)) else (if s < 38 then (if s < 37 then 2310 else 3458) else (if s < 39 then 3458 else 4600))) else (if s < 44 then (if s < 42 then (if s < 41 then 2310 else 3454) else (if s < 43 then 3458 else 4602)) else (if s < 46 then (if s < 45 then 3458 else 4602) else (if s < 47 then 4602 else 5744)))) else (if s < 56 then (if s < 52 then (if s < 50 then (if s < 49 then 2310 else 3454) else (if s < 51 then 3458 else 4602)) else (if s < 54 then (if s < 53 then 3458 else 4602) else (if s < 55 then 4602 else 5744))) else (if s < 60 then (if s < 58 then (if s < 57 then 3454 else 4598) else (if s < 59 then 4598 else 5742)) else (if s < 62 then (if s < 61 then 4598 else 5742) else (if s < 63 then 5742 else 6884)))))) else (if s < 96 then (if s < 80 then (if s < 72 then (if s < 68 then (if s < 66 then (if s < 65 then 1155 else 2306) else (if s < 67 then 2310 else 3458)) else (if s < 70 then (if s < 69 then 2307 else 3457) else (if s < 71 then 3458 else 4600))) else (if s < 76 then (if s < 74 then (if s < 73 then 2305 else 3456) else (if s < 75 then 3458 else 4602)) else (if s < 78 then (if s < 77 then 3453 else 4602) else (if s < 79 then 4602 else 5744)))) else (if s < 88 then (if s < 84 then (if s < 82 then (if s < 81 then 2304 else 3455) else (if s < 83 then 3458 else 4602)) else (if s < 86 then (if s < 85 then 3452 else 4601) else (if s < 87 then 4602 else 5744))) else (if s < 92 then (if s < 90 then (if s < 89 then 3454 else 4598) else (if s < 91 then 4598 else 5742)) else (if s < 94 then (if s < 93 then 4598 else 5742) else (if s < 95 then 5742 else 6884))))) else (if s < 112 then (if s < 104 then (if s < 100 then (if s < 98 then (if s < 97 then 2310 else 3454) else (if s < 99 then 3458 else 4600)) else (if s < 102 then (if s < 101 then 3458 else 4600) else (if s < 103 then 4602 else 5742))) else (if s < 108 then (if s < 106 then (if s < 105 then 3454 else 4598) else (if s < 107 then 4602 else 5744)) else (if s < 110 then (if s < 109 then 4602 else 5744) else (if s < 111 then 5746 else 6886)))) else (if s < 120 then (if s < 116 then (if s < 114 then (if s < 113 then 3454 else 4598) else (if s < 115 then 4602 else 5744)) else (if s < 118 then (if s < 117 then 4602 else 5744) else (if s < 119 then 5746 else 6886))) else (if s < 124 then (if s < 122 then (if s < 121 then 4598 else 5740) else (if s < 123 then 5742 else 6884)) else (if s < 126 then (if s < 125 then 5742 else 6884) else (if s < 127 then 6886 else 8026)))))))
def witness25 (S : Mask (groundSize 25)) : ℤ := lookup25 S.val

theorem witness25_table : ∀ S : Mask (groundSize 25),
    witness25 S = table25[S.val]! := by decide +kernel

theorem witness25_local_mono : MaskLocalMono witness25 := by
  unfold MaskLocalMono
  decide +kernel

theorem witness25_local_squares : MaskLocalSquares witness25 := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness25_pm : PMInt (groundSize 25) witness25 :=
  PMInt.of_local encoding_ok_7 (by decide +kernel)
    witness25_local_mono witness25_local_squares

theorem witness25_first : MatchesInt (fun S => witness25 (origMask 25 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness25_second : MatchesInt (fun S => witness25 (copyMask 25 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness25_adhesive : AdhesiveInt 25 witness25 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_25 : ∃ g : Mask (groundSize 25) → ℝ,
    PM (groundSize 25) g ∧ Matches (firstRestrict 25 g) ∧
    Matches (secondRestrict 25 g) ∧ Adhesive 25 g :=
  positive_of_int 25 witness25 witness25_pm witness25_first witness25_second witness25_adhesive

#print axioms witness25_pm
end InfoE3
