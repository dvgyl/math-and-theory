import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table22 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2305, 2310, 3440, 1155, 2305, 2310, 3440, 2300, 3450, 3440, 4570,
  1155, 2305, 2310, 3440, 2295, 3445, 3440, 4570, 2310, 3440, 3440, 4570, 3440, 4570, 4570, 5690,
  1155, 2301, 2310, 3440, 2305, 3438, 3440, 4570, 2310, 3443, 3440, 4570, 3447, 4580, 4570, 5700,
  2305, 3446, 3440, 4570, 3445, 4577, 4570, 5700, 3447, 4577, 4570, 5700, 4577, 5700, 5700, 6820,
  1155, 2305, 2310, 3440, 2300, 3450, 3440, 4570, 2310, 3451, 3440, 4570, 3441, 4582, 4570, 5700,
  2310, 3451, 3440, 4570, 3440, 4581, 4570, 5700, 3451, 4581, 4570, 5700, 4581, 5702, 5700, 6820,
  2305, 3451, 3440, 4570, 3450, 4582, 4570, 5700, 3451, 4581, 4570, 5700, 4582, 5712, 5700, 6830,
  3440, 4581, 4570, 5700, 4570, 5702, 5690, 6820, 4581, 5711, 5700, 6830, 5702, 6823, 6820, 7940
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup22 (s : Nat) : ℤ := (if s < 64 then (if s < 32 then (if s < 16 then (if s < 8 then (if s < 4 then (if s < 2 then (if s < 1 then 0 else 1155) else (if s < 3 then 1155 else 2310)) else (if s < 6 then (if s < 5 then 1155 else 2305) else (if s < 7 then 2310 else 3440))) else (if s < 12 then (if s < 10 then (if s < 9 then 1155 else 2305) else (if s < 11 then 2310 else 3440)) else (if s < 14 then (if s < 13 then 2300 else 3450) else (if s < 15 then 3440 else 4570)))) else (if s < 24 then (if s < 20 then (if s < 18 then (if s < 17 then 1155 else 2305) else (if s < 19 then 2310 else 3440)) else (if s < 22 then (if s < 21 then 2295 else 3445) else (if s < 23 then 3440 else 4570))) else (if s < 28 then (if s < 26 then (if s < 25 then 2310 else 3440) else (if s < 27 then 3440 else 4570)) else (if s < 30 then (if s < 29 then 3440 else 4570) else (if s < 31 then 4570 else 5690))))) else (if s < 48 then (if s < 40 then (if s < 36 then (if s < 34 then (if s < 33 then 1155 else 2301) else (if s < 35 then 2310 else 3440)) else (if s < 38 then (if s < 37 then 2305 else 3438) else (if s < 39 then 3440 else 4570))) else (if s < 44 then (if s < 42 then (if s < 41 then 2310 else 3443) else (if s < 43 then 3440 else 4570)) else (if s < 46 then (if s < 45 then 3447 else 4580) else (if s < 47 then 4570 else 5700)))) else (if s < 56 then (if s < 52 then (if s < 50 then (if s < 49 then 2305 else 3446) else (if s < 51 then 3440 else 4570)) else (if s < 54 then (if s < 53 then 3445 else 4577) else (if s < 55 then 4570 else 5700))) else (if s < 60 then (if s < 58 then (if s < 57 then 3447 else 4577) else (if s < 59 then 4570 else 5700)) else (if s < 62 then (if s < 61 then 4577 else 5700) else (if s < 63 then 5700 else 6820)))))) else (if s < 96 then (if s < 80 then (if s < 72 then (if s < 68 then (if s < 66 then (if s < 65 then 1155 else 2305) else (if s < 67 then 2310 else 3440)) else (if s < 70 then (if s < 69 then 2300 else 3450) else (if s < 71 then 3440 else 4570))) else (if s < 76 then (if s < 74 then (if s < 73 then 2310 else 3451) else (if s < 75 then 3440 else 4570)) else (if s < 78 then (if s < 77 then 3441 else 4582) else (if s < 79 then 4570 else 5700)))) else (if s < 88 then (if s < 84 then (if s < 82 then (if s < 81 then 2310 else 3451) else (if s < 83 then 3440 else 4570)) else (if s < 86 then (if s < 85 then 3440 else 4581) else (if s < 87 then 4570 else 5700))) else (if s < 92 then (if s < 90 then (if s < 89 then 3451 else 4581) else (if s < 91 then 4570 else 5700)) else (if s < 94 then (if s < 93 then 4581 else 5702) else (if s < 95 then 5700 else 6820))))) else (if s < 112 then (if s < 104 then (if s < 100 then (if s < 98 then (if s < 97 then 2305 else 3451) else (if s < 99 then 3440 else 4570)) else (if s < 102 then (if s < 101 then 3450 else 4582) else (if s < 103 then 4570 else 5700))) else (if s < 108 then (if s < 106 then (if s < 105 then 3451 else 4581) else (if s < 107 then 4570 else 5700)) else (if s < 110 then (if s < 109 then 4582 else 5712) else (if s < 111 then 5700 else 6830)))) else (if s < 120 then (if s < 116 then (if s < 114 then (if s < 113 then 3440 else 4581) else (if s < 115 then 4570 else 5700)) else (if s < 118 then (if s < 117 then 4570 else 5702) else (if s < 119 then 5690 else 6820))) else (if s < 124 then (if s < 122 then (if s < 121 then 4581 else 5711) else (if s < 123 then 5700 else 6830)) else (if s < 126 then (if s < 125 then 5702 else 6823) else (if s < 127 then 6820 else 7940)))))))
def witness22 (S : Mask (groundSize 22)) : ℤ := lookup22 S.val

theorem witness22_table : ∀ S : Mask (groundSize 22),
    witness22 S = table22[S.val]! := by decide +kernel

theorem witness22_local_mono : MaskLocalMono witness22 := by
  unfold MaskLocalMono
  decide +kernel

theorem witness22_local_squares : MaskLocalSquares witness22 := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness22_pm : PMInt (groundSize 22) witness22 :=
  PMInt.of_local encoding_ok_7 (by decide +kernel)
    witness22_local_mono witness22_local_squares

theorem witness22_first : MatchesInt (fun S => witness22 (origMask 22 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness22_second : MatchesInt (fun S => witness22 (copyMask 22 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness22_adhesive : AdhesiveInt 22 witness22 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_22 : ∃ g : Mask (groundSize 22) → ℝ,
    PM (groundSize 22) g ∧ Matches (firstRestrict 22 g) ∧
    Matches (secondRestrict 22 g) ∧ Adhesive 22 g :=
  positive_of_int 22 witness22 witness22_pm witness22_first witness22_second witness22_adhesive

#print axioms witness22_pm
end InfoE3
