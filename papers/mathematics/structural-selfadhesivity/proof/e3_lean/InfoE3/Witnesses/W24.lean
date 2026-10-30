import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table24 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2305, 2310, 3440, 1155, 2305, 2310, 3440, 2300, 3450, 3440, 4570,
  1155, 2305, 2310, 3440, 2295, 3445, 3440, 4570, 2310, 3440, 3440, 4570, 3440, 4570, 4570, 5690,
  1155, 2310, 2310, 3465, 2310, 3460, 3465, 4595, 2305, 3455, 3459, 4589, 3449, 4599, 4589, 5719,
  2305, 3455, 3460, 4590, 3445, 4595, 4590, 5720, 3440, 4570, 4570, 5700, 4570, 5700, 5700, 6820,
  1155, 2310, 2310, 3463, 2310, 3460, 3463, 4593, 2310, 3460, 3463, 4593, 3454, 4603, 4593, 5723,
  2310, 3460, 3463, 4593, 3450, 4596, 4593, 5721, 3440, 4570, 4570, 5700, 4570, 5700, 5700, 6820,
  2310, 3460, 3463, 4606, 3461, 4610, 4606, 5736, 3440, 4590, 4593, 5723, 4584, 5733, 5723, 6853,
  3440, 4590, 4593, 5723, 4580, 5726, 5723, 6851, 4570, 5700, 5700, 6830, 5700, 6830, 6830, 7950,
  1155, 2308, 2310, 3463, 2308, 3458, 3463, 4593, 2300, 3450, 3453, 4583, 3444, 4593, 4583, 5713,
  2295, 3445, 3450, 4580, 3435, 4585, 4580, 5710, 3440, 4570, 4570, 5700, 4570, 5700, 5700, 6820,
  2305, 3458, 3460, 4613, 3458, 4608, 4613, 5743, 3450, 4599, 4602, 5732, 4593, 5742, 5732, 6862,
  3445, 4595, 4600, 5730, 4585, 5735, 5730, 6860, 4570, 5700, 5700, 6830, 5700, 6830, 6830, 7950,
  2310, 3461, 3463, 4606, 3461, 4611, 4606, 5736, 3440, 4590, 4593, 5723, 4584, 5733, 5723, 6853,
  3440, 4590, 4593, 5723, 4580, 5726, 5723, 6851, 4570, 5700, 5700, 6830, 5700, 6830, 6830, 7950,
  3440, 4590, 4592, 5735, 4591, 5740, 5735, 6865, 4570, 5719, 5722, 6852, 5713, 6862, 6852, 7982,
  4570, 5719, 5722, 6852, 5710, 6855, 6852, 7980, 5690, 6820, 6820, 7950, 6820, 7950, 7950, 9070
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup24 (s : Nat) : ℤ := (if s < 128 then (if s < 64 then (if s < 32 then (if s < 16 then (if s < 8 then (if s < 4 then (if s < 2 then (if s < 1 then 0 else 1155) else (if s < 3 then 1155 else 2310)) else (if s < 6 then (if s < 5 then 1155 else 2305) else (if s < 7 then 2310 else 3440))) else (if s < 12 then (if s < 10 then (if s < 9 then 1155 else 2305) else (if s < 11 then 2310 else 3440)) else (if s < 14 then (if s < 13 then 2300 else 3450) else (if s < 15 then 3440 else 4570)))) else (if s < 24 then (if s < 20 then (if s < 18 then (if s < 17 then 1155 else 2305) else (if s < 19 then 2310 else 3440)) else (if s < 22 then (if s < 21 then 2295 else 3445) else (if s < 23 then 3440 else 4570))) else (if s < 28 then (if s < 26 then (if s < 25 then 2310 else 3440) else (if s < 27 then 3440 else 4570)) else (if s < 30 then (if s < 29 then 3440 else 4570) else (if s < 31 then 4570 else 5690))))) else (if s < 48 then (if s < 40 then (if s < 36 then (if s < 34 then (if s < 33 then 1155 else 2310) else (if s < 35 then 2310 else 3465)) else (if s < 38 then (if s < 37 then 2310 else 3460) else (if s < 39 then 3465 else 4595))) else (if s < 44 then (if s < 42 then (if s < 41 then 2305 else 3455) else (if s < 43 then 3459 else 4589)) else (if s < 46 then (if s < 45 then 3449 else 4599) else (if s < 47 then 4589 else 5719)))) else (if s < 56 then (if s < 52 then (if s < 50 then (if s < 49 then 2305 else 3455) else (if s < 51 then 3460 else 4590)) else (if s < 54 then (if s < 53 then 3445 else 4595) else (if s < 55 then 4590 else 5720))) else (if s < 60 then (if s < 58 then (if s < 57 then 3440 else 4570) else (if s < 59 then 4570 else 5700)) else (if s < 62 then (if s < 61 then 4570 else 5700) else (if s < 63 then 5700 else 6820)))))) else (if s < 96 then (if s < 80 then (if s < 72 then (if s < 68 then (if s < 66 then (if s < 65 then 1155 else 2310) else (if s < 67 then 2310 else 3463)) else (if s < 70 then (if s < 69 then 2310 else 3460) else (if s < 71 then 3463 else 4593))) else (if s < 76 then (if s < 74 then (if s < 73 then 2310 else 3460) else (if s < 75 then 3463 else 4593)) else (if s < 78 then (if s < 77 then 3454 else 4603) else (if s < 79 then 4593 else 5723)))) else (if s < 88 then (if s < 84 then (if s < 82 then (if s < 81 then 2310 else 3460) else (if s < 83 then 3463 else 4593)) else (if s < 86 then (if s < 85 then 3450 else 4596) else (if s < 87 then 4593 else 5721))) else (if s < 92 then (if s < 90 then (if s < 89 then 3440 else 4570) else (if s < 91 then 4570 else 5700)) else (if s < 94 then (if s < 93 then 4570 else 5700) else (if s < 95 then 5700 else 6820))))) else (if s < 112 then (if s < 104 then (if s < 100 then (if s < 98 then (if s < 97 then 2310 else 3460) else (if s < 99 then 3463 else 4606)) else (if s < 102 then (if s < 101 then 3461 else 4610) else (if s < 103 then 4606 else 5736))) else (if s < 108 then (if s < 106 then (if s < 105 then 3440 else 4590) else (if s < 107 then 4593 else 5723)) else (if s < 110 then (if s < 109 then 4584 else 5733) else (if s < 111 then 5723 else 6853)))) else (if s < 120 then (if s < 116 then (if s < 114 then (if s < 113 then 3440 else 4590) else (if s < 115 then 4593 else 5723)) else (if s < 118 then (if s < 117 then 4580 else 5726) else (if s < 119 then 5723 else 6851))) else (if s < 124 then (if s < 122 then (if s < 121 then 4570 else 5700) else (if s < 123 then 5700 else 6830)) else (if s < 126 then (if s < 125 then 5700 else 6830) else (if s < 127 then 6830 else 7950))))))) else (if s < 192 then (if s < 160 then (if s < 144 then (if s < 136 then (if s < 132 then (if s < 130 then (if s < 129 then 1155 else 2308) else (if s < 131 then 2310 else 3463)) else (if s < 134 then (if s < 133 then 2308 else 3458) else (if s < 135 then 3463 else 4593))) else (if s < 140 then (if s < 138 then (if s < 137 then 2300 else 3450) else (if s < 139 then 3453 else 4583)) else (if s < 142 then (if s < 141 then 3444 else 4593) else (if s < 143 then 4583 else 5713)))) else (if s < 152 then (if s < 148 then (if s < 146 then (if s < 145 then 2295 else 3445) else (if s < 147 then 3450 else 4580)) else (if s < 150 then (if s < 149 then 3435 else 4585) else (if s < 151 then 4580 else 5710))) else (if s < 156 then (if s < 154 then (if s < 153 then 3440 else 4570) else (if s < 155 then 4570 else 5700)) else (if s < 158 then (if s < 157 then 4570 else 5700) else (if s < 159 then 5700 else 6820))))) else (if s < 176 then (if s < 168 then (if s < 164 then (if s < 162 then (if s < 161 then 2305 else 3458) else (if s < 163 then 3460 else 4613)) else (if s < 166 then (if s < 165 then 3458 else 4608) else (if s < 167 then 4613 else 5743))) else (if s < 172 then (if s < 170 then (if s < 169 then 3450 else 4599) else (if s < 171 then 4602 else 5732)) else (if s < 174 then (if s < 173 then 4593 else 5742) else (if s < 175 then 5732 else 6862)))) else (if s < 184 then (if s < 180 then (if s < 178 then (if s < 177 then 3445 else 4595) else (if s < 179 then 4600 else 5730)) else (if s < 182 then (if s < 181 then 4585 else 5735) else (if s < 183 then 5730 else 6860))) else (if s < 188 then (if s < 186 then (if s < 185 then 4570 else 5700) else (if s < 187 then 5700 else 6830)) else (if s < 190 then (if s < 189 then 5700 else 6830) else (if s < 191 then 6830 else 7950)))))) else (if s < 224 then (if s < 208 then (if s < 200 then (if s < 196 then (if s < 194 then (if s < 193 then 2310 else 3461) else (if s < 195 then 3463 else 4606)) else (if s < 198 then (if s < 197 then 3461 else 4611) else (if s < 199 then 4606 else 5736))) else (if s < 204 then (if s < 202 then (if s < 201 then 3440 else 4590) else (if s < 203 then 4593 else 5723)) else (if s < 206 then (if s < 205 then 4584 else 5733) else (if s < 207 then 5723 else 6853)))) else (if s < 216 then (if s < 212 then (if s < 210 then (if s < 209 then 3440 else 4590) else (if s < 211 then 4593 else 5723)) else (if s < 214 then (if s < 213 then 4580 else 5726) else (if s < 215 then 5723 else 6851))) else (if s < 220 then (if s < 218 then (if s < 217 then 4570 else 5700) else (if s < 219 then 5700 else 6830)) else (if s < 222 then (if s < 221 then 5700 else 6830) else (if s < 223 then 6830 else 7950))))) else (if s < 240 then (if s < 232 then (if s < 228 then (if s < 226 then (if s < 225 then 3440 else 4590) else (if s < 227 then 4592 else 5735)) else (if s < 230 then (if s < 229 then 4591 else 5740) else (if s < 231 then 5735 else 6865))) else (if s < 236 then (if s < 234 then (if s < 233 then 4570 else 5719) else (if s < 235 then 5722 else 6852)) else (if s < 238 then (if s < 237 then 5713 else 6862) else (if s < 239 then 6852 else 7982)))) else (if s < 248 then (if s < 244 then (if s < 242 then (if s < 241 then 4570 else 5719) else (if s < 243 then 5722 else 6852)) else (if s < 246 then (if s < 245 then 5710 else 6855) else (if s < 247 then 6852 else 7980))) else (if s < 252 then (if s < 250 then (if s < 249 then 5690 else 6820) else (if s < 251 then 6820 else 7950)) else (if s < 254 then (if s < 253 then 6820 else 7950) else (if s < 255 then 7950 else 9070))))))))
def witness24 (S : Mask (groundSize 24)) : ℤ := lookup24 S.val

theorem witness24_table : ∀ S : Mask (groundSize 24),
    witness24 S = table24[S.val]! := by decide +kernel

theorem witness24_local_mono : MaskLocalMono witness24 := by
  unfold MaskLocalMono
  decide +kernel

theorem witness24_local_squares : MaskLocalSquares witness24 := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness24_pm : PMInt (groundSize 24) witness24 :=
  PMInt.of_local encoding_ok_8 (by decide +kernel)
    witness24_local_mono witness24_local_squares

theorem witness24_first : MatchesInt (fun S => witness24 (origMask 24 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness24_second : MatchesInt (fun S => witness24 (copyMask 24 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness24_adhesive : AdhesiveInt 24 witness24 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_24 : ∃ g : Mask (groundSize 24) → ℝ,
    PM (groundSize 24) g ∧ Matches (firstRestrict 24 g) ∧
    Matches (secondRestrict 24 g) ∧ Adhesive 24 g :=
  positive_of_int 24 witness24 witness24_pm witness24_first witness24_second witness24_adhesive

#print axioms witness24_pm
end InfoE3
