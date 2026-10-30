import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table06 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2304, 2310, 3435, 1155, 2304, 2310, 3435, 2298, 3447, 3435, 4560,
  1155, 2304, 2310, 3435, 2292, 3441, 3435, 4560, 2310, 3435, 3435, 4560, 3435, 4560, 4560, 5673,
  1155, 2310, 2310, 3459, 2304, 3450, 3435, 4560, 2310, 3459, 3459, 4584, 3443, 4588, 4560, 5685,
  2310, 3459, 3459, 4584, 3440, 4586, 4560, 5685, 3465, 4590, 4584, 5709, 4576, 5701, 5685, 6798,
  1155, 2310, 2310, 3459, 2298, 3447, 3435, 4560, 2310, 3459, 3459, 4584, 3437, 4584, 4560, 5685,
  2310, 3459, 3459, 4584, 3435, 4584, 4560, 5685, 3465, 4590, 4584, 5709, 4574, 5697, 5685, 6798,
  2304, 3459, 3435, 4584, 3447, 4592, 4560, 5685, 3459, 4602, 4584, 5709, 4582, 5725, 5685, 6810,
  3459, 4608, 4584, 5709, 4580, 5725, 5685, 6810, 4608, 5733, 5709, 6834, 5715, 6838, 6810, 7923,
  1155, 2310, 2310, 3459, 2292, 3441, 3435, 4560, 2310, 3457, 3459, 4584, 3435, 4582, 4560, 5685,
  2305, 3453, 3459, 4584, 3428, 4576, 4560, 5685, 3459, 4584, 4584, 5709, 4570, 5695, 5685, 6798,
  2304, 3459, 3435, 4584, 3441, 4586, 4560, 5685, 3453, 4598, 4584, 5709, 4578, 5723, 5685, 6810,
  3454, 4600, 4584, 5709, 4576, 5721, 5685, 6810, 4600, 5725, 5709, 6834, 5711, 6836, 6810, 7923,
  2310, 3465, 3435, 4584, 3435, 4584, 4560, 5685, 3459, 4606, 4584, 5709, 4574, 5719, 5685, 6810,
  3459, 4607, 4584, 5709, 4571, 5719, 5685, 6810, 4608, 5733, 5709, 6834, 5709, 6832, 6810, 7923,
  3435, 4590, 4560, 5703, 4560, 5705, 5673, 6798, 4584, 5727, 5703, 6828, 5695, 6838, 6798, 7923,
  4581, 5727, 5703, 6828, 5693, 6838, 6798, 7923, 5727, 6852, 6828, 7953, 6828, 7951, 7923, 9036
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup06 (s : Nat) : ℤ := (if s < 128 then (if s < 64 then (if s < 32 then (if s < 16 then (if s < 8 then (if s < 4 then (if s < 2 then (if s < 1 then 0 else 1155) else (if s < 3 then 1155 else 2310)) else (if s < 6 then (if s < 5 then 1155 else 2304) else (if s < 7 then 2310 else 3435))) else (if s < 12 then (if s < 10 then (if s < 9 then 1155 else 2304) else (if s < 11 then 2310 else 3435)) else (if s < 14 then (if s < 13 then 2298 else 3447) else (if s < 15 then 3435 else 4560)))) else (if s < 24 then (if s < 20 then (if s < 18 then (if s < 17 then 1155 else 2304) else (if s < 19 then 2310 else 3435)) else (if s < 22 then (if s < 21 then 2292 else 3441) else (if s < 23 then 3435 else 4560))) else (if s < 28 then (if s < 26 then (if s < 25 then 2310 else 3435) else (if s < 27 then 3435 else 4560)) else (if s < 30 then (if s < 29 then 3435 else 4560) else (if s < 31 then 4560 else 5673))))) else (if s < 48 then (if s < 40 then (if s < 36 then (if s < 34 then (if s < 33 then 1155 else 2310) else (if s < 35 then 2310 else 3459)) else (if s < 38 then (if s < 37 then 2304 else 3450) else (if s < 39 then 3435 else 4560))) else (if s < 44 then (if s < 42 then (if s < 41 then 2310 else 3459) else (if s < 43 then 3459 else 4584)) else (if s < 46 then (if s < 45 then 3443 else 4588) else (if s < 47 then 4560 else 5685)))) else (if s < 56 then (if s < 52 then (if s < 50 then (if s < 49 then 2310 else 3459) else (if s < 51 then 3459 else 4584)) else (if s < 54 then (if s < 53 then 3440 else 4586) else (if s < 55 then 4560 else 5685))) else (if s < 60 then (if s < 58 then (if s < 57 then 3465 else 4590) else (if s < 59 then 4584 else 5709)) else (if s < 62 then (if s < 61 then 4576 else 5701) else (if s < 63 then 5685 else 6798)))))) else (if s < 96 then (if s < 80 then (if s < 72 then (if s < 68 then (if s < 66 then (if s < 65 then 1155 else 2310) else (if s < 67 then 2310 else 3459)) else (if s < 70 then (if s < 69 then 2298 else 3447) else (if s < 71 then 3435 else 4560))) else (if s < 76 then (if s < 74 then (if s < 73 then 2310 else 3459) else (if s < 75 then 3459 else 4584)) else (if s < 78 then (if s < 77 then 3437 else 4584) else (if s < 79 then 4560 else 5685)))) else (if s < 88 then (if s < 84 then (if s < 82 then (if s < 81 then 2310 else 3459) else (if s < 83 then 3459 else 4584)) else (if s < 86 then (if s < 85 then 3435 else 4584) else (if s < 87 then 4560 else 5685))) else (if s < 92 then (if s < 90 then (if s < 89 then 3465 else 4590) else (if s < 91 then 4584 else 5709)) else (if s < 94 then (if s < 93 then 4574 else 5697) else (if s < 95 then 5685 else 6798))))) else (if s < 112 then (if s < 104 then (if s < 100 then (if s < 98 then (if s < 97 then 2304 else 3459) else (if s < 99 then 3435 else 4584)) else (if s < 102 then (if s < 101 then 3447 else 4592) else (if s < 103 then 4560 else 5685))) else (if s < 108 then (if s < 106 then (if s < 105 then 3459 else 4602) else (if s < 107 then 4584 else 5709)) else (if s < 110 then (if s < 109 then 4582 else 5725) else (if s < 111 then 5685 else 6810)))) else (if s < 120 then (if s < 116 then (if s < 114 then (if s < 113 then 3459 else 4608) else (if s < 115 then 4584 else 5709)) else (if s < 118 then (if s < 117 then 4580 else 5725) else (if s < 119 then 5685 else 6810))) else (if s < 124 then (if s < 122 then (if s < 121 then 4608 else 5733) else (if s < 123 then 5709 else 6834)) else (if s < 126 then (if s < 125 then 5715 else 6838) else (if s < 127 then 6810 else 7923))))))) else (if s < 192 then (if s < 160 then (if s < 144 then (if s < 136 then (if s < 132 then (if s < 130 then (if s < 129 then 1155 else 2310) else (if s < 131 then 2310 else 3459)) else (if s < 134 then (if s < 133 then 2292 else 3441) else (if s < 135 then 3435 else 4560))) else (if s < 140 then (if s < 138 then (if s < 137 then 2310 else 3457) else (if s < 139 then 3459 else 4584)) else (if s < 142 then (if s < 141 then 3435 else 4582) else (if s < 143 then 4560 else 5685)))) else (if s < 152 then (if s < 148 then (if s < 146 then (if s < 145 then 2305 else 3453) else (if s < 147 then 3459 else 4584)) else (if s < 150 then (if s < 149 then 3428 else 4576) else (if s < 151 then 4560 else 5685))) else (if s < 156 then (if s < 154 then (if s < 153 then 3459 else 4584) else (if s < 155 then 4584 else 5709)) else (if s < 158 then (if s < 157 then 4570 else 5695) else (if s < 159 then 5685 else 6798))))) else (if s < 176 then (if s < 168 then (if s < 164 then (if s < 162 then (if s < 161 then 2304 else 3459) else (if s < 163 then 3435 else 4584)) else (if s < 166 then (if s < 165 then 3441 else 4586) else (if s < 167 then 4560 else 5685))) else (if s < 172 then (if s < 170 then (if s < 169 then 3453 else 4598) else (if s < 171 then 4584 else 5709)) else (if s < 174 then (if s < 173 then 4578 else 5723) else (if s < 175 then 5685 else 6810)))) else (if s < 184 then (if s < 180 then (if s < 178 then (if s < 177 then 3454 else 4600) else (if s < 179 then 4584 else 5709)) else (if s < 182 then (if s < 181 then 4576 else 5721) else (if s < 183 then 5685 else 6810))) else (if s < 188 then (if s < 186 then (if s < 185 then 4600 else 5725) else (if s < 187 then 5709 else 6834)) else (if s < 190 then (if s < 189 then 5711 else 6836) else (if s < 191 then 6810 else 7923)))))) else (if s < 224 then (if s < 208 then (if s < 200 then (if s < 196 then (if s < 194 then (if s < 193 then 2310 else 3465) else (if s < 195 then 3435 else 4584)) else (if s < 198 then (if s < 197 then 3435 else 4584) else (if s < 199 then 4560 else 5685))) else (if s < 204 then (if s < 202 then (if s < 201 then 3459 else 4606) else (if s < 203 then 4584 else 5709)) else (if s < 206 then (if s < 205 then 4574 else 5719) else (if s < 207 then 5685 else 6810)))) else (if s < 216 then (if s < 212 then (if s < 210 then (if s < 209 then 3459 else 4607) else (if s < 211 then 4584 else 5709)) else (if s < 214 then (if s < 213 then 4571 else 5719) else (if s < 215 then 5685 else 6810))) else (if s < 220 then (if s < 218 then (if s < 217 then 4608 else 5733) else (if s < 219 then 5709 else 6834)) else (if s < 222 then (if s < 221 then 5709 else 6832) else (if s < 223 then 6810 else 7923))))) else (if s < 240 then (if s < 232 then (if s < 228 then (if s < 226 then (if s < 225 then 3435 else 4590) else (if s < 227 then 4560 else 5703)) else (if s < 230 then (if s < 229 then 4560 else 5705) else (if s < 231 then 5673 else 6798))) else (if s < 236 then (if s < 234 then (if s < 233 then 4584 else 5727) else (if s < 235 then 5703 else 6828)) else (if s < 238 then (if s < 237 then 5695 else 6838) else (if s < 239 then 6798 else 7923)))) else (if s < 248 then (if s < 244 then (if s < 242 then (if s < 241 then 4581 else 5727) else (if s < 243 then 5703 else 6828)) else (if s < 246 then (if s < 245 then 5693 else 6838) else (if s < 247 then 6798 else 7923))) else (if s < 252 then (if s < 250 then (if s < 249 then 5727 else 6852) else (if s < 251 then 6828 else 7953)) else (if s < 254 then (if s < 253 then 6828 else 7951) else (if s < 255 then 7923 else 9036))))))))
def witness06 (S : Mask (groundSize 6)) : ℤ := lookup06 S.val

theorem witness06_table : ∀ S : Mask (groundSize 6),
    witness06 S = table06[S.val]! := by decide +kernel

theorem witness06_local_mono : MaskLocalMono witness06 := by
  unfold MaskLocalMono
  decide +kernel

theorem witness06_local_squares : MaskLocalSquares witness06 := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness06_pm : PMInt (groundSize 6) witness06 :=
  PMInt.of_local encoding_ok_8 (by decide +kernel)
    witness06_local_mono witness06_local_squares

theorem witness06_first : MatchesInt (fun S => witness06 (origMask 6 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness06_second : MatchesInt (fun S => witness06 (copyMask 6 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness06_adhesive : AdhesiveInt 6 witness06 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_06 : ∃ g : Mask (groundSize 6) → ℝ,
    PM (groundSize 6) g ∧ Matches (firstRestrict 6 g) ∧
    Matches (secondRestrict 6 g) ∧ Adhesive 6 g :=
  positive_of_int 6 witness06 witness06_pm witness06_first witness06_second witness06_adhesive

#print axioms witness06_pm
end InfoE3
