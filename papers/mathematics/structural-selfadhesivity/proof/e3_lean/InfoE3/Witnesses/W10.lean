import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table10 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2283, 2310, 3363, 1155, 2283, 2310, 3363, 2267, 3395, 3363, 4416,
  1155, 2283, 2310, 3363, 2251, 3379, 3363, 4416, 2310, 3363, 3363, 4416, 3363, 4416, 4416, 5437,
  1155, 2310, 2310, 3402, 2310, 3420, 3402, 4455, 2283, 3383, 3363, 4416, 3395, 4474, 4416, 5469,
  2310, 3405, 3402, 4455, 3406, 4488, 4455, 5508, 3410, 4463, 4416, 5469, 4463, 5495, 5469, 6490,
  1155, 2297, 2310, 3402, 2310, 3425, 3402, 4455, 2267, 3368, 3363, 4416, 3373, 4474, 4416, 5469,
  2310, 3402, 3402, 4455, 3406, 4488, 4455, 5508, 3395, 4448, 4416, 5469, 4448, 5495, 5469, 6490,
  2283, 3425, 3363, 4455, 3425, 4535, 4455, 5508, 3395, 4468, 4416, 5469, 4486, 5553, 5469, 6522,
  3438, 4520, 4455, 5508, 4506, 5588, 5508, 6561, 4495, 5548, 5469, 6522, 5548, 6574, 6522, 7543,
  1155, 2279, 2310, 3402, 2310, 3407, 3402, 4455, 2310, 3383, 3363, 4416, 3401, 4474, 4416, 5469,
  2310, 3385, 3402, 4455, 3406, 4481, 4455, 5508, 3410, 4463, 4416, 5469, 4463, 5495, 5469, 6490,
  2283, 3407, 3363, 4455, 3425, 4498, 4455, 5508, 3363, 4436, 4416, 5469, 4454, 5527, 5469, 6522,
  3438, 4502, 4455, 5508, 4502, 5566, 5508, 6561, 4463, 5516, 5469, 6522, 5516, 6548, 6522, 7543,
  2251, 3375, 3363, 4455, 3406, 4503, 4455, 5508, 3363, 4436, 4416, 5469, 4454, 5527, 5469, 6522,
  3406, 4470, 4455, 5508, 4502, 5556, 5508, 6561, 4463, 5516, 5469, 6522, 5516, 6548, 6522, 7543,
  3379, 4503, 4416, 5508, 4521, 5588, 5508, 6561, 4416, 5489, 5437, 6490, 5507, 6574, 6490, 7543,
  4523, 5587, 5508, 6561, 5587, 6641, 6561, 7614, 5516, 6569, 6490, 7543, 6569, 7595, 7543, 8564
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup10 (s : Nat) : ℤ := (if s < 128 then (if s < 64 then (if s < 32 then (if s < 16 then (if s < 8 then (if s < 4 then (if s < 2 then (if s < 1 then 0 else 1155) else (if s < 3 then 1155 else 2310)) else (if s < 6 then (if s < 5 then 1155 else 2283) else (if s < 7 then 2310 else 3363))) else (if s < 12 then (if s < 10 then (if s < 9 then 1155 else 2283) else (if s < 11 then 2310 else 3363)) else (if s < 14 then (if s < 13 then 2267 else 3395) else (if s < 15 then 3363 else 4416)))) else (if s < 24 then (if s < 20 then (if s < 18 then (if s < 17 then 1155 else 2283) else (if s < 19 then 2310 else 3363)) else (if s < 22 then (if s < 21 then 2251 else 3379) else (if s < 23 then 3363 else 4416))) else (if s < 28 then (if s < 26 then (if s < 25 then 2310 else 3363) else (if s < 27 then 3363 else 4416)) else (if s < 30 then (if s < 29 then 3363 else 4416) else (if s < 31 then 4416 else 5437))))) else (if s < 48 then (if s < 40 then (if s < 36 then (if s < 34 then (if s < 33 then 1155 else 2310) else (if s < 35 then 2310 else 3402)) else (if s < 38 then (if s < 37 then 2310 else 3420) else (if s < 39 then 3402 else 4455))) else (if s < 44 then (if s < 42 then (if s < 41 then 2283 else 3383) else (if s < 43 then 3363 else 4416)) else (if s < 46 then (if s < 45 then 3395 else 4474) else (if s < 47 then 4416 else 5469)))) else (if s < 56 then (if s < 52 then (if s < 50 then (if s < 49 then 2310 else 3405) else (if s < 51 then 3402 else 4455)) else (if s < 54 then (if s < 53 then 3406 else 4488) else (if s < 55 then 4455 else 5508))) else (if s < 60 then (if s < 58 then (if s < 57 then 3410 else 4463) else (if s < 59 then 4416 else 5469)) else (if s < 62 then (if s < 61 then 4463 else 5495) else (if s < 63 then 5469 else 6490)))))) else (if s < 96 then (if s < 80 then (if s < 72 then (if s < 68 then (if s < 66 then (if s < 65 then 1155 else 2297) else (if s < 67 then 2310 else 3402)) else (if s < 70 then (if s < 69 then 2310 else 3425) else (if s < 71 then 3402 else 4455))) else (if s < 76 then (if s < 74 then (if s < 73 then 2267 else 3368) else (if s < 75 then 3363 else 4416)) else (if s < 78 then (if s < 77 then 3373 else 4474) else (if s < 79 then 4416 else 5469)))) else (if s < 88 then (if s < 84 then (if s < 82 then (if s < 81 then 2310 else 3402) else (if s < 83 then 3402 else 4455)) else (if s < 86 then (if s < 85 then 3406 else 4488) else (if s < 87 then 4455 else 5508))) else (if s < 92 then (if s < 90 then (if s < 89 then 3395 else 4448) else (if s < 91 then 4416 else 5469)) else (if s < 94 then (if s < 93 then 4448 else 5495) else (if s < 95 then 5469 else 6490))))) else (if s < 112 then (if s < 104 then (if s < 100 then (if s < 98 then (if s < 97 then 2283 else 3425) else (if s < 99 then 3363 else 4455)) else (if s < 102 then (if s < 101 then 3425 else 4535) else (if s < 103 then 4455 else 5508))) else (if s < 108 then (if s < 106 then (if s < 105 then 3395 else 4468) else (if s < 107 then 4416 else 5469)) else (if s < 110 then (if s < 109 then 4486 else 5553) else (if s < 111 then 5469 else 6522)))) else (if s < 120 then (if s < 116 then (if s < 114 then (if s < 113 then 3438 else 4520) else (if s < 115 then 4455 else 5508)) else (if s < 118 then (if s < 117 then 4506 else 5588) else (if s < 119 then 5508 else 6561))) else (if s < 124 then (if s < 122 then (if s < 121 then 4495 else 5548) else (if s < 123 then 5469 else 6522)) else (if s < 126 then (if s < 125 then 5548 else 6574) else (if s < 127 then 6522 else 7543))))))) else (if s < 192 then (if s < 160 then (if s < 144 then (if s < 136 then (if s < 132 then (if s < 130 then (if s < 129 then 1155 else 2279) else (if s < 131 then 2310 else 3402)) else (if s < 134 then (if s < 133 then 2310 else 3407) else (if s < 135 then 3402 else 4455))) else (if s < 140 then (if s < 138 then (if s < 137 then 2310 else 3383) else (if s < 139 then 3363 else 4416)) else (if s < 142 then (if s < 141 then 3401 else 4474) else (if s < 143 then 4416 else 5469)))) else (if s < 152 then (if s < 148 then (if s < 146 then (if s < 145 then 2310 else 3385) else (if s < 147 then 3402 else 4455)) else (if s < 150 then (if s < 149 then 3406 else 4481) else (if s < 151 then 4455 else 5508))) else (if s < 156 then (if s < 154 then (if s < 153 then 3410 else 4463) else (if s < 155 then 4416 else 5469)) else (if s < 158 then (if s < 157 then 4463 else 5495) else (if s < 159 then 5469 else 6490))))) else (if s < 176 then (if s < 168 then (if s < 164 then (if s < 162 then (if s < 161 then 2283 else 3407) else (if s < 163 then 3363 else 4455)) else (if s < 166 then (if s < 165 then 3425 else 4498) else (if s < 167 then 4455 else 5508))) else (if s < 172 then (if s < 170 then (if s < 169 then 3363 else 4436) else (if s < 171 then 4416 else 5469)) else (if s < 174 then (if s < 173 then 4454 else 5527) else (if s < 175 then 5469 else 6522)))) else (if s < 184 then (if s < 180 then (if s < 178 then (if s < 177 then 3438 else 4502) else (if s < 179 then 4455 else 5508)) else (if s < 182 then (if s < 181 then 4502 else 5566) else (if s < 183 then 5508 else 6561))) else (if s < 188 then (if s < 186 then (if s < 185 then 4463 else 5516) else (if s < 187 then 5469 else 6522)) else (if s < 190 then (if s < 189 then 5516 else 6548) else (if s < 191 then 6522 else 7543)))))) else (if s < 224 then (if s < 208 then (if s < 200 then (if s < 196 then (if s < 194 then (if s < 193 then 2251 else 3375) else (if s < 195 then 3363 else 4455)) else (if s < 198 then (if s < 197 then 3406 else 4503) else (if s < 199 then 4455 else 5508))) else (if s < 204 then (if s < 202 then (if s < 201 then 3363 else 4436) else (if s < 203 then 4416 else 5469)) else (if s < 206 then (if s < 205 then 4454 else 5527) else (if s < 207 then 5469 else 6522)))) else (if s < 216 then (if s < 212 then (if s < 210 then (if s < 209 then 3406 else 4470) else (if s < 211 then 4455 else 5508)) else (if s < 214 then (if s < 213 then 4502 else 5556) else (if s < 215 then 5508 else 6561))) else (if s < 220 then (if s < 218 then (if s < 217 then 4463 else 5516) else (if s < 219 then 5469 else 6522)) else (if s < 222 then (if s < 221 then 5516 else 6548) else (if s < 223 then 6522 else 7543))))) else (if s < 240 then (if s < 232 then (if s < 228 then (if s < 226 then (if s < 225 then 3379 else 4503) else (if s < 227 then 4416 else 5508)) else (if s < 230 then (if s < 229 then 4521 else 5588) else (if s < 231 then 5508 else 6561))) else (if s < 236 then (if s < 234 then (if s < 233 then 4416 else 5489) else (if s < 235 then 5437 else 6490)) else (if s < 238 then (if s < 237 then 5507 else 6574) else (if s < 239 then 6490 else 7543)))) else (if s < 248 then (if s < 244 then (if s < 242 then (if s < 241 then 4523 else 5587) else (if s < 243 then 5508 else 6561)) else (if s < 246 then (if s < 245 then 5587 else 6641) else (if s < 247 then 6561 else 7614))) else (if s < 252 then (if s < 250 then (if s < 249 then 5516 else 6569) else (if s < 251 then 6490 else 7543)) else (if s < 254 then (if s < 253 then 6569 else 7595) else (if s < 255 then 7543 else 8564))))))))
def witness10 (S : Mask (groundSize 10)) : ℤ := lookup10 S.val

theorem witness10_table : ∀ S : Mask (groundSize 10),
    witness10 S = table10[S.val]! := by decide +kernel

theorem witness10_local_mono : MaskLocalMono witness10 := by
  unfold MaskLocalMono
  decide +kernel

theorem witness10_local_squares : MaskLocalSquares witness10 := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness10_pm : PMInt (groundSize 10) witness10 :=
  PMInt.of_local encoding_ok_8 (by decide +kernel)
    witness10_local_mono witness10_local_squares

theorem witness10_first : MatchesInt (fun S => witness10 (origMask 10 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness10_second : MatchesInt (fun S => witness10 (copyMask 10 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness10_adhesive : AdhesiveInt 10 witness10 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_10 : ∃ g : Mask (groundSize 10) → ℝ,
    PM (groundSize 10) g ∧ Matches (firstRestrict 10 g) ∧
    Matches (secondRestrict 10 g) ∧ Adhesive 10 g :=
  positive_of_int 10 witness10 witness10_pm witness10_first witness10_second witness10_adhesive

#print axioms witness10_pm
end InfoE3
