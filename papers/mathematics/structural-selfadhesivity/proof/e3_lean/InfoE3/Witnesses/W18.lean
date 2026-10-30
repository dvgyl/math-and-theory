import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table18 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2267, 2310, 3292, 1155, 2267, 2310, 3292, 2238, 3350, 3292, 4274,
  1155, 2267, 2310, 3292, 2209, 3321, 3292, 4274, 2310, 3292, 3292, 4274, 3292, 4274, 4274, 5198,
  1155, 2310, 2310, 3307, 2310, 3345, 3307, 4289, 2310, 3322, 3307, 4289, 3335, 4347, 4289, 5271,
  2267, 3310, 3292, 4274, 3292, 4327, 4274, 5256, 3328, 4310, 4274, 5256, 4310, 5271, 5256, 6180,
  1155, 2310, 2310, 3307, 2281, 3336, 3307, 4289, 2265, 3321, 3307, 4289, 3319, 4347, 4289, 5271,
  2209, 3319, 3292, 4274, 3263, 4318, 4274, 5256, 3319, 4301, 4274, 5256, 4301, 5271, 5256, 6180,
  2267, 3337, 3292, 4289, 3327, 4342, 4289, 5271, 3347, 4339, 4289, 5271, 4352, 5344, 5271, 6253,
  3321, 4337, 4274, 5256, 4309, 5319, 5256, 6238, 4337, 5319, 5256, 6238, 5319, 6263, 6238, 7162,
  1155, 2298, 2310, 3307, 2269, 3345, 3307, 4289, 2188, 3300, 3307, 4289, 3271, 4347, 4289, 5271,
  2310, 3328, 3292, 4274, 3323, 4327, 4274, 5256, 3328, 4310, 4274, 5256, 4310, 5271, 5256, 6180,
  2267, 3310, 3292, 4289, 3323, 4327, 4289, 5271, 3300, 4312, 4289, 5271, 4325, 5329, 5271, 6253,
  3292, 4310, 4274, 5256, 4305, 5309, 5256, 6238, 4310, 5292, 5256, 6238, 5292, 6253, 6238, 7162,
  2238, 3325, 3292, 4289, 3323, 4342, 4289, 5271, 3256, 4312, 4289, 5271, 4310, 5329, 5271, 6253,
  3292, 4310, 4274, 5256, 4305, 5309, 5256, 6238, 4310, 5292, 5256, 6238, 5292, 6253, 6238, 7162,
  3350, 4337, 4274, 5261, 4337, 5324, 5261, 6243, 4337, 5324, 5261, 6243, 5324, 6268, 6243, 7177,
  4274, 5261, 5198, 6180, 5256, 6243, 6180, 7162, 5261, 6243, 6180, 7162, 6243, 7187, 7162, 8086
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup18 (s : Nat) : ℤ := (if s < 128 then (if s < 64 then (if s < 32 then (if s < 16 then (if s < 8 then (if s < 4 then (if s < 2 then (if s < 1 then 0 else 1155) else (if s < 3 then 1155 else 2310)) else (if s < 6 then (if s < 5 then 1155 else 2267) else (if s < 7 then 2310 else 3292))) else (if s < 12 then (if s < 10 then (if s < 9 then 1155 else 2267) else (if s < 11 then 2310 else 3292)) else (if s < 14 then (if s < 13 then 2238 else 3350) else (if s < 15 then 3292 else 4274)))) else (if s < 24 then (if s < 20 then (if s < 18 then (if s < 17 then 1155 else 2267) else (if s < 19 then 2310 else 3292)) else (if s < 22 then (if s < 21 then 2209 else 3321) else (if s < 23 then 3292 else 4274))) else (if s < 28 then (if s < 26 then (if s < 25 then 2310 else 3292) else (if s < 27 then 3292 else 4274)) else (if s < 30 then (if s < 29 then 3292 else 4274) else (if s < 31 then 4274 else 5198))))) else (if s < 48 then (if s < 40 then (if s < 36 then (if s < 34 then (if s < 33 then 1155 else 2310) else (if s < 35 then 2310 else 3307)) else (if s < 38 then (if s < 37 then 2310 else 3345) else (if s < 39 then 3307 else 4289))) else (if s < 44 then (if s < 42 then (if s < 41 then 2310 else 3322) else (if s < 43 then 3307 else 4289)) else (if s < 46 then (if s < 45 then 3335 else 4347) else (if s < 47 then 4289 else 5271)))) else (if s < 56 then (if s < 52 then (if s < 50 then (if s < 49 then 2267 else 3310) else (if s < 51 then 3292 else 4274)) else (if s < 54 then (if s < 53 then 3292 else 4327) else (if s < 55 then 4274 else 5256))) else (if s < 60 then (if s < 58 then (if s < 57 then 3328 else 4310) else (if s < 59 then 4274 else 5256)) else (if s < 62 then (if s < 61 then 4310 else 5271) else (if s < 63 then 5256 else 6180)))))) else (if s < 96 then (if s < 80 then (if s < 72 then (if s < 68 then (if s < 66 then (if s < 65 then 1155 else 2310) else (if s < 67 then 2310 else 3307)) else (if s < 70 then (if s < 69 then 2281 else 3336) else (if s < 71 then 3307 else 4289))) else (if s < 76 then (if s < 74 then (if s < 73 then 2265 else 3321) else (if s < 75 then 3307 else 4289)) else (if s < 78 then (if s < 77 then 3319 else 4347) else (if s < 79 then 4289 else 5271)))) else (if s < 88 then (if s < 84 then (if s < 82 then (if s < 81 then 2209 else 3319) else (if s < 83 then 3292 else 4274)) else (if s < 86 then (if s < 85 then 3263 else 4318) else (if s < 87 then 4274 else 5256))) else (if s < 92 then (if s < 90 then (if s < 89 then 3319 else 4301) else (if s < 91 then 4274 else 5256)) else (if s < 94 then (if s < 93 then 4301 else 5271) else (if s < 95 then 5256 else 6180))))) else (if s < 112 then (if s < 104 then (if s < 100 then (if s < 98 then (if s < 97 then 2267 else 3337) else (if s < 99 then 3292 else 4289)) else (if s < 102 then (if s < 101 then 3327 else 4342) else (if s < 103 then 4289 else 5271))) else (if s < 108 then (if s < 106 then (if s < 105 then 3347 else 4339) else (if s < 107 then 4289 else 5271)) else (if s < 110 then (if s < 109 then 4352 else 5344) else (if s < 111 then 5271 else 6253)))) else (if s < 120 then (if s < 116 then (if s < 114 then (if s < 113 then 3321 else 4337) else (if s < 115 then 4274 else 5256)) else (if s < 118 then (if s < 117 then 4309 else 5319) else (if s < 119 then 5256 else 6238))) else (if s < 124 then (if s < 122 then (if s < 121 then 4337 else 5319) else (if s < 123 then 5256 else 6238)) else (if s < 126 then (if s < 125 then 5319 else 6263) else (if s < 127 then 6238 else 7162))))))) else (if s < 192 then (if s < 160 then (if s < 144 then (if s < 136 then (if s < 132 then (if s < 130 then (if s < 129 then 1155 else 2298) else (if s < 131 then 2310 else 3307)) else (if s < 134 then (if s < 133 then 2269 else 3345) else (if s < 135 then 3307 else 4289))) else (if s < 140 then (if s < 138 then (if s < 137 then 2188 else 3300) else (if s < 139 then 3307 else 4289)) else (if s < 142 then (if s < 141 then 3271 else 4347) else (if s < 143 then 4289 else 5271)))) else (if s < 152 then (if s < 148 then (if s < 146 then (if s < 145 then 2310 else 3328) else (if s < 147 then 3292 else 4274)) else (if s < 150 then (if s < 149 then 3323 else 4327) else (if s < 151 then 4274 else 5256))) else (if s < 156 then (if s < 154 then (if s < 153 then 3328 else 4310) else (if s < 155 then 4274 else 5256)) else (if s < 158 then (if s < 157 then 4310 else 5271) else (if s < 159 then 5256 else 6180))))) else (if s < 176 then (if s < 168 then (if s < 164 then (if s < 162 then (if s < 161 then 2267 else 3310) else (if s < 163 then 3292 else 4289)) else (if s < 166 then (if s < 165 then 3323 else 4327) else (if s < 167 then 4289 else 5271))) else (if s < 172 then (if s < 170 then (if s < 169 then 3300 else 4312) else (if s < 171 then 4289 else 5271)) else (if s < 174 then (if s < 173 then 4325 else 5329) else (if s < 175 then 5271 else 6253)))) else (if s < 184 then (if s < 180 then (if s < 178 then (if s < 177 then 3292 else 4310) else (if s < 179 then 4274 else 5256)) else (if s < 182 then (if s < 181 then 4305 else 5309) else (if s < 183 then 5256 else 6238))) else (if s < 188 then (if s < 186 then (if s < 185 then 4310 else 5292) else (if s < 187 then 5256 else 6238)) else (if s < 190 then (if s < 189 then 5292 else 6253) else (if s < 191 then 6238 else 7162)))))) else (if s < 224 then (if s < 208 then (if s < 200 then (if s < 196 then (if s < 194 then (if s < 193 then 2238 else 3325) else (if s < 195 then 3292 else 4289)) else (if s < 198 then (if s < 197 then 3323 else 4342) else (if s < 199 then 4289 else 5271))) else (if s < 204 then (if s < 202 then (if s < 201 then 3256 else 4312) else (if s < 203 then 4289 else 5271)) else (if s < 206 then (if s < 205 then 4310 else 5329) else (if s < 207 then 5271 else 6253)))) else (if s < 216 then (if s < 212 then (if s < 210 then (if s < 209 then 3292 else 4310) else (if s < 211 then 4274 else 5256)) else (if s < 214 then (if s < 213 then 4305 else 5309) else (if s < 215 then 5256 else 6238))) else (if s < 220 then (if s < 218 then (if s < 217 then 4310 else 5292) else (if s < 219 then 5256 else 6238)) else (if s < 222 then (if s < 221 then 5292 else 6253) else (if s < 223 then 6238 else 7162))))) else (if s < 240 then (if s < 232 then (if s < 228 then (if s < 226 then (if s < 225 then 3350 else 4337) else (if s < 227 then 4274 else 5261)) else (if s < 230 then (if s < 229 then 4337 else 5324) else (if s < 231 then 5261 else 6243))) else (if s < 236 then (if s < 234 then (if s < 233 then 4337 else 5324) else (if s < 235 then 5261 else 6243)) else (if s < 238 then (if s < 237 then 5324 else 6268) else (if s < 239 then 6243 else 7177)))) else (if s < 248 then (if s < 244 then (if s < 242 then (if s < 241 then 4274 else 5261) else (if s < 243 then 5198 else 6180)) else (if s < 246 then (if s < 245 then 5256 else 6243) else (if s < 247 then 6180 else 7162))) else (if s < 252 then (if s < 250 then (if s < 249 then 5261 else 6243) else (if s < 251 then 6180 else 7162)) else (if s < 254 then (if s < 253 then 6243 else 7187) else (if s < 255 then 7162 else 8086))))))))
def witness18 (S : Mask (groundSize 18)) : ℤ := lookup18 S.val

theorem witness18_table : ∀ S : Mask (groundSize 18),
    witness18 S = table18[S.val]! := by decide +kernel

theorem witness18_local_mono : MaskLocalMono witness18 := by
  unfold MaskLocalMono
  decide +kernel

theorem witness18_local_squares : MaskLocalSquares witness18 := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness18_pm : PMInt (groundSize 18) witness18 :=
  PMInt.of_local encoding_ok_8 (by decide +kernel)
    witness18_local_mono witness18_local_squares

theorem witness18_first : MatchesInt (fun S => witness18 (origMask 18 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness18_second : MatchesInt (fun S => witness18 (copyMask 18 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness18_adhesive : AdhesiveInt 18 witness18 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_18 : ∃ g : Mask (groundSize 18) → ℝ,
    PM (groundSize 18) g ∧ Matches (firstRestrict 18 g) ∧
    Matches (secondRestrict 18 g) ∧ Adhesive 18 g :=
  positive_of_int 18 witness18 witness18_pm witness18_first witness18_second witness18_adhesive

#print axioms witness18_pm
end InfoE3
