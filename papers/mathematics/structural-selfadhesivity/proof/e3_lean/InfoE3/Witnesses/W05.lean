import InfoE3.PositiveBase
import InfoE3.LocalPM

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace InfoE3

def table05 : Array ℤ := #[
  0, 1155, 1155, 2310, 1155, 2306, 2310, 3445, 1155, 2306, 2310, 3445, 2302, 3453, 3445, 4580,
  1155, 2306, 2310, 3445, 2298, 3449, 3445, 4580, 2310, 3445, 3445, 4580, 3445, 4580, 4580, 5707,
  1155, 2310, 2310, 3454, 2310, 3445, 3457, 4584, 2310, 3457, 3457, 4589, 3457, 4592, 4592, 5719,
  2310, 3455, 3457, 4589, 3453, 4588, 4592, 5719, 3454, 4589, 4589, 5721, 4589, 5719, 5724, 6846,
  1155, 2306, 2310, 3457, 2302, 3453, 3457, 4592, 2306, 3457, 3457, 4592, 3449, 4600, 4592, 5727,
  2306, 3457, 3457, 4592, 3445, 4596, 4592, 5727, 3457, 4592, 4592, 5727, 4592, 5727, 5727, 6854,
  2310, 3445, 3457, 4589, 3445, 4580, 4592, 5719, 3457, 4592, 4594, 5724, 4592, 5727, 5727, 6854,
  3455, 4590, 4594, 5724, 4588, 5723, 5727, 6854, 4591, 5724, 5726, 6856, 5724, 6854, 6859, 7981,
  1155, 2306, 2310, 3455, 2298, 3449, 3453, 4588, 2306, 3457, 3455, 4590, 3445, 4596, 4588, 5723,
  2305, 3456, 3455, 4590, 3441, 4592, 4588, 5723, 3455, 4590, 4590, 5723, 4588, 5723, 5723, 6850,
  2310, 3445, 3457, 4589, 3445, 4580, 4592, 5719, 3457, 4592, 4594, 5724, 4592, 5727, 5727, 6854,
  3455, 4590, 4594, 5724, 4588, 5723, 5727, 6854, 4591, 5724, 5726, 6856, 5724, 6854, 6859, 7981,
  2310, 3445, 3454, 4589, 3445, 4580, 4589, 5719, 3457, 4592, 4591, 5724, 4592, 5727, 5724, 6854,
  3455, 4590, 4591, 5724, 4588, 5723, 5724, 6854, 4589, 5724, 5721, 6854, 5722, 6854, 6854, 7981,
  3445, 4580, 4589, 5719, 4580, 5707, 5724, 6846, 4592, 5727, 5726, 6854, 5727, 6854, 6859, 7981,
  4590, 5723, 5726, 6854, 5723, 6850, 6859, 7981, 5723, 6856, 6855, 7983, 6854, 7981, 7986, 9108
]

/-- Balanced literal lookup of the exact integer certificate. -/
def lookup05 (s : Nat) : ℤ := (if s < 128 then (if s < 64 then (if s < 32 then (if s < 16 then (if s < 8 then (if s < 4 then (if s < 2 then (if s < 1 then 0 else 1155) else (if s < 3 then 1155 else 2310)) else (if s < 6 then (if s < 5 then 1155 else 2306) else (if s < 7 then 2310 else 3445))) else (if s < 12 then (if s < 10 then (if s < 9 then 1155 else 2306) else (if s < 11 then 2310 else 3445)) else (if s < 14 then (if s < 13 then 2302 else 3453) else (if s < 15 then 3445 else 4580)))) else (if s < 24 then (if s < 20 then (if s < 18 then (if s < 17 then 1155 else 2306) else (if s < 19 then 2310 else 3445)) else (if s < 22 then (if s < 21 then 2298 else 3449) else (if s < 23 then 3445 else 4580))) else (if s < 28 then (if s < 26 then (if s < 25 then 2310 else 3445) else (if s < 27 then 3445 else 4580)) else (if s < 30 then (if s < 29 then 3445 else 4580) else (if s < 31 then 4580 else 5707))))) else (if s < 48 then (if s < 40 then (if s < 36 then (if s < 34 then (if s < 33 then 1155 else 2310) else (if s < 35 then 2310 else 3454)) else (if s < 38 then (if s < 37 then 2310 else 3445) else (if s < 39 then 3457 else 4584))) else (if s < 44 then (if s < 42 then (if s < 41 then 2310 else 3457) else (if s < 43 then 3457 else 4589)) else (if s < 46 then (if s < 45 then 3457 else 4592) else (if s < 47 then 4592 else 5719)))) else (if s < 56 then (if s < 52 then (if s < 50 then (if s < 49 then 2310 else 3455) else (if s < 51 then 3457 else 4589)) else (if s < 54 then (if s < 53 then 3453 else 4588) else (if s < 55 then 4592 else 5719))) else (if s < 60 then (if s < 58 then (if s < 57 then 3454 else 4589) else (if s < 59 then 4589 else 5721)) else (if s < 62 then (if s < 61 then 4589 else 5719) else (if s < 63 then 5724 else 6846)))))) else (if s < 96 then (if s < 80 then (if s < 72 then (if s < 68 then (if s < 66 then (if s < 65 then 1155 else 2306) else (if s < 67 then 2310 else 3457)) else (if s < 70 then (if s < 69 then 2302 else 3453) else (if s < 71 then 3457 else 4592))) else (if s < 76 then (if s < 74 then (if s < 73 then 2306 else 3457) else (if s < 75 then 3457 else 4592)) else (if s < 78 then (if s < 77 then 3449 else 4600) else (if s < 79 then 4592 else 5727)))) else (if s < 88 then (if s < 84 then (if s < 82 then (if s < 81 then 2306 else 3457) else (if s < 83 then 3457 else 4592)) else (if s < 86 then (if s < 85 then 3445 else 4596) else (if s < 87 then 4592 else 5727))) else (if s < 92 then (if s < 90 then (if s < 89 then 3457 else 4592) else (if s < 91 then 4592 else 5727)) else (if s < 94 then (if s < 93 then 4592 else 5727) else (if s < 95 then 5727 else 6854))))) else (if s < 112 then (if s < 104 then (if s < 100 then (if s < 98 then (if s < 97 then 2310 else 3445) else (if s < 99 then 3457 else 4589)) else (if s < 102 then (if s < 101 then 3445 else 4580) else (if s < 103 then 4592 else 5719))) else (if s < 108 then (if s < 106 then (if s < 105 then 3457 else 4592) else (if s < 107 then 4594 else 5724)) else (if s < 110 then (if s < 109 then 4592 else 5727) else (if s < 111 then 5727 else 6854)))) else (if s < 120 then (if s < 116 then (if s < 114 then (if s < 113 then 3455 else 4590) else (if s < 115 then 4594 else 5724)) else (if s < 118 then (if s < 117 then 4588 else 5723) else (if s < 119 then 5727 else 6854))) else (if s < 124 then (if s < 122 then (if s < 121 then 4591 else 5724) else (if s < 123 then 5726 else 6856)) else (if s < 126 then (if s < 125 then 5724 else 6854) else (if s < 127 then 6859 else 7981))))))) else (if s < 192 then (if s < 160 then (if s < 144 then (if s < 136 then (if s < 132 then (if s < 130 then (if s < 129 then 1155 else 2306) else (if s < 131 then 2310 else 3455)) else (if s < 134 then (if s < 133 then 2298 else 3449) else (if s < 135 then 3453 else 4588))) else (if s < 140 then (if s < 138 then (if s < 137 then 2306 else 3457) else (if s < 139 then 3455 else 4590)) else (if s < 142 then (if s < 141 then 3445 else 4596) else (if s < 143 then 4588 else 5723)))) else (if s < 152 then (if s < 148 then (if s < 146 then (if s < 145 then 2305 else 3456) else (if s < 147 then 3455 else 4590)) else (if s < 150 then (if s < 149 then 3441 else 4592) else (if s < 151 then 4588 else 5723))) else (if s < 156 then (if s < 154 then (if s < 153 then 3455 else 4590) else (if s < 155 then 4590 else 5723)) else (if s < 158 then (if s < 157 then 4588 else 5723) else (if s < 159 then 5723 else 6850))))) else (if s < 176 then (if s < 168 then (if s < 164 then (if s < 162 then (if s < 161 then 2310 else 3445) else (if s < 163 then 3457 else 4589)) else (if s < 166 then (if s < 165 then 3445 else 4580) else (if s < 167 then 4592 else 5719))) else (if s < 172 then (if s < 170 then (if s < 169 then 3457 else 4592) else (if s < 171 then 4594 else 5724)) else (if s < 174 then (if s < 173 then 4592 else 5727) else (if s < 175 then 5727 else 6854)))) else (if s < 184 then (if s < 180 then (if s < 178 then (if s < 177 then 3455 else 4590) else (if s < 179 then 4594 else 5724)) else (if s < 182 then (if s < 181 then 4588 else 5723) else (if s < 183 then 5727 else 6854))) else (if s < 188 then (if s < 186 then (if s < 185 then 4591 else 5724) else (if s < 187 then 5726 else 6856)) else (if s < 190 then (if s < 189 then 5724 else 6854) else (if s < 191 then 6859 else 7981)))))) else (if s < 224 then (if s < 208 then (if s < 200 then (if s < 196 then (if s < 194 then (if s < 193 then 2310 else 3445) else (if s < 195 then 3454 else 4589)) else (if s < 198 then (if s < 197 then 3445 else 4580) else (if s < 199 then 4589 else 5719))) else (if s < 204 then (if s < 202 then (if s < 201 then 3457 else 4592) else (if s < 203 then 4591 else 5724)) else (if s < 206 then (if s < 205 then 4592 else 5727) else (if s < 207 then 5724 else 6854)))) else (if s < 216 then (if s < 212 then (if s < 210 then (if s < 209 then 3455 else 4590) else (if s < 211 then 4591 else 5724)) else (if s < 214 then (if s < 213 then 4588 else 5723) else (if s < 215 then 5724 else 6854))) else (if s < 220 then (if s < 218 then (if s < 217 then 4589 else 5724) else (if s < 219 then 5721 else 6854)) else (if s < 222 then (if s < 221 then 5722 else 6854) else (if s < 223 then 6854 else 7981))))) else (if s < 240 then (if s < 232 then (if s < 228 then (if s < 226 then (if s < 225 then 3445 else 4580) else (if s < 227 then 4589 else 5719)) else (if s < 230 then (if s < 229 then 4580 else 5707) else (if s < 231 then 5724 else 6846))) else (if s < 236 then (if s < 234 then (if s < 233 then 4592 else 5727) else (if s < 235 then 5726 else 6854)) else (if s < 238 then (if s < 237 then 5727 else 6854) else (if s < 239 then 6859 else 7981)))) else (if s < 248 then (if s < 244 then (if s < 242 then (if s < 241 then 4590 else 5723) else (if s < 243 then 5726 else 6854)) else (if s < 246 then (if s < 245 then 5723 else 6850) else (if s < 247 then 6859 else 7981))) else (if s < 252 then (if s < 250 then (if s < 249 then 5723 else 6856) else (if s < 251 then 6855 else 7983)) else (if s < 254 then (if s < 253 then 6854 else 7981) else (if s < 255 then 7986 else 9108))))))))
def witness05 (S : Mask (groundSize 5)) : ℤ := lookup05 S.val

theorem witness05_table : ∀ S : Mask (groundSize 5),
    witness05 S = table05[S.val]! := by decide +kernel

theorem witness05_local_mono : MaskLocalMono witness05 := by
  unfold MaskLocalMono
  decide +kernel

theorem witness05_local_squares : MaskLocalSquares witness05 := by
  unfold MaskLocalSquares
  decide +kernel

theorem witness05_pm : PMInt (groundSize 5) witness05 :=
  PMInt.of_local encoding_ok_8 (by decide +kernel)
    witness05_local_mono witness05_local_squares

theorem witness05_first : MatchesInt (fun S => witness05 (origMask 5 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness05_second : MatchesInt (fun S => witness05 (copyMask 5 S)) := by
  unfold MatchesInt
  decide +kernel
theorem witness05_adhesive : AdhesiveInt 5 witness05 := by
  unfold AdhesiveInt
  decide +kernel

theorem structural_at_05 : ∃ g : Mask (groundSize 5) → ℝ,
    PM (groundSize 5) g ∧ Matches (firstRestrict 5 g) ∧
    Matches (secondRestrict 5 g) ∧ Adhesive 5 g :=
  positive_of_int 5 witness05 witness05_pm witness05_first witness05_second witness05_adhesive

#print axioms witness05_pm
end InfoE3
