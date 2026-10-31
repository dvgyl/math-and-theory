import SingerC3.Search

/-!
# Certificate part 0

Kernel-checked searches closing 21 of the partial assignments reached by the top search
(`SingerC3.Cert.top`). Each pair is `(o, z)`: orbit indices fixed to `true` and to `false`.
-/

namespace SingerC3.Cert

open SingerC3

theorem p00_00 : search 3 2254615939278987264 = true := by decide +kernel
theorem p00_01 : search 2359297 1957096751304278016 = true := by decide +kernel
theorem p00_02 : search 268435459 2254615938993774592 = true := by decide +kernel
theorem p00_03 : search 268451841 2254615938993750016 = true := by decide +kernel
theorem p00_04 : search 1099645845505 2093048309072527360 = true := by decide +kernel
theorem p00_05 : search 564324342956033 2102055126075179008 = true := by decide +kernel
theorem p00_06 : search 1125899990728705 2092019918881947648 = true := by decide +kernel
theorem p00_07 : search 18015566740586497 2237163389782589440 = true := by decide +kernel
theorem p00_08 : search 72057594037928193 1730703938639923200 = true := by decide +kernel
theorem p00_09 : search 72092778410018817 1730948511492751360 = true := by decide +kernel
theorem p00_10 : search 180143985094819843 2091923127577108480 = true := by decide +kernel
theorem p00_11 : search 216174981137039361 1765604567975723008 = true := by decide +kernel
theorem p00_12 : search 288230376151728129 1803692751425372160 = true := by decide +kernel
theorem p00_13 : search 288230377359671297 1957096750019772416 = true := by decide +kernel
theorem p00_14 : search 288247968404865025 1813262900555415552 = true := by decide +kernel
theorem p00_15 : search 432345564228091905 1803692751424847872 = true := by decide +kernel
theorem p00_16 : search 576460752320200705 1617356745456222208 = true := by decide +kernel
theorem p00_17 : search 594475288251858945 1598779242106060800 = true := by decide +kernel
theorem p00_18 : search 1152921504606849025 801922346231595008 = true := by decide +kernel
theorem p00_19 : search 1297107061426880513 864691128455151616 = true := by decide +kernel
theorem p00_20 : search 1729382256910270465 400961173115109376 = true := by decide +kernel

/-- The partial assignments closed in part 0. -/
def part00 : List (Nat × Nat) :=
  [(3, 2254615939278987264),
   (2359297, 1957096751304278016),
   (268435459, 2254615938993774592),
   (268451841, 2254615938993750016),
   (1099645845505, 2093048309072527360),
   (564324342956033, 2102055126075179008),
   (1125899990728705, 2092019918881947648),
   (18015566740586497, 2237163389782589440),
   (72057594037928193, 1730703938639923200),
   (72092778410018817, 1730948511492751360),
   (180143985094819843, 2091923127577108480),
   (216174981137039361, 1765604567975723008),
   (288230376151728129, 1803692751425372160),
   (288230377359671297, 1957096750019772416),
   (288247968404865025, 1813262900555415552),
   (432345564228091905, 1803692751424847872),
   (576460752320200705, 1617356745456222208),
   (594475288251858945, 1598779242106060800),
   (1152921504606849025, 801922346231595008),
   (1297107061426880513, 864691128455151616),
   (1729382256910270465, 400961173115109376)]

theorem part00_ok : AllNoSol part00 :=
  ⟨search_sound p00_00,
   search_sound p00_01,
   search_sound p00_02,
   search_sound p00_03,
   search_sound p00_04,
   search_sound p00_05,
   search_sound p00_06,
   search_sound p00_07,
   search_sound p00_08,
   search_sound p00_09,
   search_sound p00_10,
   search_sound p00_11,
   search_sound p00_12,
   search_sound p00_13,
   search_sound p00_14,
   search_sound p00_15,
   search_sound p00_16,
   search_sound p00_17,
   search_sound p00_18,
   search_sound p00_19,
   search_sound p00_20, trivial⟩

end SingerC3.Cert
