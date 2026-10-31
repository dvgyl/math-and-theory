import SingerC3.Search

/-!
# Certificate part 11

Kernel-checked searches closing 21 of the partial assignments reached by the top search
(`SingerC3.Cert.top`). Each pair is `(o, z)`: orbit indices fixed to `true` and to `false`.
-/

namespace SingerC3.Cert

open SingerC3

theorem p11_00 : search 5368709121 2093137365219409920 = true := by decide +kernel
theorem p11_01 : search 171800788993 1993266148237377536 = true := by decide +kernel
theorem p11_02 : search 1125899915231233 2091923127566073856 = true := by decide +kernel
theorem p11_03 : search 1408474395181057 2245044414252580864 = true := by decide +kernel
theorem p11_04 : search 2251799822073857 1990872647847641088 = true := by decide +kernel
theorem p11_05 : search 9007199256838145 1984962636424445952 = true := by decide +kernel
theorem p11_06 : search 9007268041326593 2093049302283714560 = true := by decide +kernel
theorem p11_07 : search 72057594037960705 1748727133242392576 = true := by decide +kernel
theorem p11_08 : search 72057868915836929 1765606835752042496 = true := by decide +kernel
theorem p11_09 : search 72198331526283265 2180305444765958144 = true := by decide +kernel
theorem p11_10 : search 73183493944770817 1729578038733080576 = true := by decide +kernel
theorem p11_11 : search 288230378366304257 1813289288834482176 = true := by decide +kernel
theorem p11_12 : search 288231476200210433 1813288190396596224 = true := by decide +kernel
theorem p11_13 : search 576460752571858945 1679280089012895744 = true := by decide +kernel
theorem p11_14 : search 576460769500069889 1617356728276353024 = true := by decide +kernel
theorem p11_15 : search 577023736616583169 1641632432920723456 = true := by decide +kernel
theorem p11_16 : search 594476250324533249 1598777867716526080 = true := by decide +kernel
theorem p11_17 : search 612489824200294401 1612851616552058880 = true := by decide +kernel
theorem p11_18 : search 1161928703865782273 792658007140859904 = true := by decide +kernel
theorem p11_19 : search 1161928978739494913 792657723673018368 = true := by decide +kernel
theorem p11_20 : search 1224979115824644097 758293759057199104 = true := by decide +kernel

/-- The partial assignments closed in part 11. -/
def part11 : List (Nat × Nat) :=
  [(5368709121, 2093137365219409920),
   (171800788993, 1993266148237377536),
   (1125899915231233, 2091923127566073856),
   (1408474395181057, 2245044414252580864),
   (2251799822073857, 1990872647847641088),
   (9007199256838145, 1984962636424445952),
   (9007268041326593, 2093049302283714560),
   (72057594037960705, 1748727133242392576),
   (72057868915836929, 1765606835752042496),
   (72198331526283265, 2180305444765958144),
   (73183493944770817, 1729578038733080576),
   (288230378366304257, 1813289288834482176),
   (288231476200210433, 1813288190396596224),
   (576460752571858945, 1679280089012895744),
   (576460769500069889, 1617356728276353024),
   (577023736616583169, 1641632432920723456),
   (594476250324533249, 1598777867716526080),
   (612489824200294401, 1612851616552058880),
   (1161928703865782273, 792658007140859904),
   (1161928978739494913, 792657723673018368),
   (1224979115824644097, 758293759057199104)]

theorem part11_ok : AllNoSol part11 :=
  ⟨search_sound p11_00,
   search_sound p11_01,
   search_sound p11_02,
   search_sound p11_03,
   search_sound p11_04,
   search_sound p11_05,
   search_sound p11_06,
   search_sound p11_07,
   search_sound p11_08,
   search_sound p11_09,
   search_sound p11_10,
   search_sound p11_11,
   search_sound p11_12,
   search_sound p11_13,
   search_sound p11_14,
   search_sound p11_15,
   search_sound p11_16,
   search_sound p11_17,
   search_sound p11_18,
   search_sound p11_19,
   search_sound p11_20, trivial⟩

end SingerC3.Cert
