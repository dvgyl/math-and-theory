import SingerC3.Search

/-!
# Certificate part 13

Kernel-checked searches closing 21 of the partial assignments reached by the top search
(`SingerC3.Cert.top`). Each pair is `(o, z)`: orbit indices fixed to `true` and to `false`.
-/

namespace SingerC3.Cert

open SingerC3

theorem p13_00 : search 8388609 2093049409859289088 = true := by decide +kernel
theorem p13_01 : search 67108929 2093049409792180224 = true := by decide +kernel
theorem p13_02 : search 137441050625 1993266182597115904 = true := by decide +kernel
theorem p13_03 : search 1099511693313 2273192311481434112 = true := by decide +kernel
theorem p13_04 : search 563225905070081 2102056225586806784 = true := by decide +kernel
theorem p13_05 : search 1125935340322817 2092019883448467456 = true := by decide +kernel
theorem p13_06 : search 2251799814733825 2247577843796017152 = true := by decide +kernel
theorem p13_07 : search 2533274807173121 2261370238039752704 = true := by decide +kernel
theorem p13_08 : search 9007233681588225 2093049371003453440 = true := by decide +kernel
theorem p13_09 : search 11259273946333185 2252362763638669312 = true := by decide +kernel
theorem p13_10 : search 38280596841037825 1954843850828677120 = true := by decide +kernel
theorem p13_11 : search 72057594079870977 1734371943756333056 = true := by decide +kernel
theorem p13_12 : search 72066390130982913 1748718337149370368 = true := by decide +kernel
theorem p13_13 : search 144115188076380161 2093049302361309184 = true := by decide +kernel
theorem p13_14 : search 144116287587549185 2093048326386614272 = true := by decide +kernel
theorem p13_15 : search 299489375220137985 1945555039024054272 = true := by decide +kernel
theorem p13_16 : search 576460752305520641 1617356590854176768 = true := by decide +kernel
theorem p13_17 : search 576460889759154177 1617356590837399552 = true := by decide +kernel
theorem p13_18 : search 577023702258941953 1641632467314016256 = true := by decide +kernel
theorem p13_19 : search 1152921504606912513 801922346231529472 = true := by decide +kernel
theorem p13_20 : search 1261007895663738881 720575940379279360 = true := by decide +kernel

/-- The partial assignments closed in part 13. -/
def part13 : List (Nat × Nat) :=
  [(8388609, 2093049409859289088),
   (67108929, 2093049409792180224),
   (137441050625, 1993266182597115904),
   (1099511693313, 2273192311481434112),
   (563225905070081, 2102056225586806784),
   (1125935340322817, 2092019883448467456),
   (2251799814733825, 2247577843796017152),
   (2533274807173121, 2261370238039752704),
   (9007233681588225, 2093049371003453440),
   (11259273946333185, 2252362763638669312),
   (38280596841037825, 1954843850828677120),
   (72057594079870977, 1734371943756333056),
   (72066390130982913, 1748718337149370368),
   (144115188076380161, 2093049302361309184),
   (144116287587549185, 2093048326386614272),
   (299489375220137985, 1945555039024054272),
   (576460752305520641, 1617356590854176768),
   (576460889759154177, 1617356590837399552),
   (577023702258941953, 1641632467314016256),
   (1152921504606912513, 801922346231529472),
   (1261007895663738881, 720575940379279360)]

theorem part13_ok : AllNoSol part13 :=
  ⟨search_sound p13_00,
   search_sound p13_01,
   search_sound p13_02,
   search_sound p13_03,
   search_sound p13_04,
   search_sound p13_05,
   search_sound p13_06,
   search_sound p13_07,
   search_sound p13_08,
   search_sound p13_09,
   search_sound p13_10,
   search_sound p13_11,
   search_sound p13_12,
   search_sound p13_13,
   search_sound p13_14,
   search_sound p13_15,
   search_sound p13_16,
   search_sound p13_17,
   search_sound p13_18,
   search_sound p13_19,
   search_sound p13_20, trivial⟩

end SingerC3.Cert
