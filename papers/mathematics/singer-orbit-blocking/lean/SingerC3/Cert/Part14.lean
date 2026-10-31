import SingerC3.Search

/-!
# Certificate part 14

Kernel-checked searches closing 21 of the partial assignments reached by the top search
(`SingerC3.Cert.top`). Each pair is `(o, z)`: orbit indices fixed to `true` and to `false`.
-/

namespace SingerC3.Cert

open SingerC3

theorem p14_00 : search 589825 1957096751306637312 = true := by decide +kernel
theorem p14_01 : search 2097153 1957096751304605696 = true := by decide +kernel
theorem p14_02 : search 16793601 2254615939262185472 = true := by decide +kernel
theorem p14_03 : search 281474978807809 1957378088706768896 = true := by decide +kernel
theorem p14_04 : search 564118184525825 2255177788292071424 = true := by decide +kernel
theorem p14_05 : search 2533274790395905 2261370238056529920 = true := by decide +kernel
theorem p14_06 : search 72059827420921857 1919008430283030528 = true := by decide +kernel
theorem p14_07 : search 72066390164504577 1734363113303572480 = true := by decide +kernel
theorem p14_08 : search 72198331543060481 2180305444747083776 = true := by decide +kernel
theorem p14_09 : search 108103983242936321 1873673366846570496 = true := by decide +kernel
theorem p14_10 : search 144115188075864065 2091923127577100288 = true := by decide +kernel
theorem p14_11 : search 288231477810823169 1813288188249112576 = true := by decide +kernel
theorem p14_12 : search 434597364041252865 1805944215348314248 = true := by decide +kernel
theorem p14_13 : search 576460752303554561 1642125289295708160 = true := by decide +kernel
theorem p14_14 : search 580964351947571201 1612851891698401280 = true := by decide +kernel
theorem p14_15 : search 585467951560261633 1603844692460437504 = true := by decide +kernel
theorem p14_16 : search 613052499275808769 1603281467343896576 = true := by decide +kernel
theorem p14_17 : search 721701840286121985 1515461274610171904 = true := by decide +kernel
theorem p14_18 : search 864691137045069825 1203041642647392256 = true := by decide +kernel
theorem p14_19 : search 1152921504607895553 842454742876569600 = true := by decide +kernel
theorem p14_20 : search 1585267068834414593 576460752303439872 = true := by decide +kernel

/-- The partial assignments closed in part 14. -/
def part14 : List (Nat × Nat) :=
  [(589825, 1957096751306637312),
   (2097153, 1957096751304605696),
   (16793601, 2254615939262185472),
   (281474978807809, 1957378088706768896),
   (564118184525825, 2255177788292071424),
   (2533274790395905, 2261370238056529920),
   (72059827420921857, 1919008430283030528),
   (72066390164504577, 1734363113303572480),
   (72198331543060481, 2180305444747083776),
   (108103983242936321, 1873673366846570496),
   (144115188075864065, 2091923127577100288),
   (288231477810823169, 1813288188249112576),
   (434597364041252865, 1805944215348314248),
   (576460752303554561, 1642125289295708160),
   (580964351947571201, 1612851891698401280),
   (585467951560261633, 1603844692460437504),
   (613052499275808769, 1603281467343896576),
   (721701840286121985, 1515461274610171904),
   (864691137045069825, 1203041642647392256),
   (1152921504607895553, 842454742876569600),
   (1585267068834414593, 576460752303439872)]

theorem part14_ok : AllNoSol part14 :=
  ⟨search_sound p14_00,
   search_sound p14_01,
   search_sound p14_02,
   search_sound p14_03,
   search_sound p14_04,
   search_sound p14_05,
   search_sound p14_06,
   search_sound p14_07,
   search_sound p14_08,
   search_sound p14_09,
   search_sound p14_10,
   search_sound p14_11,
   search_sound p14_12,
   search_sound p14_13,
   search_sound p14_14,
   search_sound p14_15,
   search_sound p14_16,
   search_sound p14_17,
   search_sound p14_18,
   search_sound p14_19,
   search_sound p14_20, trivial⟩

end SingerC3.Cert
