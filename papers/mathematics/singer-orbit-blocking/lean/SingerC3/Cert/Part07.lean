import SingerC3.Search

/-!
# Certificate part 7

Kernel-checked searches closing 21 of the partial assignments reached by the top search
(`SingerC3.Cert.top`). Each pair is `(o, z)`: orbit indices fixed to `true` and to `false`.
-/

namespace SingerC3.Cert

open SingerC3

theorem p07_00 : search 524289 1957096751306702848 = true := by decide +kernel
theorem p07_01 : search 2162689 1957096751304540160 = true := by decide +kernel
theorem p07_02 : search 35433480193 2106560306250514432 = true := by decide +kernel
theorem p07_03 : search 172872433665 2106560168811560960 = true := by decide +kernel
theorem p07_04 : search 274877923329 2254615664115843072 = true := by decide +kernel
theorem p07_05 : search 281474977234945 1957404476987932672 = true := by decide +kernel
theorem p07_06 : search 1125900980584449 2092019917808205824 = true := by decide +kernel
theorem p07_07 : search 4503668413956097 2102056501538455552 = true := by decide +kernel
theorem p07_08 : search 9007269047959553 2093330776186683392 = true := by decide +kernel
theorem p07_09 : search 10133099163680769 1983836736517603328 = true := by decide +kernel
theorem p07_10 : search 18015532380848129 2237163475673546752 = true := by decide +kernel
theorem p07_11 : search 45035996275802113 1947807939498639360 = true := by decide +kernel
theorem p07_12 : search 72374253386727425 1730648894305730560 = true := by decide +kernel
theorem p07_13 : search 288230376151711747 1803692751425396736 = true := by decide +kernel
theorem p07_14 : search 580964351932891137 1612851891715178496 = true := by decide +kernel
theorem p07_15 : search 1152939234231844865 802032159878615712 = true := by decide +kernel
theorem p07_16 : search 1153202979583557633 801640733671948288 = true := by decide +kernel
theorem p07_17 : search 1161928712451522561 792657998550925312 = true := by decide +kernel
theorem p07_18 : search 1161933101908099073 792651126603251712 = true := by decide +kernel
theorem p07_19 : search 1729382256977379329 400961173043806208 = true := by decide +kernel
theorem p07_20 : search 2017612633061982209 0 = true := by decide +kernel

/-- The partial assignments closed in part 7. -/
def part07 : List (Nat × Nat) :=
  [(524289, 1957096751306702848),
   (2162689, 1957096751304540160),
   (35433480193, 2106560306250514432),
   (172872433665, 2106560168811560960),
   (274877923329, 2254615664115843072),
   (281474977234945, 1957404476987932672),
   (1125900980584449, 2092019917808205824),
   (4503668413956097, 2102056501538455552),
   (9007269047959553, 2093330776186683392),
   (10133099163680769, 1983836736517603328),
   (18015532380848129, 2237163475673546752),
   (45035996275802113, 1947807939498639360),
   (72374253386727425, 1730648894305730560),
   (288230376151711747, 1803692751425396736),
   (580964351932891137, 1612851891715178496),
   (1152939234231844865, 802032159878615712),
   (1153202979583557633, 801640733671948288),
   (1161928712451522561, 792657998550925312),
   (1161933101908099073, 792651126603251712),
   (1729382256977379329, 400961173043806208),
   (2017612633061982209, 0)]

theorem part07_ok : AllNoSol part07 :=
  ⟨search_sound p07_00,
   search_sound p07_01,
   search_sound p07_02,
   search_sound p07_03,
   search_sound p07_04,
   search_sound p07_05,
   search_sound p07_06,
   search_sound p07_07,
   search_sound p07_08,
   search_sound p07_09,
   search_sound p07_10,
   search_sound p07_11,
   search_sound p07_12,
   search_sound p07_13,
   search_sound p07_14,
   search_sound p07_15,
   search_sound p07_16,
   search_sound p07_17,
   search_sound p07_18,
   search_sound p07_19,
   search_sound p07_20, trivial⟩

end SingerC3.Cert
