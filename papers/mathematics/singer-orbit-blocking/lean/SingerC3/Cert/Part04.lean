import SingerC3.Search

/-!
# Certificate part 4

Kernel-checked searches closing 22 of the partial assignments reached by the top search
(`SingerC3.Cert.top`). Each pair is `(o, z)`: orbit indices fixed to `true` and to `false`.
-/

namespace SingerC3.Cert

open SingerC3

theorem p04_00 : search 786433 1957096751306375168 = true := by decide +kernel
theorem p04_01 : search 1168499539969 2255740738245492736 = true := by decide +kernel
theorem p04_02 : search 562949953429505 2254052714162438144 = true := by decide +kernel
theorem p04_03 : search 564083824787457 2255177874183028736 = true := by decide +kernel
theorem p04_04 : search 844424930656257 1956815138755444736 = true := by decide +kernel
theorem p04_05 : search 1125899973951489 2092019918898724864 = true := by decide +kernel
theorem p04_06 : search 2251834307641345 1991013385201778688 = true := by decide +kernel
theorem p04_07 : search 2392537436258305 1990872647713423360 = true := by decide +kernel
theorem p04_08 : search 72057594037929985 1765607128346689536 = true := by decide +kernel
theorem p04_09 : search 72058212513218561 1730985344863567872 = true := by decide +kernel
theorem p04_10 : search 144115188075855875 2127951924596072448 = true := by decide +kernel
theorem p04_11 : search 144115188075872257 2091923127577083904 = true := by decide +kernel
theorem p04_12 : search 144115188077953025 1813289291057463296 = true := by decide +kernel
theorem p04_13 : search 144115190225436673 1813289288909979648 = true := by decide +kernel
theorem p04_14 : search 288230377225453569 1957096750162378752 = true := by decide +kernel
theorem p04_15 : search 360428707677995009 1729382256910270464 = true := by decide +kernel
theorem p04_16 : search 576460752303947777 1617356590856273920 = true := by decide +kernel
theorem p04_17 : search 594475151349776385 1598779396724883456 = true := by decide +kernel
theorem p04_18 : search 720576009098756097 1516587449394921472 = true := by decide +kernel
theorem p04_19 : search 864708720641179649 1203024050461347840 = true := by decide +kernel
theorem p04_20 : search 869194728082505729 1197957500880556032 = true := by decide +kernel
theorem p04_21 : search 1297037792194330625 864787885478395904 = true := by decide +kernel

/-- The partial assignments closed in part 4. -/
def part04 : List (Nat × Nat) :=
  [(786433, 1957096751306375168),
   (1168499539969, 2255740738245492736),
   (562949953429505, 2254052714162438144),
   (564083824787457, 2255177874183028736),
   (844424930656257, 1956815138755444736),
   (1125899973951489, 2092019918898724864),
   (2251834307641345, 1991013385201778688),
   (2392537436258305, 1990872647713423360),
   (72057594037929985, 1765607128346689536),
   (72058212513218561, 1730985344863567872),
   (144115188075855875, 2127951924596072448),
   (144115188075872257, 2091923127577083904),
   (144115188077953025, 1813289291057463296),
   (144115190225436673, 1813289288909979648),
   (288230377225453569, 1957096750162378752),
   (360428707677995009, 1729382256910270464),
   (576460752303947777, 1617356590856273920),
   (594475151349776385, 1598779396724883456),
   (720576009098756097, 1516587449394921472),
   (864708720641179649, 1203024050461347840),
   (869194728082505729, 1197957500880556032),
   (1297037792194330625, 864787885478395904)]

theorem part04_ok : AllNoSol part04 :=
  ⟨search_sound p04_00,
   search_sound p04_01,
   search_sound p04_02,
   search_sound p04_03,
   search_sound p04_04,
   search_sound p04_05,
   search_sound p04_06,
   search_sound p04_07,
   search_sound p04_08,
   search_sound p04_09,
   search_sound p04_10,
   search_sound p04_11,
   search_sound p04_12,
   search_sound p04_13,
   search_sound p04_14,
   search_sound p04_15,
   search_sound p04_16,
   search_sound p04_17,
   search_sound p04_18,
   search_sound p04_19,
   search_sound p04_20,
   search_sound p04_21, trivial⟩

end SingerC3.Cert
