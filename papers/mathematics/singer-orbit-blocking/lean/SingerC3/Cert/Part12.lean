import SingerC3.Search

/-!
# Certificate part 12

Kernel-checked searches closing 22 of the partial assignments reached by the top search
(`SingerC3.Cert.top`). Each pair is `(o, z)`: orbit indices fixed to `true` and to `false`.
-/

namespace SingerC3.Cert

open SingerC3

theorem p12_00 : search 8193 2254615939262201856 = true := by decide +kernel
theorem p12_01 : search 1207959553 2093049408584155136 = true := by decide +kernel
theorem p12_02 : search 4303355905 2093049405430038528 = true := by decide +kernel
theorem p12_03 : search 274877906947 2254615664115867648 = true := by decide +kernel
theorem p12_04 : search 1099511627841 2093048309206810624 = true := by decide +kernel
theorem p12_05 : search 1133871366145 2255740824136450048 = true := by decide +kernel
theorem p12_06 : search 17867131060225 2093119396149985280 = true := by decide +kernel
theorem p12_07 : search 140874929405953 1993125410749022208 = true := by decide +kernel
theorem p12_08 : search 299067163279361 1957378088708866048 = true := by decide +kernel
theorem p12_09 : search 9008573644275713 2093047926820438016 = true := by decide +kernel
theorem p12_10 : search 11258999336861697 2252363038516576256 = true := by decide +kernel
theorem p12_11 : search 72075220583710721 1918990838096986112 = true := by decide +kernel
theorem p12_12 : search 76561193698852865 1729859513676201984 = true := by decide +kernel
theorem p12_13 : search 288230376218820609 1813289290981965824 = true := by decide +kernel
theorem p12_14 : search 288794425616760833 1812698850016624640 = true := by decide +kernel
theorem p12_15 : search 297238674918080513 1803691650761883648 = true := by decide +kernel
theorem p12_16 : search 576460752303423489 1603844692463194112 = true := by decide +kernel
theorem p12_17 : search 576460786931597313 1679280054653157376 = true := by decide +kernel
theorem p12_18 : search 576461851831828481 1617355491325771776 = true := by decide +kernel
theorem p12_19 : search 598978750440275969 1594274268089155584 = true := by decide +kernel
theorem p12_20 : search 720575940513497089 1516587556769103872 = true := by decide +kernel
theorem p12_21 : search 1297054284868747265 864761497199329280 = true := by decide +kernel

/-- The partial assignments closed in part 12. -/
def part12 : List (Nat × Nat) :=
  [(8193, 2254615939262201856),
   (1207959553, 2093049408584155136),
   (4303355905, 2093049405430038528),
   (274877906947, 2254615664115867648),
   (1099511627841, 2093048309206810624),
   (1133871366145, 2255740824136450048),
   (17867131060225, 2093119396149985280),
   (140874929405953, 1993125410749022208),
   (299067163279361, 1957378088708866048),
   (9008573644275713, 2093047926820438016),
   (11258999336861697, 2252363038516576256),
   (72075220583710721, 1918990838096986112),
   (76561193698852865, 1729859513676201984),
   (288230376218820609, 1813289290981965824),
   (288794425616760833, 1812698850016624640),
   (297238674918080513, 1803691650761883648),
   (576460752303423489, 1603844692463194112),
   (576460786931597313, 1679280054653157376),
   (576461851831828481, 1617355491325771776),
   (598978750440275969, 1594274268089155584),
   (720575940513497089, 1516587556769103872),
   (1297054284868747265, 864761497199329280)]

theorem part12_ok : AllNoSol part12 :=
  ⟨search_sound p12_00,
   search_sound p12_01,
   search_sound p12_02,
   search_sound p12_03,
   search_sound p12_04,
   search_sound p12_05,
   search_sound p12_06,
   search_sound p12_07,
   search_sound p12_08,
   search_sound p12_09,
   search_sound p12_10,
   search_sound p12_11,
   search_sound p12_12,
   search_sound p12_13,
   search_sound p12_14,
   search_sound p12_15,
   search_sound p12_16,
   search_sound p12_17,
   search_sound p12_18,
   search_sound p12_19,
   search_sound p12_20,
   search_sound p12_21, trivial⟩

end SingerC3.Cert
