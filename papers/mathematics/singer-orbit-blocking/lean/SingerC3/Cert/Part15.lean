import SingerC3.Search

/-!
# Certificate part 15

Kernel-checked searches closing 21 of the partial assignments reached by the top search
(`SingerC3.Cert.top`). Each pair is `(o, z)`: orbit indices fixed to `true` and to `false`.
-/

namespace SingerC3.Cert

open SingerC3

theorem p15_00 : search 16777219 2254615939262210048 = true := by decide +kernel
theorem p15_01 : search 34368126977 2093049371070300160 = true := by decide +kernel
theorem p15_02 : search 274945015809 2093145784429051904 = true := by decide +kernel
theorem p15_03 : search 844424932229121 1956815138753347584 = true := by decide +kernel
theorem p15_04 : search 1126999418470401 2245326026668244992 = true := by decide +kernel
theorem p15_05 : search 1196268718129153 2091940719685009408 = true := by decide +kernel
theorem p15_06 : search 72093328165830657 1730947961468485632 = true := by decide +kernel
theorem p15_07 : search 72110370596061185 1730930369282441216 = true := by decide +kernel
theorem p15_08 : search 144115462954287105 2093049027483402240 = true := by decide +kernel
theorem p15_09 : search 144123984170975233 1813280492816957440 = true := by decide +kernel
theorem p15_10 : search 288230376151719937 1803692751425388544 = true := by decide +kernel
theorem p15_11 : search 288240271756361729 1813279392156090368 = true := by decide +kernel
theorem p15_12 : search 288793326113521665 1803692751414394880 = true := by decide +kernel
theorem p15_13 : search 290763650942107649 1954562238278795264 = true := by decide +kernel
theorem p15_14 : search 580964351931318273 1612851891717275648 = true := by decide +kernel
theorem p15_15 : search 792633534417207297 1443403680572243968 = true := by decide +kernel
theorem p15_16 : search 864691128455135233 1203041651245715456 = true := by decide +kernel
theorem p15_17 : search 1161928703861587969 792658007145054208 = true := by decide +kernel
theorem p15_18 : search 1161946296047632385 792633534417207296 = true := by decide +kernel
theorem p15_19 : search 1224979236083728385 758293587258507264 = true := by decide +kernel
theorem p15_20 : search 1297036727042441217 864788984990023680 = true := by decide +kernel

/-- The partial assignments closed in part 15. -/
def part15 : List (Nat × Nat) :=
  [(16777219, 2254615939262210048),
   (34368126977, 2093049371070300160),
   (274945015809, 2093145784429051904),
   (844424932229121, 1956815138753347584),
   (1126999418470401, 2245326026668244992),
   (1196268718129153, 2091940719685009408),
   (72093328165830657, 1730947961468485632),
   (72110370596061185, 1730930369282441216),
   (144115462954287105, 2093049027483402240),
   (144123984170975233, 1813280492816957440),
   (288230376151719937, 1803692751425388544),
   (288240271756361729, 1813279392156090368),
   (288793326113521665, 1803692751414394880),
   (290763650942107649, 1954562238278795264),
   (580964351931318273, 1612851891717275648),
   (792633534417207297, 1443403680572243968),
   (864691128455135233, 1203041651245715456),
   (1161928703861587969, 792658007145054208),
   (1161946296047632385, 792633534417207296),
   (1224979236083728385, 758293587258507264),
   (1297036727042441217, 864788984990023680)]

theorem part15_ok : AllNoSol part15 :=
  ⟨search_sound p15_00,
   search_sound p15_01,
   search_sound p15_02,
   search_sound p15_03,
   search_sound p15_04,
   search_sound p15_05,
   search_sound p15_06,
   search_sound p15_07,
   search_sound p15_08,
   search_sound p15_09,
   search_sound p15_10,
   search_sound p15_11,
   search_sound p15_12,
   search_sound p15_13,
   search_sound p15_14,
   search_sound p15_15,
   search_sound p15_16,
   search_sound p15_17,
   search_sound p15_18,
   search_sound p15_19,
   search_sound p15_20, trivial⟩

end SingerC3.Cert
