import SingerC3.Search

/-!
# Certificate part 6

Kernel-checked searches closing 21 of the partial assignments reached by the top search
(`SingerC3.Cert.top`). Each pair is `(o, z)`: orbit indices fixed to `true` and to `false`.
-/

namespace SingerC3.Cert

open SingerC3

theorem p06_00 : search 1073807361 2093119777462550528 = true := by decide +kernel
theorem p06_01 : search 68786585601 2106560101165826048 = true := by decide +kernel
theorem p06_02 : search 274877915137 2254615664115859456 = true := by decide +kernel
theorem p06_03 : search 1374389534721 2102644466992021504 = true := by decide +kernel
theorem p06_04 : search 1374926405633 2102644466455150592 = true := by decide +kernel
theorem p06_05 : search 1376537018369 2102644464307666944 = true := by decide +kernel
theorem p06_06 : search 9071038038017 2093136988336029696 = true := by decide +kernel
theorem p06_07 : search 1127136857423873 2245325889229291520 = true := by decide +kernel
theorem p06_08 : search 2251799813685249 1954843850838444032 = true := by decide +kernel
theorem p06_09 : search 9007199255265281 1947807939500703744 = true := by decide +kernel
theorem p06_10 : search 10134198673211393 2236037214997839872 = true := by decide +kernel
theorem p06_11 : search 11821949021847553 2251799813685248000 = true := by decide +kernel
theorem p06_12 : search 72059793061183489 1919008464642768896 = true := by decide +kernel
theorem p06_13 : search 144116356306960385 2093048201706733568 = true := by decide +kernel
theorem p06_14 : search 288230376160100353 1804537176344526848 = true := by decide +kernel
theorem p06_15 : search 288511851136811009 1804255701367816192 = true := by decide +kernel
theorem p06_16 : search 432345565301309441 1803974225250222080 = true := by decide +kernel
theorem p06_17 : search 576461061541068801 1649302626036088832 = true := by decide +kernel
theorem p06_18 : search 1152921504606846977 801922346231597056 = true := by decide +kernel
theorem p06_19 : search 1161930902884843521 792655524649762816 = true := by decide +kernel
theorem p06_20 : search 1297045488775725057 864779089385373696 = true := by decide +kernel

/-- The partial assignments closed in part 6. -/
def part06 : List (Nat × Nat) :=
  [(1073807361, 2093119777462550528),
   (68786585601, 2106560101165826048),
   (274877915137, 2254615664115859456),
   (1374389534721, 2102644466992021504),
   (1374926405633, 2102644466455150592),
   (1376537018369, 2102644464307666944),
   (9071038038017, 2093136988336029696),
   (1127136857423873, 2245325889229291520),
   (2251799813685249, 1954843850838444032),
   (9007199255265281, 1947807939500703744),
   (10134198673211393, 2236037214997839872),
   (11821949021847553, 2251799813685248000),
   (72059793061183489, 1919008464642768896),
   (144116356306960385, 2093048201706733568),
   (288230376160100353, 1804537176344526848),
   (288511851136811009, 1804255701367816192),
   (432345565301309441, 1803974225250222080),
   (576461061541068801, 1649302626036088832),
   (1152921504606846977, 801922346231597056),
   (1161930902884843521, 792655524649762816),
   (1297045488775725057, 864779089385373696)]

theorem part06_ok : AllNoSol part06 :=
  ⟨search_sound p06_00,
   search_sound p06_01,
   search_sound p06_02,
   search_sound p06_03,
   search_sound p06_04,
   search_sound p06_05,
   search_sound p06_06,
   search_sound p06_07,
   search_sound p06_08,
   search_sound p06_09,
   search_sound p06_10,
   search_sound p06_11,
   search_sound p06_12,
   search_sound p06_13,
   search_sound p06_14,
   search_sound p06_15,
   search_sound p06_16,
   search_sound p06_17,
   search_sound p06_18,
   search_sound p06_19,
   search_sound p06_20, trivial⟩

end SingerC3.Cert
