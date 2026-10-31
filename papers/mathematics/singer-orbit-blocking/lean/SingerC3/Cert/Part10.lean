import SingerC3.Search

/-!
# Certificate part 10

Kernel-checked searches closing 21 of the partial assignments reached by the top search
(`SingerC3.Cert.top`). Each pair is `(o, z)`: orbit indices fixed to `true` and to `false`.
-/

namespace SingerC3.Cert

open SingerC3

theorem p10_00 : search 16385 2254615939278962688 = true := by decide +kernel
theorem p10_01 : search 8454145 2093049409859223552 = true := by decide +kernel
theorem p10_02 : search 67108865 2093049409792180288 = true := by decide +kernel
theorem p10_03 : search 1073741889 2093049408718438400 = true := by decide +kernel
theorem p10_04 : search 274886295553 2093049027472916480 = true := by decide +kernel
theorem p10_05 : search 10170482556929 2102635668214644736 = true := by decide +kernel
theorem p10_06 : search 1125934333689857 2092019884522209280 = true := by decide +kernel
theorem p10_07 : search 2251799813687297 1954843850838441984 = true := by decide +kernel
theorem p10_08 : search 72057628431220737 1734371909396594688 = true := by decide +kernel
theorem p10_09 : search 73218678316859393 1729522994398887936 = true := by decide +kernel
theorem p10_10 : search 153122387332694017 1803710343608795136 = true := by decide +kernel
theorem p10_11 : search 288249067849383937 1813261799970045952 = true := by decide +kernel
theorem p10_12 : search 288793326172241921 1812699950601994240 = true := by decide +kernel
theorem p10_13 : search 297237575473561601 1803692751347253248 = true := by decide +kernel
theorem p10_14 : search 576460752303427585 1603844692463190016 = true := by decide +kernel
theorem p10_15 : search 579275502070530049 1639310264362860544 = true := by decide +kernel
theorem p10_16 : search 1152921642045800449 802049752064660128 = true := by decide +kernel
theorem p10_17 : search 1157425104235266049 837951143249199104 = true := by decide +kernel
theorem p10_18 : search 1224979100792258561 758293776237068288 = true := by decide +kernel
theorem p10_19 : search 1729382256914464769 400961173110915072 = true := by decide +kernel
theorem p10_20 : search 1729382325629747201 400961104324329472 = true := by decide +kernel

/-- The partial assignments closed in part 10. -/
def part10 : List (Nat × Nat) :=
  [(16385, 2254615939278962688),
   (8454145, 2093049409859223552),
   (67108865, 2093049409792180288),
   (1073741889, 2093049408718438400),
   (274886295553, 2093049027472916480),
   (10170482556929, 2102635668214644736),
   (1125934333689857, 2092019884522209280),
   (2251799813687297, 1954843850838441984),
   (72057628431220737, 1734371909396594688),
   (73218678316859393, 1729522994398887936),
   (153122387332694017, 1803710343608795136),
   (288249067849383937, 1813261799970045952),
   (288793326172241921, 1812699950601994240),
   (297237575473561601, 1803692751347253248),
   (576460752303427585, 1603844692463190016),
   (579275502070530049, 1639310264362860544),
   (1152921642045800449, 802049752064660128),
   (1157425104235266049, 837951143249199104),
   (1224979100792258561, 758293776237068288),
   (1729382256914464769, 400961173110915072),
   (1729382325629747201, 400961104324329472)]

theorem part10_ok : AllNoSol part10 :=
  ⟨search_sound p10_00,
   search_sound p10_01,
   search_sound p10_02,
   search_sound p10_03,
   search_sound p10_04,
   search_sound p10_05,
   search_sound p10_06,
   search_sound p10_07,
   search_sound p10_08,
   search_sound p10_09,
   search_sound p10_10,
   search_sound p10_11,
   search_sound p10_12,
   search_sound p10_13,
   search_sound p10_14,
   search_sound p10_15,
   search_sound p10_16,
   search_sound p10_17,
   search_sound p10_18,
   search_sound p10_19,
   search_sound p10_20, trivial⟩

end SingerC3.Cert
