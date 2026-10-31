import SingerC3.Search

/-!
# Certificate part 8

Kernel-checked searches closing 21 of the partial assignments reached by the top search
(`SingerC3.Cert.top`). Each pair is `(o, z)`: orbit indices fixed to `true` and to `false`.
-/

namespace SingerC3.Cert

open SingerC3

theorem p08_00 : search 1572865 1957096751305326592 = true := by decide +kernel
theorem p08_01 : search 67174401 2093049409792114688 = true := by decide +kernel
theorem p08_02 : search 142606337 2093049409725005824 = true := by decide +kernel
theorem p08_03 : search 1073741825 2093049408718438464 = true := by decide +kernel
theorem p08_04 : search 34426847233 2102056570258194432 = true := by decide +kernel
theorem p08_05 : search 70369817985025 2093049408718372864 = true := by decide +kernel
theorem p08_06 : search 70374112886785 2093066996475232256 = true := by decide +kernel
theorem p08_07 : search 290271070257153 1957395680894910464 = true := by decide +kernel
theorem p08_08 : search 4504703433965569 2129077101796524032 = true := by decide +kernel
theorem p08_09 : search 36029896530657281 2237163514462470144 = true := by decide +kernel
theorem p08_10 : search 38280596966866945 1954843850694459392 = true := by decide +kernel
theorem p08_11 : search 72075186223972353 1918990872456724480 = true := by decide +kernel
theorem p08_12 : search 72198331528380417 2180305444763860992 = true := by decide +kernel
theorem p08_13 : search 72356661200683009 1918709363120275456 = true := by decide +kernel
theorem p08_14 : search 90071992547442689 1729578038733045760 = true := by decide +kernel
theorem p08_15 : search 216313519602139137 2017612633061982208 = true := by decide +kernel
theorem p08_16 : search 297237576480194561 1948089413326077952 = true := by decide +kernel
theorem p08_17 : search 594475167992774657 1598779379545014272 = true := by decide +kernel
theorem p08_18 : search 612489549322518529 1606096492276744192 = true := by decide +kernel
theorem p08_19 : search 1224979098644774913 758293778384551936 = true := by decide +kernel
theorem p08_20 : search 1224979133004513281 758293724697460736 = true := by decide +kernel

/-- The partial assignments closed in part 8. -/
def part08 : List (Nat × Nat) :=
  [(1572865, 1957096751305326592),
   (67174401, 2093049409792114688),
   (142606337, 2093049409725005824),
   (1073741825, 2093049408718438464),
   (34426847233, 2102056570258194432),
   (70369817985025, 2093049408718372864),
   (70374112886785, 2093066996475232256),
   (290271070257153, 1957395680894910464),
   (4504703433965569, 2129077101796524032),
   (36029896530657281, 2237163514462470144),
   (38280596966866945, 1954843850694459392),
   (72075186223972353, 1918990872456724480),
   (72198331528380417, 2180305444763860992),
   (72356661200683009, 1918709363120275456),
   (90071992547442689, 1729578038733045760),
   (216313519602139137, 2017612633061982208),
   (297237576480194561, 1948089413326077952),
   (594475167992774657, 1598779379545014272),
   (612489549322518529, 1606096492276744192),
   (1224979098644774913, 758293778384551936),
   (1224979133004513281, 758293724697460736)]

theorem part08_ok : AllNoSol part08 :=
  ⟨search_sound p08_00,
   search_sound p08_01,
   search_sound p08_02,
   search_sound p08_03,
   search_sound p08_04,
   search_sound p08_05,
   search_sound p08_06,
   search_sound p08_07,
   search_sound p08_08,
   search_sound p08_09,
   search_sound p08_10,
   search_sound p08_11,
   search_sound p08_12,
   search_sound p08_13,
   search_sound p08_14,
   search_sound p08_15,
   search_sound p08_16,
   search_sound p08_17,
   search_sound p08_18,
   search_sound p08_19,
   search_sound p08_20, trivial⟩

end SingerC3.Cert
