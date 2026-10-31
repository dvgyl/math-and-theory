import SingerC3.Search

/-!
# Certificate part 2

Kernel-checked searches closing 21 of the partial assignments reached by the top search
(`SingerC3.Cert.top`). Each pair is `(o, z)`: orbit indices fixed to `true` and to `false`.
-/

namespace SingerC3.Cert

open SingerC3

theorem p02_00 : search 136314881 1957096751169011712 = true := by decide +kernel
theorem p02_01 : search 201326593 2093049409657896960 = true := by decide +kernel
theorem p02_02 : search 268443649 2254615938993766400 = true := by decide +kernel
theorem p02_03 : search 137439477761 1957096613732155392 = true := by decide +kernel
theorem p02_04 : search 1168231104513 2255740738513928192 = true := by decide +kernel
theorem p02_05 : search 20547673299877889 2242792614430507008 = true := by decide +kernel
theorem p02_06 : search 72057594037928001 1729578038733080832 = true := by decide +kernel
theorem p02_07 : search 72057662757404673 1730985894888095744 = true := by decide +kernel
theorem p02_08 : search 72057662757421057 1730985894888079360 = true := by decide +kernel
theorem p02_09 : search 72057662757666817 1730985894887817216 = true := by decide +kernel
theorem p02_10 : search 72092778678452225 1730948511224299520 = true := by decide +kernel
theorem p02_11 : search 72198606404190209 2180305169600741376 = true := by decide +kernel
theorem p02_12 : search 288230377233842177 1957096750153990144 = true := by decide +kernel
theorem p02_13 : search 576461851815575553 1617355491344646144 = true := by decide +kernel
theorem p02_14 : search 577023702256844801 1641632467316113408 = true := by decide +kernel
theorem p02_15 : search 577023702290399233 1641632467280461824 = true := by decide +kernel
theorem p02_16 : search 585467951574941697 1603844692443660288 = true := by decide +kernel
theorem p02_17 : search 720575944674246657 1516587552474136576 = true := by decide +kernel
theorem p02_18 : search 720576215257186305 1516587174517014528 = true := by decide +kernel
theorem p02_19 : search 1188950301634199553 801922346221830144 = true := by decide +kernel
theorem p02_20 : search 1225542048598196225 757730637305085952 = true := by decide +kernel

/-- The partial assignments closed in part 2. -/
def part02 : List (Nat × Nat) :=
  [(136314881, 1957096751169011712),
   (201326593, 2093049409657896960),
   (268443649, 2254615938993766400),
   (137439477761, 1957096613732155392),
   (1168231104513, 2255740738513928192),
   (20547673299877889, 2242792614430507008),
   (72057594037928001, 1729578038733080832),
   (72057662757404673, 1730985894888095744),
   (72057662757421057, 1730985894888079360),
   (72057662757666817, 1730985894887817216),
   (72092778678452225, 1730948511224299520),
   (72198606404190209, 2180305169600741376),
   (288230377233842177, 1957096750153990144),
   (576461851815575553, 1617355491344646144),
   (577023702256844801, 1641632467316113408),
   (577023702290399233, 1641632467280461824),
   (585467951574941697, 1603844692443660288),
   (720575944674246657, 1516587552474136576),
   (720576215257186305, 1516587174517014528),
   (1188950301634199553, 801922346221830144),
   (1225542048598196225, 757730637305085952)]

theorem part02_ok : AllNoSol part02 :=
  ⟨search_sound p02_00,
   search_sound p02_01,
   search_sound p02_02,
   search_sound p02_03,
   search_sound p02_04,
   search_sound p02_05,
   search_sound p02_06,
   search_sound p02_07,
   search_sound p02_08,
   search_sound p02_09,
   search_sound p02_10,
   search_sound p02_11,
   search_sound p02_12,
   search_sound p02_13,
   search_sound p02_14,
   search_sound p02_15,
   search_sound p02_16,
   search_sound p02_17,
   search_sound p02_18,
   search_sound p02_19,
   search_sound p02_20, trivial⟩

end SingerC3.Cert
