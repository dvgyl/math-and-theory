import SingerC3.Search

/-!
# Certificate part 3

Kernel-checked searches closing 22 of the partial assignments reached by the top search
(`SingerC3.Cert.top`). Each pair is `(o, z)`: orbit indices fixed to `true` and to `false`.
-/

namespace SingerC3.Cert

open SingerC3

theorem p03_00 : search 4362076161 2093049405362929664 = true := by decide +kernel
theorem p03_01 : search 69793218561 2106841575068794880 = true := by decide +kernel
theorem p03_02 : search 275951648769 2102619175540228096 = true := by decide +kernel
theorem p03_03 : search 1099511627777 2093048309206810688 = true := by decide +kernel
theorem p03_04 : search 18966575579137 2102618076028600320 = true := by decide +kernel
theorem p03_05 : search 562949953421315 2254052714162446336 = true := by decide +kernel
theorem p03_06 : search 2251937252638721 1954843713255505920 = true := by decide +kernel
theorem p03_07 : search 4503635060850689 2102056569184190464 = true := by decide +kernel
theorem p03_08 : search 6755399442104321 2243074244168646656 = true := by decide +kernel
theorem p03_09 : search 18014398509490177 2236038315652956160 = true := by decide +kernel
theorem p03_10 : search 72198331794718721 2180305444478648320 = true := by decide +kernel
theorem p03_11 : search 73183562664247297 1729859444956725248 = true := by decide +kernel
theorem p03_12 : search 90212730035765249 2161727821137838080 = true := by decide +kernel
theorem p03_13 : search 216190374299828225 1729558178770714624 = true := by decide +kernel
theorem p03_14 : search 288230514664407041 1957096612580818944 = true := by decide +kernel
theorem p03_15 : search 290482175966445569 1954843868016934912 = true := by decide +kernel
theorem p03_16 : search 576461027181330433 1649302660395827200 = true := by decide +kernel
theorem p03_17 : search 648518346609786881 1606096491988910080 = true := by decide +kernel
theorem p03_18 : search 873698327709876225 1188950301625815040 = true := by decide +kernel
theorem p03_19 : search 900719925474099201 1152921504606851072 = true := by decide +kernel
theorem p03_20 : search 1153484454568656897 839077043147636736 = true := by decide +kernel
theorem p03_21 : search 1226104998551617537 756604737398243328 = true := by decide +kernel

/-- The partial assignments closed in part 3. -/
def part03 : List (Nat × Nat) :=
  [(4362076161, 2093049405362929664),
   (69793218561, 2106841575068794880),
   (275951648769, 2102619175540228096),
   (1099511627777, 2093048309206810688),
   (18966575579137, 2102618076028600320),
   (562949953421315, 2254052714162446336),
   (2251937252638721, 1954843713255505920),
   (4503635060850689, 2102056569184190464),
   (6755399442104321, 2243074244168646656),
   (18014398509490177, 2236038315652956160),
   (72198331794718721, 2180305444478648320),
   (73183562664247297, 1729859444956725248),
   (90212730035765249, 2161727821137838080),
   (216190374299828225, 1729558178770714624),
   (288230514664407041, 1957096612580818944),
   (290482175966445569, 1954843868016934912),
   (576461027181330433, 1649302660395827200),
   (648518346609786881, 1606096491988910080),
   (873698327709876225, 1188950301625815040),
   (900719925474099201, 1152921504606851072),
   (1153484454568656897, 839077043147636736),
   (1226104998551617537, 756604737398243328)]

theorem part03_ok : AllNoSol part03 :=
  ⟨search_sound p03_00,
   search_sound p03_01,
   search_sound p03_02,
   search_sound p03_03,
   search_sound p03_04,
   search_sound p03_05,
   search_sound p03_06,
   search_sound p03_07,
   search_sound p03_08,
   search_sound p03_09,
   search_sound p03_10,
   search_sound p03_11,
   search_sound p03_12,
   search_sound p03_13,
   search_sound p03_14,
   search_sound p03_15,
   search_sound p03_16,
   search_sound p03_17,
   search_sound p03_18,
   search_sound p03_19,
   search_sound p03_20,
   search_sound p03_21, trivial⟩

end SingerC3.Cert
