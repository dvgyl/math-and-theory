module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Chamber1

/-!
# Chamber 1 (ordering `01243`): coefficient of `a^1`

Generated certificate. The coefficient of `a^1` (a power of the smallest weight) in the chamber
polynomial `chamberPoly1` is a polynomial in the first gap `b` whose coefficients are explicit
polynomials in `c`, `d`, `e` with nonnegative integer coefficients. Each is proved equal to the
computed coefficient by `ring` and nonnegative by `positivity`, so the whole coefficient is
nonnegative for `b, c, d, e ≥ 0`.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
namespace MathAndTheory.GyiresCirculant5

def strong1_part_1_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 573910) + ((d * 3643980) + (e * 2122770)))) + ((d * ((d * 10818690) + (e * 12829820))) + (e * (e * 4338740))))) + ((d * ((d * ((d * 18979560) + (e * 34086390))) + (e * (e * 23734120)))) + (e * (e * (e * 5699020)))))) + ((d * ((d * ((d * ((d * 21298270) + (e * 51179140))) + (e * (e * 54823440)))) + (e * (e * (e * 27061720))))) + (e * (e * (e * (e * 4982330))))))) + ((d * ((d * ((d * ((d * ((d * 15692420) + (e * 47021590))) + (e * (e * 68873600)))) + (e * (e * (e * 52502600))))) + (e * (e * (e * (e * 19949300)))))) + (e * (e * (e * (e * (e * 2997390)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 7548430) + (e * 26853980))) + (e * (e * 50525170)))) + (e * (e * (e * 53049520))))) + (e * (e * (e * (e * 31299960)))))) + (e * (e * (e * (e * (e * 9752760))))))) + (e * (e * (e * (e * (e * (e * 1252660))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 2280680) + (e * 9234610))) + (e * (e * 21499020)))) + (e * (e * (e * 29299270))))) + (e * (e * (e * (e * 23976840)))))) + (e * (e * (e * (e * (e * 11676000))))))) + (e * (e * (e * (e * (e * (e * 3132760)))))))) + (e * (e * (e * (e * (e * (e * (e * 358220)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 392730) + (e * 1729100))) + (e * (e * 4868680)))) + (e * (e * (e * 8331340))))) + (e * (e * (e * (e * 8921020)))))) + (e * (e * (e * (e * (e * 6070640))))))) + (e * (e * (e * (e * (e * (e * 2567470)))))))) + (e * (e * (e * (e * (e * (e * (e * 618820))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 65150))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 29380) + (e * 132210))) + (e * (e * 445680)))) + (e * (e * (e * 942900))))) + (e * (e * (e * (e * 1278840)))))) + (e * (e * (e * (e * (e * 1148340))))))) + (e * (e * (e * (e * (e * (e * 686160)))))))) + (e * (e * (e * (e * (e * (e * (e * 264210))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59620)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))

private theorem strong1_part_1_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_1_0 c d e := by
  unfold strong1_part_1_0
  positivity

theorem strong1_part_1_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 1) 0 = strong1_part_1_0 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_1_0 <;> ring

def strong1_part_1_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 5880800) + ((d * 33154600) + (e * 18676860)))) + ((d * ((d * 86833560) + (e * 99266720))) + (e * (e * 33220760))))) + ((d * ((d * ((d * 132353780) + (e * 228984520))) + (e * (e * 157170120)))) + (e * (e * (e * 37546900)))))) + ((d * ((d * ((d * ((d * 125897900) + (e * 291438460))) + (e * (e * 306392280)))) + (e * (e * (e * 149729920))))) + (e * (e * (e * (e * 27404600))))))) + ((d * ((d * ((d * ((d * ((d * 75755580) + (e * 218779420))) + (e * (e * 312771000)))) + (e * (e * (e * 234783500))))) + (e * (e * (e * (e * 88275520)))))) + (e * (e * (e * (e * (e * 13164140)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 28015220) + (e * 96193660))) + (e * (e * 175376640)))) + (e * (e * (e * 180232960))))) + (e * (e * (e * (e * 104711440)))))) + (e * (e * (e * (e * (e * 32241120))))))) + (e * (e * (e * (e * (e * (e * 4107200))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 5810020) + (e * 22791700))) + (e * (e * 50911140)))) + (e * (e * (e * 67429160))))) + (e * (e * (e * (e * 54044300)))))) + (e * (e * (e * (e * (e * 25882740))))))) + (e * (e * (e * (e * (e * (e * 6859040)))))))) + (e * (e * (e * (e * (e * (e * (e * 778960)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 517180) + (e * 2226900))) + (e * (e * 5929020)))) + (e * (e * (e * 9770060))))) + (e * (e * (e * (e * 10183820)))))) + (e * (e * (e * (e * (e * 6779140))))))) + (e * (e * (e * (e * (e * (e * 2818280)))))))) + (e * (e * (e * (e * (e * (e * (e * 672200))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 70680))))))))))

private theorem strong1_part_1_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_1_1 c d e := by
  unfold strong1_part_1_1
  positivity

theorem strong1_part_1_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 1) 1 = strong1_part_1_1 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_1_1 <;> ring

def strong1_part_1_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 26633280) + ((d * 130753280) + (e * 71483660)))) + ((d * ((d * 295204840) + (e * 326727320))) + (e * (e * 108900190))))) + ((d * ((d * ((d * 379327020) + (e * 635780080))) + (e * (e * 432818980)))) + (e * (e * (e * 103374210)))))) + ((d * ((d * ((d * ((d * 292844740) + (e * 657766480))) + (e * (e * 682950090)))) + (e * (e * (e * 331945940))))) + (e * (e * (e * (e * 60625270))))))) + ((d * ((d * ((d * ((d * ((d * 134338660) + (e * 377167960))) + (e * (e * 529937040)))) + (e * (e * (e * 393608070))))) + (e * (e * (e * (e * 146996940)))))) + (e * (e * (e * (e * (e * 21830490)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 33726670) + (e * 112861940))) + (e * (e * 201064440)))) + (e * (e * (e * 203353820))))) + (e * (e * (e * (e * 116804150)))))) + (e * (e * (e * (e * (e * 35661240))))))) + (e * (e * (e * (e * (e * (e * 4520190))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 3566220) + (e * 13686170))) + (e * (e * 29665380)))) + (e * (e * (e * 38440340))))) + (e * (e * (e * (e * 30309620)))))) + (e * (e * (e * (e * (e * 14324070))))))) + (e * (e * (e * (e * (e * (e * 3758060)))))))) + (e * (e * (e * (e * (e * (e * (e * 424350)))))))))

private theorem strong1_part_1_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_1_2 c d e := by
  unfold strong1_part_1_2
  positivity

theorem strong1_part_1_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 1) 2 = strong1_part_1_2 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_1_2 <;> ring

def strong1_part_1_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 70178720) + ((d * 292945900) + (e * 155935960)))) + ((d * ((d * 553275620) + (e * 594966220))) + (e * (e * 198664220))))) + ((d * ((d * ((d * 574859100) + (e * 937489160))) + (e * (e * 636166520)))) + (e * (e * (e * 152491860)))))) + ((d * ((d * ((d * ((d * 337381500) + (e * 739140300))) + (e * (e * 761269140)))) + (e * (e * (e * 369184640))))) + (e * (e * (e * (e * 67456740))))))) + ((d * ((d * ((d * ((d * ((d * 104708400) + (e * 287457460))) + (e * (e * 398597700)))) + (e * (e * (e * 293773880))))) + (e * (e * (e * (e * 109234920)))))) + (e * (e * (e * (e * (e * 16194300)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 13344420) + (e * 43775880))) + (e * (e * 76536380)))) + (e * (e * (e * 76394500))))) + (e * (e * (e * (e * 43483700)))))) + (e * (e * (e * (e * (e * 13194120))))))) + (e * (e * (e * (e * (e * (e * 1666860))))))))

private theorem strong1_part_1_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_1_3 c d e := by
  unfold strong1_part_1_3
  positivity

theorem strong1_part_1_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 1) 3 = strong1_part_1_3 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_1_3 <;> ring

def strong1_part_1_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 118962400) + ((d * 409435340) + (e * 212930720)))) + ((d * ((d * 620090270) + (e * 650125500))) + (e * (e * 218547430))))) + ((d * ((d * ((d * 488245100) + (e * 777735490))) + (e * (e * 527984780)))) + (e * (e * (e * 127302190)))))) + ((d * ((d * ((d * ((d * 193640380) + (e * 415533620))) + (e * (e * 425607820)))) + (e * (e * (e * 206230340))))) + (e * (e * (e * (e * 37735690))))))) + ((d * ((d * ((d * ((d * ((d * 30483720) + (e * 82174380))) + (e * (e * 112646420)))) + (e * (e * (e * 82452200))))) + (e * (e * (e * (e * 30554220)))))) + (e * (e * (e * (e * (e * 4528890)))))))

private theorem strong1_part_1_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_1_4 c d e := by
  unfold strong1_part_1_4
  positivity

theorem strong1_part_1_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 1) 4 = strong1_part_1_4 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_1_4 <;> ring

def strong1_part_1_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 135190920) + ((d * 367759100) + (e * 187621080)))) + ((d * ((d * 418295140) + (e * 429259220))) + (e * (e * 145672360))))) + ((d * ((d * ((d * 221863580) + (e * 346541200))) + (e * (e * 235627220)))) + (e * (e * (e * 57105580)))))) + ((d * ((d * ((d * ((d * 44616900) + (e * 94126300))) + (e * (e * 95838220)))) + (e * (e * (e * 46328820))))) + (e * (e * (e * (e * 8480280))))))

private theorem strong1_part_1_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_1_5 c d e := by
  unfold strong1_part_1_5
  positivity

theorem strong1_part_1_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 1) 5 = strong1_part_1_5 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_1_5 <;> ring

def strong1_part_1_6 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 103836250) + ((d * 209405000) + (e * 105355250)))) + ((d * ((d * 158928140) + (e * 160447140))) + (e * (e * 54878390))))) + ((d * ((d * ((d * 42589260) + (e * 65509640))) + (e * (e * 44460640)))) + (e * (e * (e * 10770130)))))

private theorem strong1_part_1_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_1_6 c d e := by
  unfold strong1_part_1_6
  positivity

theorem strong1_part_1_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 1) 6 = strong1_part_1_6 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_1_6 <;> ring

def strong1_part_1_7 (c d e : ℝ) : ℝ :=
  ((c * ((c * 52678940) + ((d * 70258920) + (e * 35098960)))) + ((d * ((d * 26691000) + (e * 26691000))) + (e * (e * 9111020))))

private theorem strong1_part_1_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_1_7 c d e := by
  unfold strong1_part_1_7
  positivity

theorem strong1_part_1_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 1) 7 = strong1_part_1_7 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_1_7 <;> ring

def strong1_part_1_8 (c d e : ℝ) : ℝ :=
  ((c * 16337970) + ((d * 10891980) + (e * 5445990)))

private theorem strong1_part_1_8_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_1_8 c d e := by
  unfold strong1_part_1_8
  positivity

theorem strong1_part_1_8_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 1) 8 = strong1_part_1_8 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_1_8 <;> ring

def strong1_part_1_9 (c d e : ℝ) : ℝ :=
  2420440

private theorem strong1_part_1_9_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong1_part_1_9 c d e := by
  unfold strong1_part_1_9
  positivity

theorem strong1_part_1_9_eq (c d e : ℝ) :
    polyCoeff (chamberPoly1 c d e 1) 9 = strong1_part_1_9 c d e := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong1_part_1_9 <;> ring

theorem strong1_coeff_1_length (c d e : ℝ) :
    (chamberPoly1 c d e 1).length ≤ 10 := by
  dsimp only [chamberPoly1, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift1_0_eq, compactShift1_1_eq, compactShift1_2_eq,
    compactShift1_3_eq, compactShift1_4_eq, compactShift1_5_eq,
    compactGram1_0_eq, compactGram1_1_eq, compactGram1_2_eq]
  dsimp only [compactShift1_0, compactShift1_1, compactShift1_2,
    compactShift1_3, compactShift1_4, compactShift1_5,
    compactGram1_0, compactGram1_1, compactGram1_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly1, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num

theorem strong1_coeff_1_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly1 c d e 1) b := by
  apply polyEval_nonneg_of_coeff _ b 10
    (strong1_coeff_1_length c d e) hb
  apply forall_fin10
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 1) 0
    rw [strong1_part_1_0_eq]
    exact strong1_part_1_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 1) 1
    rw [strong1_part_1_1_eq]
    exact strong1_part_1_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 1) 2
    rw [strong1_part_1_2_eq]
    exact strong1_part_1_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 1) 3
    rw [strong1_part_1_3_eq]
    exact strong1_part_1_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 1) 4
    rw [strong1_part_1_4_eq]
    exact strong1_part_1_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 1) 5
    rw [strong1_part_1_5_eq]
    exact strong1_part_1_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 1) 6
    rw [strong1_part_1_6_eq]
    exact strong1_part_1_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 1) 7
    rw [strong1_part_1_7_eq]
    exact strong1_part_1_7_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 1) 8
    rw [strong1_part_1_8_eq]
    exact strong1_part_1_8_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly1 c d e 1) 9
    rw [strong1_part_1_9_eq]
    exact strong1_part_1_9_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
