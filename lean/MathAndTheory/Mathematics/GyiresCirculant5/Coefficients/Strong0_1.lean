module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.CompactInputs.Chamber0

/-!
# Chamber 0 (ordering `01234`): coefficient of `a^1`

Generated certificate. The coefficient of `a^1` (a power of the smallest weight) in the chamber
polynomial `chamberPoly0` is a polynomial in the first gap `b` whose coefficients are explicit
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

def strong0_part_1_0 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 573910) + ((d * 3643980) + (e * 1521210)))) + ((d * ((d * 10818690) + (e * 8807560))) + (e * (e * 2327610))))) + ((d * ((d * ((d * 18979560) + (e * 22852290))) + (e * (e * 12500020)))) + (e * (e * (e * 2928270)))))) + ((d * ((d * ((d * ((d * 21298270) + (e * 34013940))) + (e * (e * 29075640)))) + (e * (e * (e * 14240820))))) + (e * (e * (e * (e * 2863180))))))) + ((d * ((d * ((d * ((d * ((d * 15692420) + (e * 31440510))) + (e * (e * 37711440)))) + (e * (e * (e * 28912860))))) + (e * (e * (e * (e * 11940640)))))) + (e * (e * (e * (e * (e * 1993740)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 7548430) + (e * 18436600))) + (e * (e * 29481720)))) + (e * (e * (e * 31479960))))) + (e * (e * (e * (e * 19989070)))))) + (e * (e * (e * (e * (e * 6819960))))))) + (e * (e * (e * (e * (e * (e * 969960))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 2280680) + (e * 6730150))) + (e * (e * 13985640)))) + (e * (e * (e * 19500480))))) + (e * (e * (e * (e * 16901560)))))) + (e * (e * (e * (e * (e * 8824230))))))) + (e * (e * (e * (e * (e * (e * 2566400)))))))) + (e * (e * (e * (e * (e * (e * (e * 321200)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 392730) + (e * 1412740))) + (e * (e * 3761420)))) + (e * (e * (e * 6562520))))) + (e * (e * (e * (e * 7267120)))))) + (e * (e * (e * (e * (e * 5148020))))))) + (e * (e * (e * (e * (e * (e * 2283810)))))))) + (e * (e * (e * (e * (e * (e * (e * 581800))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 65150))))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 29380) + (e * 132210))) + (e * (e * 445680)))) + (e * (e * (e * 942900))))) + (e * (e * (e * (e * 1278840)))))) + (e * (e * (e * (e * (e * 1148340))))))) + (e * (e * (e * (e * (e * (e * 686160)))))))) + (e * (e * (e * (e * (e * (e * (e * 264210))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 59620)))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * (e * 6010)))))))))))

private theorem strong0_part_1_0_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_1_0 c d e := by
  unfold strong0_part_1_0
  positivity

theorem strong0_part_1_0_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 1) 0 = strong0_part_1_0 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift0_0_eq, compactShift0_1_eq, compactShift0_2_eq,
    compactShift0_3_eq, compactShift0_4_eq, compactShift0_5_eq,
    compactGram0_0_eq, compactGram0_1_eq, compactGram0_2_eq]
  dsimp only [compactShift0_0, compactShift0_1, compactShift0_2,
    compactShift0_3, compactShift0_4, compactShift0_5,
    compactGram0_0, compactGram0_1, compactGram0_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly0, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong0_part_1_0 <;> ring

def strong0_part_1_1 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * ((c * 5880800) + ((d * 33154600) + (e * 14477740)))) + ((d * ((d * 86833560) + (e * 74400400))) + (e * (e * 20787600))))) + ((d * ((d * ((d * 132353780) + (e * 168076820))) + (e * (e * 96262420)))) + (e * (e * (e * 22992480)))))) + ((d * ((d * ((d * ((d * 125897900) + (e * 212153140))) + (e * (e * 187464300)))) + (e * (e * (e * 92330860))))) + (e * (e * (e * (e * 18526400))))))) + ((d * ((d * ((d * ((d * ((d * 75755580) + (e * 159998480))) + (e * (e * 195209120)))) + (e * (e * (e * 148408780))))) + (e * (e * (e * (e * 60681740)))))) + (e * (e * (e * (e * (e * 10075040)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 28015220) + (e * 71897660))) + (e * (e * 114636640)))) + (e * (e * (e * 119641400))))) + (e * (e * (e * (e * 74564100)))))) + (e * (e * (e * (e * (e * 25112460))))))) + (e * (e * (e * (e * (e * (e * 3542760))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 5810020) + (e * 17878440))) + (e * (e * 36171360)))) + (e * (e * (e * 48601740))))) + (e * (e * (e * (e * 40955760)))))) + (e * (e * (e * (e * (e * 20921520))))))) + (e * (e * (e * (e * (e * (e * 5985460)))))))) + (e * (e * (e * (e * (e * (e * (e * 741940)))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * ((d * 517180) + (e * 1910540))) + (e * (e * 4821760)))) + (e * (e * (e * 8001240))))) + (e * (e * (e * (e * 8529920)))))) + (e * (e * (e * (e * (e * 5856520))))))) + (e * (e * (e * (e * (e * (e * 2534620)))))))) + (e * (e * (e * (e * (e * (e * (e * 635180))))))))) + (e * (e * (e * (e * (e * (e * (e * (e * 70680))))))))))

private theorem strong0_part_1_1_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_1_1 c d e := by
  unfold strong0_part_1_1
  positivity

theorem strong0_part_1_1_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 1) 1 = strong0_part_1_1 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift0_0_eq, compactShift0_1_eq, compactShift0_2_eq,
    compactShift0_3_eq, compactShift0_4_eq, compactShift0_5_eq,
    compactGram0_0_eq, compactGram0_1_eq, compactGram0_2_eq]
  dsimp only [compactShift0_0, compactShift0_1, compactShift0_2,
    compactShift0_3, compactShift0_4, compactShift0_5,
    compactGram0_0, compactGram0_1, compactGram0_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly0, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong0_part_1_1 <;> ring

def strong0_part_1_2 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * ((c * 26633280) + ((d * 130753280) + (e * 59269620)))) + ((d * ((d * 295204840) + (e * 263682360))) + (e * (e * 77377710))))) + ((d * ((d * ((d * 379327020) + (e * 502200980))) + (e * (e * 299239880)))) + (e * (e * (e * 72991710)))))) + ((d * ((d * ((d * ((d * 292844740) + (e * 513612480))) + (e * (e * 466719090)))) + (e * (e * (e * 232033760))))) + (e * (e * (e * (e * 46707680))))))) + ((d * ((d * ((d * ((d * ((d * 134338660) + (e * 294525340))) + (e * (e * 364651800)))) + (e * (e * (e * 276581890))))) + (e * (e * (e * (e * 112613380)))))) + (e * (e * (e * (e * (e * 18666120)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 33726670) + (e * 89498080))) + (e * (e * 142654790)))) + (e * (e * (e * 146817940))))) + (e * (e * (e * (e * 90409980)))))) + (e * (e * (e * (e * (e * 30193680))))))) + (e * (e * (e * (e * (e * (e * 4238450))))))))) + ((d * ((d * ((d * ((d * ((d * ((d * ((d * 3566220) + (e * 11277370))) + (e * (e * 22438980)))) + (e * (e * (e * 29411710))))) + (e * (e * (e * (e * 24296360)))))) + (e * (e * (e * (e * (e * 12214620))))))) + (e * (e * (e * (e * (e * (e * 3450840)))))))) + (e * (e * (e * (e * (e * (e * (e * 424350)))))))))

private theorem strong0_part_1_2_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_1_2 c d e := by
  unfold strong0_part_1_2
  positivity

theorem strong0_part_1_2_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 1) 2 = strong0_part_1_2 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift0_0_eq, compactShift0_1_eq, compactShift0_2_eq,
    compactShift0_3_eq, compactShift0_4_eq, compactShift0_5_eq,
    compactGram0_0_eq, compactGram0_1_eq, compactGram0_2_eq]
  dsimp only [compactShift0_0, compactShift0_1, compactShift0_2,
    compactShift0_3, compactShift0_4, compactShift0_5,
    compactGram0_0, compactGram0_1, compactGram0_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly0, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong0_part_1_2 <;> ring

def strong0_part_1_3 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * ((c * 70178720) + ((d * 292945900) + (e * 137009940)))) + ((d * ((d * 553275620) + (e * 511585020))) + (e * (e * 156973620))))) + ((d * ((d * ((d * 574859100) + (e * 787088140))) + (e * (e * 485765500)))) + (e * (e * (e * 121044600)))))) + ((d * ((d * ((d * ((d * 337381500) + (e * 610385700))) + (e * (e * 568137240)))) + (e * (e * (e * 285458740))))) + (e * (e * (e * (e * 57782440))))))) + ((d * ((d * ((d * ((d * ((d * 104708400) + (e * 236084540))) + (e * (e * 295851860)))) + (e * (e * (e * 224358460))))) + (e * (e * (e * (e * 91192420)))))) + (e * (e * (e * (e * (e * 15115380)))))))) + ((d * ((d * ((d * ((d * ((d * ((d * 13344420) + (e * 36290640))) + (e * (e * 57823280)))) + (e * (e * (e * 58880620))))) + (e * (e * (e * (e * 35925980)))))) + (e * (e * (e * (e * (e * 11922420))))))) + (e * (e * (e * (e * (e * (e * 1666860))))))))

private theorem strong0_part_1_3_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_1_3 c d e := by
  unfold strong0_part_1_3
  positivity

theorem strong0_part_1_3_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 1) 3 = strong0_part_1_3 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift0_0_eq, compactShift0_1_eq, compactShift0_2_eq,
    compactShift0_3_eq, compactShift0_4_eq, compactShift0_5_eq,
    compactGram0_0_eq, compactGram0_1_eq, compactGram0_2_eq]
  dsimp only [compactShift0_0, compactShift0_1, compactShift0_2,
    compactShift0_3, compactShift0_4, compactShift0_5,
    compactGram0_0, compactGram0_1, compactGram0_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly0, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong0_part_1_3 <;> ring

def strong0_part_1_4 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * ((c * 118962400) + ((d * 409435340) + (e * 196504620)))) + ((d * ((d * 620090270) + (e * 590055040))) + (e * (e * 188512200))))) + ((d * ((d * ((d * 488245100) + (e * 686999810))) + (e * (e * 437249100)))) + (e * (e * (e * 111192200)))))) + ((d * ((d * ((d * ((d * 193640380) + (e * 359027900))) + (e * (e * 340849240)))) + (e * (e * (e * 172945960))))) + (e * (e * (e * (e * 35219930))))))) + ((d * ((d * ((d * ((d * ((d * 30483720) + (e * 70244220))) + (e * (e * 88786100)))) + (e * (e * (e * 67277980))))) + (e * (e * (e * (e * 27310160)))))) + (e * (e * (e * (e * (e * 4528890)))))))

private theorem strong0_part_1_4_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_1_4 c d e := by
  unfold strong0_part_1_4
  positivity

theorem strong0_part_1_4_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 1) 4 = strong0_part_1_4 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift0_0_eq, compactShift0_1_eq, compactShift0_2_eq,
    compactShift0_3_eq, compactShift0_4_eq, compactShift0_5_eq,
    compactGram0_0_eq, compactGram0_1_eq, compactGram0_2_eq]
  dsimp only [compactShift0_0, compactShift0_1, compactShift0_2,
    compactShift0_3, compactShift0_4, compactShift0_5,
    compactGram0_0, compactGram0_1, compactGram0_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly0, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong0_part_1_4 <;> ring

def strong0_part_1_5 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * ((c * 135190920) + ((d * 367759100) + (e * 180138020)))) + ((d * ((d * 418295140) + (e * 407331060))) + (e * (e * 134708280))))) + ((d * ((d * ((d * 221863580) + (e * 319049540))) + (e * (e * 208135560)))) + (e * (e * (e * 53844020)))))) + ((d * ((d * ((d * ((d * 44616900) + (e * 84341300))) + (e * (e * 81160720)))) + (e * (e * (e * 41436320))))) + (e * (e * (e * (e * 8480280))))))

private theorem strong0_part_1_5_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_1_5 c d e := by
  unfold strong0_part_1_5
  positivity

theorem strong0_part_1_5_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 1) 5 = strong0_part_1_5 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift0_0_eq, compactShift0_1_eq, compactShift0_2_eq,
    compactShift0_3_eq, compactShift0_4_eq, compactShift0_5_eq,
    compactGram0_0_eq, compactGram0_1_eq, compactGram0_2_eq]
  dsimp only [compactShift0_0, compactShift0_1, compactShift0_2,
    compactShift0_3, compactShift0_4, compactShift0_5,
    compactGram0_0, compactGram0_1, compactGram0_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly0, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong0_part_1_5 <;> ring

def strong0_part_1_6 (c d e : ℝ) : ℝ :=
  ((c * ((c * ((c * 103836250) + ((d * 209405000) + (e * 104049750)))) + ((d * ((d * 158928140) + (e * 157409140))) + (e * (e * 53359390))))) + ((d * ((d * ((d * 42589260) + (e * 62258140))) + (e * (e * 41209140)))) + (e * (e * (e * 10770130)))))

private theorem strong0_part_1_6_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_1_6 c d e := by
  unfold strong0_part_1_6
  positivity

theorem strong0_part_1_6_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 1) 6 = strong0_part_1_6 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift0_0_eq, compactShift0_1_eq, compactShift0_2_eq,
    compactShift0_3_eq, compactShift0_4_eq, compactShift0_5_eq,
    compactGram0_0_eq, compactGram0_1_eq, compactGram0_2_eq]
  dsimp only [compactShift0_0, compactShift0_1, compactShift0_2,
    compactShift0_3, compactShift0_4, compactShift0_5,
    compactGram0_0, compactGram0_1, compactGram0_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly0, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong0_part_1_6 <;> ring

def strong0_part_1_7 (c d e : ℝ) : ℝ :=
  ((c * ((c * 52678940) + ((d * 70258920) + (e * 35159960)))) + ((d * ((d * 26691000) + (e * 26691000))) + (e * (e * 9111020))))

private theorem strong0_part_1_7_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_1_7 c d e := by
  unfold strong0_part_1_7
  positivity

theorem strong0_part_1_7_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 1) 7 = strong0_part_1_7 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift0_0_eq, compactShift0_1_eq, compactShift0_2_eq,
    compactShift0_3_eq, compactShift0_4_eq, compactShift0_5_eq,
    compactGram0_0_eq, compactGram0_1_eq, compactGram0_2_eq]
  dsimp only [compactShift0_0, compactShift0_1, compactShift0_2,
    compactShift0_3, compactShift0_4, compactShift0_5,
    compactGram0_0, compactGram0_1, compactGram0_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly0, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong0_part_1_7 <;> ring

def strong0_part_1_8 (c d e : ℝ) : ℝ :=
  ((c * 16337970) + ((d * 10891980) + (e * 5445990)))

private theorem strong0_part_1_8_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_1_8 c d e := by
  unfold strong0_part_1_8
  positivity

theorem strong0_part_1_8_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 1) 8 = strong0_part_1_8 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift0_0_eq, compactShift0_1_eq, compactShift0_2_eq,
    compactShift0_3_eq, compactShift0_4_eq, compactShift0_5_eq,
    compactGram0_0_eq, compactGram0_1_eq, compactGram0_2_eq]
  dsimp only [compactShift0_0, compactShift0_1, compactShift0_2,
    compactShift0_3, compactShift0_4, compactShift0_5,
    compactGram0_0, compactGram0_1, compactGram0_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly0, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong0_part_1_8 <;> ring

def strong0_part_1_9 (c d e : ℝ) : ℝ :=
  2420440

private theorem strong0_part_1_9_nonneg (c d e : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : 0 ≤ strong0_part_1_9 c d e := by
  unfold strong0_part_1_9
  positivity

theorem strong0_part_1_9_eq (c d e : ℝ) :
    polyCoeff (chamberPoly0 c d e 1) 9 = strong0_part_1_9 c d e := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift0_0_eq, compactShift0_1_eq, compactShift0_2_eq,
    compactShift0_3_eq, compactShift0_4_eq, compactShift0_5_eq,
    compactGram0_0_eq, compactGram0_1_eq, compactGram0_2_eq]
  dsimp only [compactShift0_0, compactShift0_1, compactShift0_2,
    compactShift0_3, compactShift0_4, compactShift0_5,
    compactGram0_0, compactGram0_1, compactGram0_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly0, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num [polyCoeff] <;> unfold strong0_part_1_9 <;> ring

theorem strong0_coeff_1_length (c d e : ℝ) :
    (chamberPoly0 c d e 1).length ≤ 10 := by
  dsimp only [chamberPoly0, residualOuter]
  simp only [ite_eq_right (show (1 : Fin 11) ≠ 0 by decide)]
  dsimp only [liftedOuter, polyOuterCoeff, Matrix.cons_val]
  dsimp only [polyOuterPart1, polyShiftCoeffs, polyGramShiftCoeffs, Matrix.cons_val]
  simp only [compactShift0_0_eq, compactShift0_1_eq, compactShift0_2_eq,
    compactShift0_3_eq, compactShift0_4_eq, compactShift0_5_eq,
    compactGram0_0_eq, compactGram0_1_eq, compactGram0_2_eq]
  dsimp only [compactShift0_0, compactShift0_1, compactShift0_2,
    compactShift0_3, compactShift0_4, compactShift0_5,
    compactGram0_0, compactGram0_1, compactGram0_2,
    polyGramShiftCoeff0, polyGramShiftCoeff1, polyGramShiftCoeff2,
    polyGramShiftCoeff3, polyGramShiftCoeff4, polyGramShiftCoeff5,
    polySum5, basePoly0, gapPoly, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  norm_num

theorem strong0_coeff_1_nonneg (b c d e : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ polyEval (chamberPoly0 c d e 1) b := by
  apply polyEval_nonneg_of_coeff _ b 10
    (strong0_coeff_1_length c d e) hb
  apply forall_fin10
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 1) 0
    rw [strong0_part_1_0_eq]
    exact strong0_part_1_0_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 1) 1
    rw [strong0_part_1_1_eq]
    exact strong0_part_1_1_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 1) 2
    rw [strong0_part_1_2_eq]
    exact strong0_part_1_2_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 1) 3
    rw [strong0_part_1_3_eq]
    exact strong0_part_1_3_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 1) 4
    rw [strong0_part_1_4_eq]
    exact strong0_part_1_4_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 1) 5
    rw [strong0_part_1_5_eq]
    exact strong0_part_1_5_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 1) 6
    rw [strong0_part_1_6_eq]
    exact strong0_part_1_6_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 1) 7
    rw [strong0_part_1_7_eq]
    exact strong0_part_1_7_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 1) 8
    rw [strong0_part_1_8_eq]
    exact strong0_part_1_8_nonneg c d e hc hd he
  · change 0 ≤ polyCoeff (chamberPoly0 c d e 1) 9
    rw [strong0_part_1_9_eq]
    exact strong0_part_1_9_nonneg c d e hc hd he

end MathAndTheory.GyiresCirculant5
