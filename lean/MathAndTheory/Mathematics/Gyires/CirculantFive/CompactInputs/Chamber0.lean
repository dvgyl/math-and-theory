module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.ChamberPolynomials
public import MathAndTheory.Mathematics.Gyires.CirculantFive.CompactInputs.Basic
public import Mathlib.Tactic.NormNum

/-!
# Collected input lists for chamber 0 (ordering `01234`)

Generated file. The shift coefficients of `P5` at the weights `basePoly0` and at their
autocorrelation vector, as coefficient lists in the first gap whose entries are explicit
polynomials in the remaining gaps `c`, `d`, `e`. Each entry is proved equal to the computed
list by `ring`.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace MathAndTheory.GyiresCirculant5

def compactShift0_0 (c d e : ℝ) : List ℝ :=
  [((c * ((c * ((c * ((c * ((c * 13) + ((d * 45) + (e * 20)))) + ((d * ((d * 65) + (e * 55))) + (e * (e * 15))))) + ((d * ((d * ((d * 45) + (e * 55))) + (e * (e * 35)))) + (e * (e * (e * 10)))))) + ((d * ((d * ((d * ((d * 15) + (e * 25))) + (e * (e * 30)))) + (e * (e * (e * 20))))) + (e * (e * (e * (e * 5))))))) + ((d * ((d * ((d * ((d * ((d * 2) + (e * 5))) + (e * (e * 10)))) + (e * (e * (e * 10))))) + (e * (e * (e * (e * 5)))))) + (e * (e * (e * (e * (e * 1))))))),
   ((c * ((c * ((c * ((c * 80) + ((d * 220) + (e * 105)))) + ((d * ((d * 240) + (e * 225))) + (e * (e * 65))))) + ((d * ((d * ((d * 115) + (e * 155))) + (e * (e * 95)))) + (e * (e * (e * 25)))))) + ((d * ((d * ((d * ((d * 20) + (e * 35))) + (e * (e * 35)))) + (e * (e * (e * 20))))) + (e * (e * (e * (e * 5)))))),
   ((c * ((c * ((c * 200) + ((d * 405) + (e * 200)))) + ((d * ((d * 290) + (e * 285))) + (e * (e * 85))))) + ((d * ((d * ((d * 70) + (e * 100))) + (e * (e * 60)))) + (e * (e * (e * 15))))),
   ((c * ((c * 255) + ((d * 340) + (e * 170)))) + ((d * ((d * 120) + (e * 120))) + (e * (e * 35)))),
   ((c * 165) + ((d * 110) + (e * 55))),
   44]

private theorem compactShift0_0_entry0 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff0 (basePoly0 c d e)) 0 = ((c * ((c * ((c * ((c * ((c * 13) + ((d * 45) + (e * 20)))) + ((d * ((d * 65) + (e * 55))) + (e * (e * 15))))) + ((d * ((d * ((d * 45) + (e * 55))) + (e * (e * 35)))) + (e * (e * (e * 10)))))) + ((d * ((d * ((d * ((d * 15) + (e * 25))) + (e * (e * 30)))) + (e * (e * (e * 20))))) + (e * (e * (e * (e * 5))))))) + ((d * ((d * ((d * ((d * ((d * 2) + (e * 5))) + (e * (e * 10)))) + (e * (e * (e * 10))))) + (e * (e * (e * (e * 5)))))) + (e * (e * (e * (e * (e * 1))))))) := by
  dsimp only [polyShiftCoeff0, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_0_entry1 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff0 (basePoly0 c d e)) 1 = ((c * ((c * ((c * ((c * 80) + ((d * 220) + (e * 105)))) + ((d * ((d * 240) + (e * 225))) + (e * (e * 65))))) + ((d * ((d * ((d * 115) + (e * 155))) + (e * (e * 95)))) + (e * (e * (e * 25)))))) + ((d * ((d * ((d * ((d * 20) + (e * 35))) + (e * (e * 35)))) + (e * (e * (e * 20))))) + (e * (e * (e * (e * 5)))))) := by
  dsimp only [polyShiftCoeff0, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_0_entry2 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff0 (basePoly0 c d e)) 2 = ((c * ((c * ((c * 200) + ((d * 405) + (e * 200)))) + ((d * ((d * 290) + (e * 285))) + (e * (e * 85))))) + ((d * ((d * ((d * 70) + (e * 100))) + (e * (e * 60)))) + (e * (e * (e * 15))))) := by
  dsimp only [polyShiftCoeff0, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_0_entry3 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff0 (basePoly0 c d e)) 3 = ((c * ((c * 255) + ((d * 340) + (e * 170)))) + ((d * ((d * 120) + (e * 120))) + (e * (e * 35)))) := by
  dsimp only [polyShiftCoeff0, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_0_entry4 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff0 (basePoly0 c d e)) 4 = ((c * 165) + ((d * 110) + (e * 55))) := by
  dsimp only [polyShiftCoeff0, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_0_entry5 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff0 (basePoly0 c d e)) 5 = 44 := by
  dsimp only [polyShiftCoeff0, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_0_length (c d e : ℝ) :
    (polyShiftCoeff0 (basePoly0 c d e)).length = 6 := by
  dsimp only [polyShiftCoeff0, basePoly0, Matrix.cons_val]
  simp only [polyAdd_length, polyScale_length, polyMul_length_total,
    polyPow, List.length_cons, List.length_nil]
  norm_num

theorem compactShift0_0_eq (c d e : ℝ) :
    polyShiftCoeff0 (basePoly0 c d e) = compactShift0_0 c d e := by
  apply polyList_eq_of_coeff_n _ _ 6 (compactShift0_0_length c d e) (by rfl)
  apply forall_fin6
  · conv_rhs => dsimp only [compactShift0_0, polyCoeff]
    exact compactShift0_0_entry0 c d e
  · conv_rhs => dsimp only [compactShift0_0, polyCoeff]
    exact compactShift0_0_entry1 c d e
  · conv_rhs => dsimp only [compactShift0_0, polyCoeff]
    exact compactShift0_0_entry2 c d e
  · conv_rhs => dsimp only [compactShift0_0, polyCoeff]
    exact compactShift0_0_entry3 c d e
  · conv_rhs => dsimp only [compactShift0_0, polyCoeff]
    exact compactShift0_0_entry4 c d e
  · conv_rhs => dsimp only [compactShift0_0, polyCoeff]
    exact compactShift0_0_entry5 c d e

def compactShift0_1 (c d e : ℝ) : List ℝ :=
  [((c * ((c * ((c * ((c * 95) + ((d * 255) + (e * 125)))) + ((d * ((d * 275) + (e * 270))) + (e * (e * 80))))) + ((d * ((d * ((d * 135) + (e * 200))) + (e * (e * 125)))) + (e * (e * (e * 30)))))) + ((d * ((d * ((d * ((d * 25) + (e * 50))) + (e * (e * 50)))) + (e * (e * (e * 25))))) + (e * (e * (e * (e * 5)))))),
   ((c * ((c * ((c * 480) + ((d * 960) + (e * 475)))) + ((d * ((d * 680) + (e * 675))) + (e * (e * 200))))) + ((d * ((d * ((d * 165) + (e * 245))) + (e * (e * 150)))) + (e * (e * (e * 35))))),
   ((c * ((c * 920) + ((d * 1225) + (e * 610)))) + ((d * ((d * 430) + (e * 430))) + (e * (e * 125)))),
   ((c * 795) + ((d * 530) + (e * 265))),
   265]

private theorem compactShift0_1_entry0 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff1 (basePoly0 c d e)) 0 = ((c * ((c * ((c * ((c * 95) + ((d * 255) + (e * 125)))) + ((d * ((d * 275) + (e * 270))) + (e * (e * 80))))) + ((d * ((d * ((d * 135) + (e * 200))) + (e * (e * 125)))) + (e * (e * (e * 30)))))) + ((d * ((d * ((d * ((d * 25) + (e * 50))) + (e * (e * 50)))) + (e * (e * (e * 25))))) + (e * (e * (e * (e * 5)))))) := by
  dsimp only [polyShiftCoeff1, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_1_entry1 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff1 (basePoly0 c d e)) 1 = ((c * ((c * ((c * 480) + ((d * 960) + (e * 475)))) + ((d * ((d * 680) + (e * 675))) + (e * (e * 200))))) + ((d * ((d * ((d * 165) + (e * 245))) + (e * (e * 150)))) + (e * (e * (e * 35))))) := by
  dsimp only [polyShiftCoeff1, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_1_entry2 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff1 (basePoly0 c d e)) 2 = ((c * ((c * 920) + ((d * 1225) + (e * 610)))) + ((d * ((d * 430) + (e * 430))) + (e * (e * 125)))) := by
  dsimp only [polyShiftCoeff1, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_1_entry3 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff1 (basePoly0 c d e)) 3 = ((c * 795) + ((d * 530) + (e * 265))) := by
  dsimp only [polyShiftCoeff1, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_1_entry4 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff1 (basePoly0 c d e)) 4 = 265 := by
  dsimp only [polyShiftCoeff1, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_1_length (c d e : ℝ) :
    (polyShiftCoeff1 (basePoly0 c d e)).length = 5 := by
  dsimp only [polyShiftCoeff1, basePoly0, Matrix.cons_val]
  simp only [polyAdd_length, polyScale_length, polyMul_length_total,
    polyPow, List.length_cons, List.length_nil]
  norm_num

theorem compactShift0_1_eq (c d e : ℝ) :
    polyShiftCoeff1 (basePoly0 c d e) = compactShift0_1 c d e := by
  apply polyList_eq_of_coeff_n _ _ 5 (compactShift0_1_length c d e) (by rfl)
  apply forall_fin5
  · conv_rhs => dsimp only [compactShift0_1, polyCoeff]
    exact compactShift0_1_entry0 c d e
  · conv_rhs => dsimp only [compactShift0_1, polyCoeff]
    exact compactShift0_1_entry1 c d e
  · conv_rhs => dsimp only [compactShift0_1, polyCoeff]
    exact compactShift0_1_entry2 c d e
  · conv_rhs => dsimp only [compactShift0_1, polyCoeff]
    exact compactShift0_1_entry3 c d e
  · conv_rhs => dsimp only [compactShift0_1, polyCoeff]
    exact compactShift0_1_entry4 c d e

def compactShift0_2 (c d e : ℝ) : List ℝ :=
  [((c * ((c * ((c * 290) + ((d * 580) + (e * 290)))) + ((d * ((d * 410) + (e * 410))) + (e * (e * 120))))) + ((d * ((d * ((d * 100) + (e * 150))) + (e * (e * 90)))) + (e * (e * (e * 20))))),
   ((c * ((c * 1110) + ((d * 1480) + (e * 740)))) + ((d * ((d * 520) + (e * 520))) + (e * (e * 150)))),
   ((c * 1440) + ((d * 960) + (e * 480))),
   640]

private theorem compactShift0_2_entry0 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff2 (basePoly0 c d e)) 0 = ((c * ((c * ((c * 290) + ((d * 580) + (e * 290)))) + ((d * ((d * 410) + (e * 410))) + (e * (e * 120))))) + ((d * ((d * ((d * 100) + (e * 150))) + (e * (e * 90)))) + (e * (e * (e * 20))))) := by
  dsimp only [polyShiftCoeff2, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_2_entry1 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff2 (basePoly0 c d e)) 1 = ((c * ((c * 1110) + ((d * 1480) + (e * 740)))) + ((d * ((d * 520) + (e * 520))) + (e * (e * 150)))) := by
  dsimp only [polyShiftCoeff2, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_2_entry2 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff2 (basePoly0 c d e)) 2 = ((c * 1440) + ((d * 960) + (e * 480))) := by
  dsimp only [polyShiftCoeff2, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_2_entry3 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff2 (basePoly0 c d e)) 3 = 640 := by
  dsimp only [polyShiftCoeff2, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_2_length (c d e : ℝ) :
    (polyShiftCoeff2 (basePoly0 c d e)).length = 4 := by
  dsimp only [polyShiftCoeff2, basePoly0, Matrix.cons_val]
  simp only [polyAdd_length, polyScale_length, polyMul_length_total,
    polyPow, List.length_cons, List.length_nil]
  norm_num

theorem compactShift0_2_eq (c d e : ℝ) :
    polyShiftCoeff2 (basePoly0 c d e) = compactShift0_2 c d e := by
  apply polyList_eq_of_coeff_n _ _ 4 (compactShift0_2_length c d e) (by rfl)
  apply forall_fin4
  · conv_rhs => dsimp only [compactShift0_2, polyCoeff]
    exact compactShift0_2_entry0 c d e
  · conv_rhs => dsimp only [compactShift0_2, polyCoeff]
    exact compactShift0_2_entry1 c d e
  · conv_rhs => dsimp only [compactShift0_2, polyCoeff]
    exact compactShift0_2_entry2 c d e
  · conv_rhs => dsimp only [compactShift0_2, polyCoeff]
    exact compactShift0_2_entry3 c d e

def compactShift0_3 (c d e : ℝ) : List ℝ :=
  [((c * ((c * 450) + ((d * 600) + (e * 300)))) + ((d * ((d * 210) + (e * 210))) + (e * (e * 60)))),
   ((c * 1170) + ((d * 780) + (e * 390))),
   780]

private theorem compactShift0_3_entry0 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff3 (basePoly0 c d e)) 0 = ((c * ((c * 450) + ((d * 600) + (e * 300)))) + ((d * ((d * 210) + (e * 210))) + (e * (e * 60)))) := by
  dsimp only [polyShiftCoeff3, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_3_entry1 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff3 (basePoly0 c d e)) 1 = ((c * 1170) + ((d * 780) + (e * 390))) := by
  dsimp only [polyShiftCoeff3, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_3_entry2 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff3 (basePoly0 c d e)) 2 = 780 := by
  dsimp only [polyShiftCoeff3, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_3_length (c d e : ℝ) :
    (polyShiftCoeff3 (basePoly0 c d e)).length = 3 := by
  dsimp only [polyShiftCoeff3, basePoly0, Matrix.cons_val]
  simp only [polyAdd_length, polyScale_length, polyMul_length_total,
    polyPow, List.length_cons, List.length_nil]
  norm_num

theorem compactShift0_3_eq (c d e : ℝ) :
    polyShiftCoeff3 (basePoly0 c d e) = compactShift0_3 c d e := by
  apply polyList_eq_of_coeff_n _ _ 3 (compactShift0_3_length c d e) (by rfl)
  apply forall_fin3
  · conv_rhs => dsimp only [compactShift0_3, polyCoeff]
    exact compactShift0_3_entry0 c d e
  · conv_rhs => dsimp only [compactShift0_3, polyCoeff]
    exact compactShift0_3_entry1 c d e
  · conv_rhs => dsimp only [compactShift0_3, polyCoeff]
    exact compactShift0_3_entry2 c d e

def compactShift0_4 (c d e : ℝ) : List ℝ :=
  [((c * 360) + ((d * 240) + (e * 120))),
   480]

private theorem compactShift0_4_entry0 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff4 (basePoly0 c d e)) 0 = ((c * 360) + ((d * 240) + (e * 120))) := by
  dsimp only [polyShiftCoeff4, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_4_entry1 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff4 (basePoly0 c d e)) 1 = 480 := by
  dsimp only [polyShiftCoeff4, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactShift0_4_length (c d e : ℝ) :
    (polyShiftCoeff4 (basePoly0 c d e)).length = 2 := by
  dsimp only [polyShiftCoeff4, basePoly0, Matrix.cons_val]
  simp only [polyAdd_length, polyScale_length, polyMul_length_total,
    polyPow, List.length_cons, List.length_nil]
  norm_num

theorem compactShift0_4_eq (c d e : ℝ) :
    polyShiftCoeff4 (basePoly0 c d e) = compactShift0_4 c d e := by
  apply polyList_eq_of_coeff_n _ _ 2 (compactShift0_4_length c d e) (by rfl)
  apply forall_fin2
  · conv_rhs => dsimp only [compactShift0_4, polyCoeff]
    exact compactShift0_4_entry0 c d e
  · conv_rhs => dsimp only [compactShift0_4, polyCoeff]
    exact compactShift0_4_entry1 c d e

def compactShift0_5 (c d e : ℝ) : List ℝ :=
  [120]

private theorem compactShift0_5_entry0 (c d e : ℝ) :
    polyCoeff (polyShiftCoeff5 (basePoly0 c d e)) 0 = 120 := by
  rfl

private theorem compactShift0_5_length (c d e : ℝ) :
    (polyShiftCoeff5 (basePoly0 c d e)).length = 1 := by
  rfl

theorem compactShift0_5_eq (c d e : ℝ) :
    polyShiftCoeff5 (basePoly0 c d e) = compactShift0_5 c d e := by
  apply polyList_eq_of_coeff_n _ _ 1 (compactShift0_5_length c d e) (by rfl)
  apply forall_fin1
  · conv_rhs => dsimp only [compactShift0_5, polyCoeff]
    exact compactShift0_5_entry0 c d e

def compactGram0_0 (c d e : ℝ) : List ℝ :=
  [((c * ((c * 3) + ((d * 4) + (e * 2)))) + ((d * ((d * 2) + (e * 2))) + (e * (e * 1)))),
   ((c * 6) + ((d * 4) + (e * 2))),
   4]

private theorem compactGram0_0_entry0 (c d e : ℝ) :
    polyCoeff (polyGramPart0 (basePoly0 c d e)) 0 = ((c * ((c * 3) + ((d * 4) + (e * 2)))) + ((d * ((d * 2) + (e * 2))) + (e * (e * 1)))) := by
  dsimp only [polyGramPart0, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactGram0_0_entry1 (c d e : ℝ) :
    polyCoeff (polyGramPart0 (basePoly0 c d e)) 1 = ((c * 6) + ((d * 4) + (e * 2))) := by
  dsimp only [polyGramPart0, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactGram0_0_entry2 (c d e : ℝ) :
    polyCoeff (polyGramPart0 (basePoly0 c d e)) 2 = 4 := by
  dsimp only [polyGramPart0, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactGram0_0_length (c d e : ℝ) :
    (polyGramPart0 (basePoly0 c d e)).length = 3 := by
  dsimp only [polyGramPart0, basePoly0, Matrix.cons_val]
  simp only [polyAdd_length, polyScale_length, polyMul_length_total,
    polyPow, List.length_cons, List.length_nil]
  norm_num

theorem compactGram0_0_eq (c d e : ℝ) :
    polyGramPart0 (basePoly0 c d e) = compactGram0_0 c d e := by
  apply polyList_eq_of_coeff_n _ _ 3 (compactGram0_0_length c d e) (by rfl)
  apply forall_fin3
  · conv_rhs => dsimp only [compactGram0_0, polyCoeff]
    exact compactGram0_0_entry0 c d e
  · conv_rhs => dsimp only [compactGram0_0, polyCoeff]
    exact compactGram0_0_entry1 c d e
  · conv_rhs => dsimp only [compactGram0_0, polyCoeff]
    exact compactGram0_0_entry2 c d e

def compactGram0_1 (c d e : ℝ) : List ℝ :=
  [((c * ((c * 2) + ((d * 3) + (e * 1)))) + (d * ((d * 1) + (e * 1)))),
   ((c * 5) + ((d * 3) + (e * 1))),
   3]

private theorem compactGram0_1_entry0 (c d e : ℝ) :
    polyCoeff (polyGramPart1 (basePoly0 c d e)) 0 = ((c * ((c * 2) + ((d * 3) + (e * 1)))) + (d * ((d * 1) + (e * 1)))) := by
  dsimp only [polyGramPart1, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactGram0_1_entry1 (c d e : ℝ) :
    polyCoeff (polyGramPart1 (basePoly0 c d e)) 1 = ((c * 5) + ((d * 3) + (e * 1))) := by
  dsimp only [polyGramPart1, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactGram0_1_entry2 (c d e : ℝ) :
    polyCoeff (polyGramPart1 (basePoly0 c d e)) 2 = 3 := by
  dsimp only [polyGramPart1, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactGram0_1_length (c d e : ℝ) :
    (polyGramPart1 (basePoly0 c d e)).length = 3 := by
  dsimp only [polyGramPart1, basePoly0, Matrix.cons_val]
  simp only [polyAdd_length, polyScale_length, polyMul_length_total,
    polyPow, List.length_cons, List.length_nil]
  norm_num

theorem compactGram0_1_eq (c d e : ℝ) :
    polyGramPart1 (basePoly0 c d e) = compactGram0_1 c d e := by
  apply polyList_eq_of_coeff_n _ _ 3 (compactGram0_1_length c d e) (by rfl)
  apply forall_fin3
  · conv_rhs => dsimp only [compactGram0_1, polyCoeff]
    exact compactGram0_1_entry0 c d e
  · conv_rhs => dsimp only [compactGram0_1, polyCoeff]
    exact compactGram0_1_entry1 c d e
  · conv_rhs => dsimp only [compactGram0_1, polyCoeff]
    exact compactGram0_1_entry2 c d e

def compactGram0_2 (c d e : ℝ) : List ℝ :=
  [(c * ((c * 1) + ((d * 1) + (e * 1)))),
   ((c * 4) + ((d * 3) + (e * 2))),
   3]

private theorem compactGram0_2_entry0 (c d e : ℝ) :
    polyCoeff (polyGramPart2 (basePoly0 c d e)) 0 = (c * ((c * 1) + ((d * 1) + (e * 1)))) := by
  dsimp only [polyGramPart2, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactGram0_2_entry1 (c d e : ℝ) :
    polyCoeff (polyGramPart2 (basePoly0 c d e)) 1 = ((c * 4) + ((d * 3) + (e * 2))) := by
  dsimp only [polyGramPart2, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactGram0_2_entry2 (c d e : ℝ) :
    polyCoeff (polyGramPart2 (basePoly0 c d e)) 2 = 3 := by
  dsimp only [polyGramPart2, basePoly0, Matrix.cons_val]
  dsimp only [polyCoeff, polyAdd, polyScale, polyMul, polyPow, List.map]
  ring

private theorem compactGram0_2_length (c d e : ℝ) :
    (polyGramPart2 (basePoly0 c d e)).length = 3 := by
  dsimp only [polyGramPart2, basePoly0, Matrix.cons_val]
  simp only [polyAdd_length, polyScale_length, polyMul_length_total,
    polyPow, List.length_cons, List.length_nil]
  norm_num

theorem compactGram0_2_eq (c d e : ℝ) :
    polyGramPart2 (basePoly0 c d e) = compactGram0_2 c d e := by
  apply polyList_eq_of_coeff_n _ _ 3 (compactGram0_2_length c d e) (by rfl)
  apply forall_fin3
  · conv_rhs => dsimp only [compactGram0_2, polyCoeff]
    exact compactGram0_2_entry0 c d e
  · conv_rhs => dsimp only [compactGram0_2, polyCoeff]
    exact compactGram0_2_entry1 c d e
  · conv_rhs => dsimp only [compactGram0_2, polyCoeff]
    exact compactGram0_2_entry2 c d e

end MathAndTheory.GyiresCirculant5
