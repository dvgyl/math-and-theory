module

public import ScalarSixU
public import ScalarSixV
public import ScalarSixW
public import PowersFive
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def squareFive (k : Fin 3) : Polynomial :=
  squareJoin (apFive k) (cpFive k) (uSix k 5) (vSix k 5) (wSix k 5) (fpFive k)
    (SparsePolynomial.mul (SparsePolynomial.const ((-1 : ℤ)^5)) (fpFive k))

def gramFive (k : Fin 3) : Polynomial := gramJoin (fpFive k) (t1Five k) (t2Five k)

def gapFive : Fin 3 → Polynomial :=
  ![[(1024, 221045), (1536, 1595850), (2304, 5348375), (2560, 614600), (3456, 10590300), (3840, 3950950), (5184, 13480325), (5760, 11351300), (6400, 932750), (7776, 11381060), (8640, 18738750), (9600, 5592700), (11664, 6399375), (12960, 19364200), (14400, 14675725), (16000, 1271500), (17496, 2346850), (19440, 12959100), (21600, 21932750), (24000, 7180350), (26244, 528225), (29160, 5624250), (32400, 20465275), (36000, 17289500), (39366, 62700), (40000, 1470775), (43740, 1516700), (48600, 12223250), (54000, 23012300), (59049, 2420), (60000, 7329250), (65610, 223250), (72900, 4536575), (81000, 18242900), (90000, 15070025), (98415, 12100), (100000, 1239830), (109350, 947750), (121500, 8618050), (135000, 16418900), (150000, 5249900), (164025, 84925), (182250, 2273900), (202500, 10117600), (225000, 8915650), (250000, 767050), (273375, 267100), (303750, 3433350), (337500, 7717750), (375000, 2744650), (455625, 519500), (506250, 3492650), (562500, 3768800), (625000, 369050), (759375, 674470), (843750, 2388650), (937500, 1068650), (1265625, 593850), (1406250, 1050600), (1562500, 132825), (2109375, 351000), (2343750, 268050), (3515625, 134025), (3906250, 30050), (5859375, 30050), (9765625, 3005)],
    [(1024, 221045), (1536, 1229200), (2304, 3445950), (2560, 614600), (3456, 6281600), (3840, 3445950), (5184, 8025675), (5760, 9422400), (6400, 932750), (7776, 7288260), (8640, 16051350), (9600, 5683800), (11664, 4635850), (12960, 18220650), (14400, 15628925), (16000, 1271500), (17496, 1982300), (19440, 13907550), (21600, 25006300), (24000, 7603250), (26244, 523325), (29160, 6938050), (32400, 25093400), (36000, 19288800), (39366, 69900), (40000, 1470775), (43740, 2093300), (48600, 15918950), (54000, 27007550), (59049, 2420), (60000, 7694550), (65610, 314550), (72900, 6088350), (81000, 22452250), (90000, 16737400), (98415, 12100), (100000, 1239830), (109350, 1220500), (121500, 10938500), (135000, 19325950), (150000, 5551550), (164025, 84925), (182250, 2803850), (202500, 12393175), (225000, 10005700), (250000, 767050), (273375, 267100), (303750, 4103950), (337500, 8997700), (375000, 2906900), (455625, 519500), (506250, 3984200), (562500, 4125750), (625000, 369050), (759375, 674470), (843750, 2583350), (937500, 1101100), (1265625, 593850), (1406250, 1083050), (1562500, 132825), (2109375, 351000), (2343750, 268050), (3515625, 134025), (3906250, 30050), (5859375, 30050), (9765625, 3005)],
    [(1024, 221045), (1536, 1595850), (2304, 5348375), (2560, 981250), (3456, 10590300), (3840, 6745800), (5184, 13480325), (5760, 20419600), (6400, 2330175), (7776, 11381060), (8640, 35182550), (9600, 14661000), (11664, 6399375), (12960, 37541100), (14400, 39341425), (16000, 3560200), (17496, 2346850), (19440, 25437150), (21600, 58286550), (24000, 19876150), (26244, 528225), (29160, 10803700), (32400, 51660400), (36000, 46134150), (39366, 62700), (40000, 3707725), (43740, 2709100), (48600, 27761600), (54000, 57245300), (59049, 2420), (60000, 17997000), (65610, 341050), (72900, 8709975), (81000, 40649350), (90000, 35224400), (98415, 12100), (100000, 2749530), (109350, 1418950), (121500, 16331300), (135000, 35334550), (150000, 11315100), (164025, 84925), (182250, 3376150), (202500, 18967225), (225000, 18036250), (250000, 1480425), (273375, 267100), (303750, 5090900), (337500, 13799750), (375000, 4997150), (455625, 519500), (506250, 5009550), (562500, 6128875), (625000, 581800), (759375, 674470), (843750, 3209600), (937500, 1524200), (1265625, 593850), (1406250, 1293400), (1562500, 162875), (2109375, 351000), (2343750, 298100), (3515625, 134025), (3906250, 30050), (5859375, 30050), (9765625, 3005)]]

theorem gap_five_identity (k : Fin 3) :
    SparsePolynomial.same (gapJoin 5 (squareFive k) (gramFive k)) (gapFive k) = true := by
  fin_cases k <;> decide +kernel

theorem gap_five_coefficients (k : Fin 3) : SparsePolynomial.coeffsNonneg (gapFive k) = true := by
  fin_cases k <;> decide +kernel

theorem eval_squareFive (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (squareFive k) =
      permanentSquareExpr 5 (realA z k) (realB z k) (realC z k) := by
  apply eval_squareJoin
  · exact eval_apFive z k
  · exact eval_cpFive z k
  · simpa using eval_uSix z k 5 (by omega)
  · simpa using eval_vSix z k 5 (by omega)
  · simpa using eval_wSix z k 5 (by omega)
  · exact eval_fpFive z k
  · exact eval_signed_power (evaluator z) (fpFive k) 5 (realA z k*realC z k) (eval_fpFive z k)

theorem eval_gramFive (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (gramFive k) =
      gramExpr 5 (realA z k) (realB z k) (realC z k) :=
  eval_gramJoin (evaluator z) 5 (realA z k) (realB z k) (realC z k)
    (fpFive k) (t1Five k) (t2Five k) (eval_fpFive z k) (eval_t1Five z k) (eval_t2Five z k)

theorem eval_gapFive (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (gapFive k) =
      rawGap 5 (realA z k) (realB z k) (realC z k) := by
  rw [eval_of_same _ _ _ (gap_five_identity k)]
  exact eval_gapJoin (evaluator z) 5 (realA z k) (realB z k) (realC z k)
    (squareFive k) (gramFive k) (eval_squareFive z k) (eval_gramFive z k)

theorem chamber_five_nonneg (z : Fin 3 → ℝ) (hz : ∀ i, 0 ≤ z i) (k : Fin 3) :
    0 ≤ rawGap 5 (realA z k) (realB z k) (realC z k) := by
  rw [← eval_gapFive]
  exact SparsePolynomial.eval_nonneg_of_check _
    (SparsePolynomial.primeEvaluation_nonneg PermutationCoefficients.primes z hz) _ (gap_five_coefficients k)

theorem cycle_order_five_both_gram {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A := PermutationMatrixBridge.polynomialMatrix (finRotate 5) a b c
    dimensionConstant 5 * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      dimensionConstant 5 * (A.transpose*A).permanent ≤ A.permanent^2 := by
  apply both_gram_of_rawGap_nonneg 5 (by omega) ha hb hc
  exact rawGap_nonneg_of_chambers 5 chamber_five_nonneg ha hb hc

end MathAndTheory.Gyires.PermutationCoefficientStage
