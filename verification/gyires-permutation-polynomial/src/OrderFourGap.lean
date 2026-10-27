module

public import OrderFourU
public import OrderFourV
public import OrderFourW
public import OrderFourPowers
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientStage

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficientRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def squareFour (k : Fin 3) : Polynomial :=
  squareJoin (apFour k) (cpFour k) (uData k 4) (vData k 4) (wData k 4) (fpFour k)
    (SparsePolynomial.mul (SparsePolynomial.const ((-1 : ℤ)^4)) (fpFour k))

def gramFour (k : Fin 3) : Polynomial := gramJoin (fpFour k) (t1Four k) (t2Four k)

def gapFour : Fin 3 → Polynomial :=
  ![[(256, 5544), (384, 29568), (576, 77088), (640, 14784), (864, 118080), (960, 68736), (1296, 111232), (1440, 146304), (1600, 25344), (1944, 63744), (2160, 175296), (2400, 107712), (2916, 21056), (3240, 123136), (3600, 200096), (4000, 33984), (4374, 3456), (4860, 49792), (5400, 202368), (6000, 127296), (6561, 160), (7290, 10240), (8100, 116160), (9000, 197120), (10000, 30352), (10935, 640), (12150, 34688), (13500, 155264), (15000, 93696), (18225, 3904), (20250, 60928), (22500, 111648), (25000, 17728), (30375, 9472), (33750, 61120), (37500, 42880), (50625, 13440), (56250, 36992), (62500, 7040), (84375, 11840), (93750, 12608), (140625, 6304), (156250, 1856), (234375, 1856), (390625, 232)],
    [(256, 5544), (384, 29568), (576, 85440), (640, 14784), (864, 156672), (960, 85440), (1296, 187648), (1440, 235008), (1600, 25344), (1944, 146432), (2160, 375296), (2400, 146304), (2916, 72192), (3240, 366080), (3600, 351680), (4000, 33984), (4374, 20480), (4860, 216576), (5400, 454656), (6000, 164032), (6561, 2560), (7290, 71680), (8100, 333824), (9000, 315904), (10000, 30352), (10935, 10240), (12150, 132096), (13500, 306688), (15000, 116352), (18225, 22016), (20250, 151040), (22500, 169792), (25000, 17728), (30375, 30208), (33750, 111616), (37500, 52544), (50625, 27904), (56250, 52224), (62500, 7040), (84375, 17408), (93750, 14464), (140625, 7232), (156250, 1856), (234375, 1856), (390625, 232)],
    [(256, 5544), (384, 29568), (576, 77088), (640, 14784), (864, 118080), (960, 85440), (1296, 111232), (1440, 207936), (1600, 33696), (1944, 63744), (2160, 269632), (2400, 169344), (2916, 21056), (3240, 195584), (3600, 341600), (4000, 45504), (4374, 3456), (4860, 76544), (5400, 347264), (6000, 191936), (6561, 160), (7290, 13952), (8100, 183040), (9000, 308608), (10000, 39088), (10935, 640), (12150, 45824), (13500, 232576), (15000, 132736), (18225, 3904), (20250, 79872), (22500, 160736), (25000, 21824), (30375, 9472), (33750, 80448), (37500, 56640), (50625, 13440), (56250, 46656), (62500, 7968), (84375, 11840), (93750, 14464), (140625, 6304), (156250, 1856), (234375, 1856), (390625, 232)]]

theorem gap_four_identity (k : Fin 3) :
    SparsePolynomial.same (gapJoin 4 (squareFour k) (gramFour k)) (gapFour k) = true := by
  fin_cases k <;> decide +kernel

theorem gap_four_coefficients (k : Fin 3) : SparsePolynomial.coeffsNonneg (gapFour k) = true := by
  fin_cases k <;> decide +kernel

theorem eval_squareFour (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (squareFour k) =
      permanentSquareExpr 4 (realA z k) (realB z k) (realC z k) := by
  apply eval_squareJoin
  · exact eval_apFour z k
  · exact eval_cpFour z k
  · simpa using eval_uData z k 4 (by omega)
  · simpa using eval_vData z k 4 (by omega)
  · simpa using eval_wData z k 4 (by omega)
  · exact eval_fpFour z k
  · exact eval_signed_power (evaluator z) (fpFour k) 4 (realA z k*realC z k) (eval_fpFour z k)

theorem eval_gramFour (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (gramFour k) =
      gramExpr 4 (realA z k) (realB z k) (realC z k) :=
  eval_gramJoin (evaluator z) 4 (realA z k) (realB z k) (realC z k)
    (fpFour k) (t1Four k) (t2Four k) (eval_fpFour z k) (eval_t1Four z k) (eval_t2Four z k)

theorem eval_gapFour (z : Fin 3 → ℝ) (k : Fin 3) :
    SparsePolynomial.eval (evaluator z) (gapFour k) =
      rawGap 4 (realA z k) (realB z k) (realC z k) := by
  rw [eval_of_same _ _ _ (gap_four_identity k)]
  exact eval_gapJoin (evaluator z) 4 (realA z k) (realB z k) (realC z k)
    (squareFour k) (gramFour k) (eval_squareFour z k) (eval_gramFour z k)

theorem chamber_four_nonneg (z : Fin 3 → ℝ) (hz : ∀ i, 0 ≤ z i) (k : Fin 3) :
    0 ≤ rawGap 4 (realA z k) (realB z k) (realC z k) := by
  rw [← eval_gapFour]
  exact SparsePolynomial.eval_nonneg_of_check _
    (SparsePolynomial.primeEvaluation_nonneg PermutationCoefficients.primes z hz) _ (gap_four_coefficients k)

theorem cycle_order_four_both_gram {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A := PermutationMatrixBridge.polynomialMatrix (finRotate 4) a b c
    dimensionConstant 4 * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      dimensionConstant 4 * (A.transpose*A).permanent ≤ A.permanent^2 := by
  apply both_gram_of_rawGap_nonneg 4 (by omega) ha hb hc
  exact rawGap_nonneg_of_chambers 4 chamber_four_nonneg ha hb hc

end MathAndTheory.Gyires.PermutationCoefficientStage
