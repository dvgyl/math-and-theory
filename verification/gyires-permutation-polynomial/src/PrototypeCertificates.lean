module

public import PrototypeExpression

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficients

open SparsePolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def chamberOutput : Fin 3 → Polynomial :=
  ![[(144, 324), (216, 720), (240, 324), (324, 585), (360, 1080), (400, 324), (486, 180), (540, 1170), (600, 1512), (729, 12), (810, 450), (900, 2187), (1000, 576), (1215, 36), (1350, 1224), (1500, 1602), (2025, 189), (2250, 1386), (2500, 369), (3375, 318), (3750, 684), (5625, 279), (6250, 126), (9375, 126), (15625, 21)],
    [(144, 324), (216, 720), (240, 324), (324, 585), (360, 1080), (400, 324), (486, 180), (540, 1170), (600, 1512), (729, 12), (810, 450), (900, 2187), (1000, 576), (1215, 36), (1350, 1224), (1500, 1602), (2025, 189), (2250, 1386), (2500, 369), (3375, 318), (3750, 684), (5625, 279), (6250, 126), (9375, 126), (15625, 21)],
    [(144, 324), (216, 720), (240, 324), (324, 585), (360, 1080), (400, 324), (486, 180), (540, 1170), (600, 1512), (729, 12), (810, 450), (900, 2187), (1000, 576), (1215, 36), (1350, 1224), (1500, 1602), (2025, 189), (2250, 1386), (2500, 369), (3375, 318), (3750, 684), (5625, 279), (6250, 126), (9375, 126), (15625, 21)]]

theorem chamber_identity (k : Fin 3) : same (chamberInput k) (chamberOutput k) = true := by
  fin_cases k <;> decide +kernel

theorem chamber_coefficients_nonneg (k : Fin 3) : coeffsNonneg (chamberOutput k) = true := by
  fin_cases k <;> decide +kernel

theorem chamber_gap_nonneg (z : Fin 3 → ℝ) (hz : ∀ i, 0 ≤ z i) (k : Fin 3) :
    0 ≤ gapThree (chamberValues z k 0) (chamberValues z k 1) (chamberValues z k 2) := by
  rw [← eval_chamberInput, same_sound _ _ (chamber_identity k)]
  exact eval_nonneg_of_check _ (primeEvaluation_nonneg primes z hz) _ (chamber_coefficients_nonneg k)

end MathAndTheory.Gyires.PermutationCoefficients
