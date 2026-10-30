import BlockScaling
import PowerModel

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology NNReal ENNReal

namespace NesterovHilbert
open NesterovThresholdModel
abbrev Hilbert := SumSpace Plane

def hilbertPotential (e : PowerExponent) (ε : ℕ → ℝ) : Hilbert → ℝ :=
  sumPotential (fun n => scalePotential (weight n) (ε n) (potential e (ε n)))
def hilbertGradient (e : PowerExponent) (ε : ℕ → ℝ) : Hilbert → Hilbert :=
  sumGradient (fun n => scaleGradient (weight n) (ε n) (gradient e (ε n)))

lemma block_bound (e : PowerExponent) {ε : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (n : ℕ) (x : Plane) :
    ‖scaleGradient (weight n) (ε n) (gradient e (ε n)) x‖≤3*weight n :=
  scale_bound (weight_pos n) (he n).1.le (he n).2 (gradient_norm_le_three e (ε n)) x

lemma block_deriv (e : PowerExponent) {ε : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (n : ℕ) (x : Plane) :
    HasGradientAt (scalePotential (weight n) (ε n) (potential e (ε n)))
      (scaleGradient (weight n) (ε n) (gradient e (ε n)) x) x :=
  scale_hasGradient (weight_pos n) (potential_hasGradientAt e (he n).1) x

lemma block_zero (e : PowerExponent) (ε : ℕ → ℝ) (n : ℕ) :
    scalePotential (weight n) (ε n) (potential e (ε n)) 0=0 :=
  scale_zero (potential_zero e (ε n))

theorem hilbert_hasGradient (e : PowerExponent) {ε : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (x : Hilbert) :
    HasGradientAt (hilbertPotential e ε) (hilbertGradient e ε x) x :=
  sumPotential_hasGradient weight_bound_summable (block_deriv e he)
    (block_bound e he) (block_zero e ε) x

theorem hilbert_convex (e : PowerExponent) {ε : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) : ConvexOn ℝ univ (hilbertPotential e ε) :=
  sumPotential_convex weight_bound_summable (block_deriv e he)
    (block_bound e he) (block_zero e ε)
    (fun n => scale_convex (potential_convex e (he n).1))

theorem hilbert_lipschitz (e : PowerExponent) {ε : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) : LipschitzWith 1 (hilbertGradient e ε) :=
  sumGradient_lipschitz weight_bound_summable (block_bound e he)
    (fun n => scale_lipschitz (weight_pos n) (he n).1 (he n).2
      (gradient_dist_le e (he n).1))

theorem hilbert_nonneg (e : PowerExponent) {ε : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (x : Hilbert) : 0≤hilbertPotential e ε x :=
  sumPotential_nonneg (fun n => scale_nonneg (potential_nonneg e (he n).1)) x

theorem hilbert_zero (e : PowerExponent) (ε : ℕ → ℝ) :
    hilbertPotential e ε (0 : Hilbert)=0 := sumPotential_zero (block_zero e ε)

theorem hilbert_gradient_bound (e : PowerExponent) {ε : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (x : Hilbert) : ‖hilbertGradient e ε x‖≤2 := by
  have h := sumGradient_bound weight_bound_summable (block_bound e he) x
  rw [weight_bound_sum] at h
  exact h.trans (by norm_num)

lemma hilbert_gradient_apply (e : PowerExponent) {ε : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (x : Hilbert) (n : ℕ) :
    hilbertGradient e ε x n=scaleGradient (weight n) (ε n) (gradient e (ε n)) (x n) :=
  sumGradient_apply weight_bound_summable (block_bound e he) x n

end NesterovHilbert
