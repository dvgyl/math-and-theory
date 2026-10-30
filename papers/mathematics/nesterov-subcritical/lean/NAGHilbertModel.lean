import HilbertModel
import NAGConjugacy

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace DiscreteNesterov
open NesterovThresholdModel NesterovHilbert

def normalGradient (e : PowerExponent) (ε : ℝ) (x : Plane) : Plane :=
  (ε^2/4) • gradient e ε x

def blockScale (ε h : ℝ) : ℝ := h*ε/2

lemma blockScale_pos {ε h : ℝ} (he : 0<ε) (hh : 0<h) : 0<blockScale ε h := by
  unfold blockScale
  positivity
lemma blockScale_le {ε h : ℝ} (he : 0<ε) (hh0 : 0≤h) (hh1 : h≤1) :
    blockScale ε h≤ε := by
  unfold blockScale
  nlinarith
lemma blockScale_le_one {ε h : ℝ} (he : 0<ε) (he1 : ε≤1) (hh0 : 0≤h) (hh1 : h≤1) :
    blockScale ε h≤1 := (blockScale_le he hh0 hh1).trans he1

def discretePotential (e : PowerExponent) (ε h : ℕ → ℝ) : Hilbert → ℝ :=
  sumPotential (fun n => scalePotential (weight n) (blockScale (ε n) (h n)) (potential e (ε n)))
def discreteGradient (e : PowerExponent) (ε h : ℕ → ℝ) : Hilbert → Hilbert :=
  sumGradient (fun n => scaleGradient (weight n) (blockScale (ε n) (h n)) (gradient e (ε n)))

lemma discrete_block_bound (e : PowerExponent) {ε h : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (hh : ∀ n, 0<h n ∧ h n≤1) (n : ℕ) (x : Plane) :
    ‖scaleGradient (weight n) (blockScale (ε n) (h n)) (gradient e (ε n)) x‖≤3*weight n :=
  scale_bound (weight_pos n) (blockScale_pos (he n).1 (hh n).1).le
    (blockScale_le_one (he n).1 (he n).2 (hh n).1.le (hh n).2)
    (gradient_norm_le_three e (ε n)) x

lemma discrete_block_deriv (e : PowerExponent) {ε h : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (n : ℕ) (x : Plane) :
    HasGradientAt (scalePotential (weight n) (blockScale (ε n) (h n)) (potential e (ε n)))
      (scaleGradient (weight n) (blockScale (ε n) (h n)) (gradient e (ε n)) x) x :=
  scale_hasGradient (weight_pos n) (potential_hasGradientAt e (he n).1) x

lemma discrete_block_zero (e : PowerExponent) (ε h : ℕ → ℝ) (n : ℕ) :
    scalePotential (weight n) (blockScale (ε n) (h n)) (potential e (ε n)) 0=0 :=
  scale_zero (potential_zero e (ε n))

theorem discrete_hasGradient (e : PowerExponent) {ε h : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (hh : ∀ n, 0<h n ∧ h n≤1) (x : Hilbert) :
    HasGradientAt (discretePotential e ε h) (discreteGradient e ε h x) x :=
  sumPotential_hasGradient weight_bound_summable (discrete_block_deriv e he)
    (discrete_block_bound e he hh) (discrete_block_zero e ε h) x

theorem discrete_convex (e : PowerExponent) {ε h : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (hh : ∀ n, 0<h n ∧ h n≤1) :
    ConvexOn ℝ univ (discretePotential e ε h) :=
  sumPotential_convex weight_bound_summable (discrete_block_deriv e he)
    (discrete_block_bound e he hh) (discrete_block_zero e ε h)
    (fun n => scale_convex (potential_convex e (he n).1))

theorem discrete_lipschitz (e : PowerExponent) {ε h : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (hh : ∀ n, 0<h n ∧ h n≤1) :
    LipschitzWith 1 (discreteGradient e ε h) := by
  apply sumGradient_lipschitz weight_bound_summable (discrete_block_bound e he hh)
  intro n
  apply scale_lipschitz (weight_pos n) (blockScale_pos (he n).1 (hh n).1)
    (blockScale_le_one (he n).1 (he n).2 (hh n).1.le (hh n).2)
  intro x y
  apply (gradient_dist_le e (he n).1 x y).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact inv_anti₀ (blockScale_pos (he n).1 (hh n).1)
    (blockScale_le (he n).1 (hh n).1.le (hh n).2)

theorem discrete_nonneg (e : PowerExponent) {ε h : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (x : Hilbert) : 0≤discretePotential e ε h x :=
  sumPotential_nonneg (fun n => scale_nonneg (potential_nonneg e (he n).1)) x

theorem discrete_zero (e : PowerExponent) (ε h : ℕ → ℝ) :
    discretePotential e ε h (0 : Hilbert)=0 := sumPotential_zero (discrete_block_zero e ε h)

theorem discrete_gradient_bound (e : PowerExponent) {ε h : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (hh : ∀ n, 0<h n ∧ h n≤1) (x : Hilbert) :
    ‖discreteGradient e ε h x‖≤2 := by
  have hb := sumGradient_bound weight_bound_summable (discrete_block_bound e he hh) x
  rw [weight_bound_sum] at hb
  exact hb.trans (by norm_num)

lemma discrete_gradient_apply (e : PowerExponent) {ε h : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (hh : ∀ n, 0<h n ∧ h n≤1) (x : Hilbert) (n : ℕ) :
    discreteGradient e ε h x n=
      scaleGradient (weight n) (blockScale (ε n) (h n)) (gradient e (ε n)) (x n) :=
  sumGradient_apply weight_bound_summable (discrete_block_bound e he hh) x n

def normalizedCoordinate (n : ℕ) : Hilbert →L[ℝ] Plane :=
  (weight n)⁻¹ • coordinate n

lemma normalizedCoordinate_initial (n : ℕ) :
    normalizedCoordinate n (initialData (point 2 1))=point 2 1 := by
  simp [normalizedCoordinate, coordinate_apply, initialData_apply, smul_smul,
    ne_of_gt (weight_pos n)]

lemma normalizedCoordinate_gradient (e : PowerExponent) {ε h : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (hh : ∀ n, 0<h n ∧ h n≤1) (n : ℕ) (x : Hilbert) :
    normalizedCoordinate n (discreteGradient e ε h x)=
      (h n)^2 • normalGradient e (ε n) (normalizedCoordinate n x) := by
  change (weight n)⁻¹ • (discreteGradient e ε h x n)=_
  rw [discrete_gradient_apply e he hh]
  simp only [scaleGradient, blockScale, normalGradient, normalizedCoordinate,
    ContinuousLinearMap.smul_apply, coordinate_apply, smul_smul]
  congr 1
  field_simp [ne_of_gt (weight_pos n)]
  <;> ring

/-- Every block of the fixed-step Hilbert iteration is exactly a scaled planar
iteration. All parameters are fixed before any iterate is generated. -/
theorem discrete_iterate_coordinate {r : ℝ} (e : PowerExponent) {ε h : ℕ → ℝ}
    (he : ∀ n, 0<ε n ∧ ε n≤1) (hh : ∀ n, 0<h n ∧ h n≤1) (n k : ℕ) :
    nagX r 1 (discreteGradient e ε h) (initialData (point 2 1)) k n=
      weight n • nagX r (h n) (normalGradient e (ε n)) (point 2 1) k := by
  have hm := (nag_map (normalizedCoordinate n) r 1 (h n) (discreteGradient e ε h)
    (normalGradient e (ε n)) (initialData (point 2 1))
    (fun x => by simpa using normalizedCoordinate_gradient e he hh n x) k).1
  rw [normalizedCoordinate_initial] at hm
  have hs := congrArg (fun z : Plane => weight n • z) hm
  simpa [normalizedCoordinate, coordinate_apply, smul_smul, ne_of_gt (weight_pos n)] using hs

end DiscreteNesterov
