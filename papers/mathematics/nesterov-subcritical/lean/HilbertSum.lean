import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open Set Filter InnerProductSpace
open scoped Topology NNReal ENNReal

namespace NesterovHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev SumSpace (E : Type*) [NormedAddCommGroup E] := lp (fun _ : ℕ => E) 2

def coordinate (n : ℕ) : SumSpace E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun z => z n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun z => by simpa using lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) z n)

@[simp] lemma coordinate_apply (n : ℕ) (z : SumSpace E) : coordinate n z = z n := rfl

def sumPotential (f : ℕ → E → ℝ) (z : SumSpace E) : ℝ := ∑' n, f n (z n)

def sumGradient (g : ℕ → E → E) (z : SumSpace E) : SumSpace E :=
  ∑' n, lp.single 2 n (g n (z n))

lemma gradient_summable {g : ℕ → E → E} {u : ℕ → ℝ}
    (hu : Summable u) (hg : ∀ n x, ‖g n x‖ ≤ u n) (z : SumSpace E) :
    Summable (fun n => lp.single 2 n (g n (z n)) : ℕ → SumSpace E) := by
  apply Summable.of_norm_bounded u hu
  intro n
  simpa only [lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2)] using hg n (z n)

lemma sumGradient_apply {g : ℕ → E → E} {u : ℕ → ℝ}
    (hu : Summable u) (hg : ∀ n x, ‖g n x‖ ≤ u n) (z : SumSpace E) (n : ℕ) :
    sumGradient g z n = g n (z n) := by
  have h := (coordinate (E := E) n).map_tsum (gradient_summable hu hg z)
  change coordinate n (sumGradient g z) = g n (z n)
  rw [sumGradient, h]
  rw [tsum_eq_single n]
  · simp
  · intro b hb
    simp only [coordinate_apply, lp.coeFn_single, Pi.single_eq_of_ne hb.symm]

lemma single_gradient {f : E → ℝ} {g : E → E}
    (hf : ∀ x, HasGradientAt f (g x) x) (n : ℕ) (z : SumSpace E) :
    HasFDerivAt (fun z : SumSpace E => f (z n))
      (toDual ℝ (SumSpace E) (lp.single 2 n (g (z n)))) z := by
  have h := (hf (z n)).hasFDerivAt.comp z (coordinate (E := E) n).hasFDerivAt
  convert h using 1
  ext v
  simp [lp.inner_single_left]

lemma single_derivative_bound {g : ℕ → E → E} {u : ℕ → ℝ}
    (hg : ∀ n x, ‖g n x‖ ≤ u n) (n : ℕ) (z : SumSpace E) :
    ‖toDual ℝ (SumSpace E) (lp.single 2 n (g n (z n)))‖ ≤ u n := by
  simpa only [LinearIsometryEquiv.norm_map,
    lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2)] using hg n (z n)

lemma potential_summable {f : ℕ → E → ℝ} {g : ℕ → E → E} {u : ℕ → ℝ}
    (hu : Summable u) (hf : ∀ n x, HasGradientAt (f n) (g n x) x)
    (hg : ∀ n x, ‖g n x‖ ≤ u n) (hzero : ∀ n, f n 0 = 0) (z : SumSpace E) :
    Summable (fun n => f n (z n)) := by
  apply summable_of_summable_hasFDerivAt hu
    (fun n z => single_gradient (hf n) n z) (single_derivative_bound hg)
    (x₀ := (0 : SumSpace E))
  simpa [hzero] using (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))

theorem sumPotential_hasGradient {f : ℕ → E → ℝ} {g : ℕ → E → E} {u : ℕ → ℝ}
    (hu : Summable u) (hf : ∀ n x, HasGradientAt (f n) (g n x) x)
    (hg : ∀ n x, ‖g n x‖ ≤ u n) (hzero : ∀ n, f n 0 = 0) (z : SumSpace E) :
    HasGradientAt (sumPotential f) (sumGradient g z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h0 : Summable (fun n => f n ((0 : SumSpace E) n)) := by
    simpa [hzero] using (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))
  have h := hasFDerivAt_tsum hu (fun n z => single_gradient (hf n) n z)
    (single_derivative_bound hg) h0 z
  change HasFDerivAt (fun y : SumSpace E => ∑' n, f n (y n))
    ((toDual ℝ (SumSpace E)).toContinuousLinearEquiv
      (∑' n, lp.single 2 n (g n (z n)))) z
  rw [ContinuousLinearEquiv.map_tsum]
  exact h

lemma sumPotential_nonneg {f : ℕ → E → ℝ} (hf : ∀ n x, 0 ≤ f n x) (z : SumSpace E) :
    0 ≤ sumPotential f z := tsum_nonneg (fun n => hf n _)

lemma sumPotential_zero {f : ℕ → E → ℝ} (hf : ∀ n, f n 0 = 0) :
    sumPotential f (0 : SumSpace E) = 0 := by simp [sumPotential, hf]

theorem sumPotential_convex {f : ℕ → E → ℝ} {g : ℕ → E → E} {u : ℕ → ℝ}
    (hu : Summable u) (hf : ∀ n x, HasGradientAt (f n) (g n x) x)
    (hg : ∀ n x, ‖g n x‖ ≤ u n) (hzero : ∀ n, f n 0 = 0)
    (hc : ∀ n, ConvexOn ℝ univ (f n)) : ConvexOn ℝ univ (sumPotential f) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hx := potential_summable hu hf hg hzero x
  have hy := potential_summable hu hf hg hzero y
  have hz := potential_summable hu hf hg hzero (a • x + b • y)
  have hl := hz.tsum_le_tsum (fun n => (hc n).2 (mem_univ _) (mem_univ _) ha hb hab)
    ((hx.mul_left a).add (hy.mul_left b))
  simpa only [sumPotential, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Summable.tsum_add (hx.mul_left a) (hy.mul_left b), tsum_mul_left] using hl

lemma norm_sq_eq_tsum (z : SumSpace E) : ‖z‖^2 = ∑' n, ‖z n‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) z

lemma summable_norm_sq (z : SumSpace E) : Summable (fun n => ‖z n‖^2) := by
  simpa using (lp.memℓp z).summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)

theorem sumGradient_lipschitz {g : ℕ → E → E} {u : ℕ → ℝ}
    (hu : Summable u) (hg : ∀ n x, ‖g n x‖ ≤ u n)
    (hl : ∀ n, LipschitzWith 1 (g n)) : LipschitzWith 1 (sumGradient g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have hsq : ‖sumGradient g x - sumGradient g y‖^2 ≤ ‖x-y‖^2 := by
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
    apply (summable_norm_sq (sumGradient g x-sumGradient g y)).tsum_le_tsum
      (fun n => ?_) (summable_norm_sq (x-y))
    have h := (hl n).dist_le_mul (x n) (y n)
    simp only [NNReal.coe_one, one_mul, dist_eq_norm] at h
    simpa [sumGradient_apply hu hg] using pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [norm_nonneg (sumGradient g x-sumGradient g y), norm_nonneg (x-y)]

theorem sumGradient_bound {g : ℕ → E → E} {u : ℕ → ℝ}
    (hu : Summable u) (hg : ∀ n x, ‖g n x‖ ≤ u n) (z : SumSpace E) :
    ‖sumGradient g z‖ ≤ ∑' n, u n := by
  have hn : Summable (fun n => ‖(lp.single 2 n (g n (z n)) : SumSpace E)‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hu
    simpa only [lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2)] using hg n (z n)
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (fun n => by
      simpa only [lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2)] using hg n (z n)) hu)

end NesterovHilbert
