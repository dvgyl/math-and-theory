import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite likelihood-ratio comparisons and deletion ratios

All comparisons below are finite algebraic inequalities. In particular, the
cross-product statements remain meaningful when some individual weights vanish.
-/

namespace DominationULC

open scoped BigOperators

/-- A pointwise comparison on a finite rectangle can be summed without dividing
by any individual weight. -/
theorem rectangle_cross_mul
    {α β : Type*} (s : Finset α) (t : Finset β)
    (f g : α → ℝ) (f' g' : β → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ t, f i * g' j ≤ g i * f' j) :
    (∑ i ∈ s, f i) * (∑ j ∈ t, g' j) ≤
      (∑ i ∈ s, g i) * (∑ j ∈ t, f' j) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => h i hi j hj

/-- Monotone likelihood-ratio cross-products imply the corresponding lower-tail
cross-product comparison. This statement permits arbitrary zero weights. -/
theorem lowerTail_cross_mul
    {α : Type*} [LinearOrder α] (s : Finset α) (f g : α → ℝ) (L : α)
    (h : ∀ i ∈ s, ∀ j ∈ s, i < j → f i * g j ≤ g i * f j) :
    (∑ i ∈ s.filter (fun i => i ≤ L), f i) * (∑ i ∈ s, g i) ≤
      (∑ i ∈ s.filter (fun i => i ≤ L), g i) * (∑ i ∈ s, f i) := by
  classical
  let low := s.filter (fun i => i ≤ L)
  let high := s.filter (fun i => ¬ i ≤ L)
  have hc : (∑ i ∈ low, f i) * (∑ j ∈ high, g j) ≤
      (∑ i ∈ low, g i) * (∑ j ∈ high, f j) := by
    apply rectangle_cross_mul
    intro i hi j hj
    have hi' : i ∈ s ∧ i ≤ L := Finset.mem_filter.mp hi
    have hj' : j ∈ s ∧ ¬ j ≤ L := Finset.mem_filter.mp hj
    exact h i hi'.1 j hj'.1 (lt_of_le_of_lt hi'.2 (lt_of_not_ge hj'.2))
  have hf : (∑ i ∈ s, f i) = (∑ i ∈ low, f i) + (∑ i ∈ high, f i) := by
    simpa only [low, high] using
      (Finset.sum_filter_add_sum_filter_not s (fun i => i ≤ L) f).symm
  have hg : (∑ i ∈ s, g i) = (∑ i ∈ low, g i) + (∑ i ∈ high, g i) := by
    simpa only [low, high] using
      (Finset.sum_filter_add_sum_filter_not s (fun i => i ≤ L) g).symm
  change (∑ i ∈ low, f i) * (∑ i ∈ s, g i) ≤
    (∑ i ∈ low, g i) * (∑ i ∈ s, f i)
  rw [hf, hg]
  nlinarith

/-- The normalized form requires positivity only of the two total weights. -/
theorem lowerTail_normalized_mono
    {α : Type*} [LinearOrder α] (s : Finset α) (f g : α → ℝ) (L : α)
    (hf : 0 < ∑ i ∈ s, f i) (hg : 0 < ∑ i ∈ s, g i)
    (h : ∀ i ∈ s, ∀ j ∈ s, i < j → f i * g j ≤ g i * f j) :
    (∑ i ∈ s.filter (fun i => i ≤ L), f i) / (∑ i ∈ s, f i) ≤
      (∑ i ∈ s.filter (fun i => i ≤ L), g i) / (∑ i ∈ s, g i) := by
  exact (div_le_div_iff₀ hf hg).2 (lowerTail_cross_mul s f g L h)

/-- Conditional weights obtained from a fixed total reverse the likelihood-ratio
order of the coefficient sequences. -/
theorem conditional_lowerTail_cross_mul
    (s : Finset ℤ) (w q q' : ℤ → ℝ) (N L : ℤ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hq : ∀ u v : ℤ, u < v → q u * q' v ≥ q' u * q v) :
    (∑ i ∈ s.filter (fun i => i ≤ L), w i * q (N - i)) *
        (∑ i ∈ s, w i * q' (N - i)) ≤
      (∑ i ∈ s.filter (fun i => i ≤ L), w i * q' (N - i)) *
        (∑ i ∈ s, w i * q (N - i)) := by
  apply lowerTail_cross_mul
  intro i hi j hj hij
  have h := hq (N - j) (N - i) (by omega)
  have hp := mul_le_mul_of_nonneg_left h (mul_nonneg (hw i hi) (hw j hj))
  nlinarith only [hp]

/-- Increasing endpoint and interior deletion probabilities give an increasing
weighted deletion probability, provided interior deletion is at least as likely. -/
theorem deletion_mixture_mono
    {k E I E' I' : ℝ} (hk : 2 ≤ k)
    (hE : E ≤ E') (hI : I ≤ I') (hEI : E ≤ I) :
    (2 * E + (k - 2) * I) / k ≤
      (2 * E' + (k - 1) * I') / (k + 1) := by
  apply (div_le_div_iff₀ (by linarith : 0 < k) (by linarith : 0 < k + 1)).2
  have h₁ : 0 ≤ k * (E' - E) := mul_nonneg (by linarith) (sub_nonneg.mpr hE)
  have h₂ : 0 ≤ (k * (k - 1)) * (I' - I) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sub_nonneg.mpr hI)
  nlinarith

/-- The transition from two selected vertices to three does not need a fictitious
interior deletion probability for a two-element set. -/
theorem deletion_mixture_two_three
    {E₂ E₃ I₃ : ℝ} (hE : E₂ ≤ E₃) (hEI : E₃ ≤ I₃) :
    E₂ ≤ (2 * E₃ + I₃) / 3 := by
  linarith

/-- The weighted deletion comparison directly in unnormalized counts. This form
does not require any rank to be positive. -/
theorem deletion_mixture_cross_mul
    {k D D' e i e' i' : ℝ} (hk : 2 ≤ k) (hD' : 0 ≤ D')
    (he : e * D' ≤ e' * D) (hi : i * D' ≤ i' * D) (hei : e ≤ i) :
    (k + 1) * (2 * e + (k - 2) * i) * D' ≤
      k * (2 * e' + (k - 1) * i') * D := by
  have h₁ := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ 2 * k)
  have h₂ := mul_le_mul_of_nonneg_left hi
    (mul_nonneg (by linarith : 0 ≤ k) (by linarith : 0 ≤ k - 1))
  have h₃ := mul_le_mul_of_nonneg_right hei hD'
  nlinarith only [h₁, h₂, h₃]

theorem deletion_mixture_two_three_cross_mul
    {D₂ D₃ e₂ e₃ i₃ : ℝ} (hD₂ : 0 ≤ D₂)
    (he : e₂ * D₃ ≤ e₃ * D₂) (hei : e₃ ≤ i₃) :
    3 * e₂ * D₃ ≤ (2 * e₃ + i₃) * D₂ := by
  have h := mul_le_mul_of_nonneg_right hei hD₂
  nlinarith only [he, h]

/-- The general double-counting deletion identities convert monotonicity of
deletion probabilities directly to the unnormalized ultra-log-concavity
inequality. No coefficient is divided by, so vanishing ranks cause no issue. -/
theorem deletion_identities_ulc
    {n k dprev d dnext r rnext : ℝ}
    (hk : 0 ≤ k) (hd : 0 ≤ d) (hdnext : 0 ≤ dnext)
    (hprev : k * d * r = (n - k + 1) * dprev)
    (hnext : (k + 1) * dnext * rnext = (n - k) * d)
    (hr : r ≤ rnext) :
    (k + 1) * (n - k + 1) * dprev * dnext ≤ k * (n - k) * d ^ 2 := by
  have hfactor : 0 ≤ (k * d) * ((k + 1) * dnext) :=
    mul_nonneg (mul_nonneg hk hd) (mul_nonneg (by linarith) hdnext)
  calc
    (k + 1) * (n - k + 1) * dprev * dnext =
        ((k + 1) * dnext) * ((n - k + 1) * dprev) := by ring
    _ = ((k + 1) * dnext) * (k * d * r) := by rw [hprev]
    _ = (k * d) * ((k + 1) * dnext) * r := by ring
    _ ≤ (k * d) * ((k + 1) * dnext) * rnext :=
      mul_le_mul_of_nonneg_left hr hfactor
    _ = (k * d) * ((k + 1) * dnext * rnext) := by ring
    _ = (k * d) * ((n - k) * d) := by rw [hnext]
    _ = k * (n - k) * d ^ 2 := by ring

end DominationULC
