import GlobalGapRigidity

/-!
Concrete equality and endpoint examples for the new global inverse theorem.
The signed-sum minima are proved from the coefficient constructions.
-/

noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.GapRigidityExamples
open Breakthrough.GapFibers Breakthrough.GapCore
open Breakthrough.ExactSupportGap Breakthrough.GlobalGapRigidity

set_option maxHeartbeats 4000000

lemma saturated_core_eq {n : ℕ} {a r : ℝ}
    (hr : 0 ≤ r) (hra : 2*r < a) :
    gapCore (saturatedCoefficients n a r) (a-r) = Finset.univ.erase 0 := by
  classical
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [gapCore, saturatedCoefficients] <;> linarith
  · simp [gapCore, saturatedCoefficients] <;> linarith

lemma saturated_tail_eq {n : ℕ} {a r : ℝ}
    (hr : 0 ≤ r) (hra : 2*r < a) :
    gapTail (saturatedCoefficients n a r) (a-r) = {0} := by
  classical
  rw [gapTail, saturated_core_eq hr hra]
  ext i
  simp

lemma saturated_cap_residual_shape {n : ℕ} {a r : ℝ}
    (hr : 0 ≤ r) (hra : 2*r < a) :
    CapResidualShape (saturatedCoefficients n a r) (a-r) a := by
  classical
  unfold CapResidualShape
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [saturated_core_eq hr hra] at hi
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    revert hi0
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi0
      exact False.elim (hi0 rfl)
    · intro _
      simp [saturatedCoefficients]
  · rw [saturated_tail_eq hr hra]
    exact (Finset.card_filter_le _ _).trans (by simp)
  · rw [tailL1, saturated_tail_eq hr hra]
    simp [saturatedCoefficients]

/-- Every feasible odd saturated vector attains the sharp distance curve;
the support-gap value is established by the actual finite signed sum. -/
theorem saturated_inverse_equality {n : ℕ} (hn : Odd n) {a r : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : 2*r < a)
    (hvar : (n : ℝ)*a^2+r^2=1) :
    supportGap (saturatedCoefficients n a r) = a-r ∧
    (∑ i, saturatedCoefficients n a r i ^ 2) = 1 ∧
    (gapCore (saturatedCoefficients n a r) (a-r)).card = n ∧
    flatDistanceSq (saturatedCoefficients n a r) (a-r) =
      2-2*Real.sqrt (1-r^2) := by
  classical
  have hrle : r ≤ a := by linarith
  have hgap := supportGap_saturated hn ha hr hrle
  have hv : (∑ i, saturatedCoefficients n a r i ^ 2) = 1 := by
    rw [saturated_variance, hvar]
  have hn1 : 1 ≤ n := by
    have hm := Nat.odd_iff.mp hn
    omega
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hna := mul_le_mul_of_nonneg_right hn1r (sq_nonneg a)
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg r]
  have hc : ∀ i, 0 ≤ saturatedCoefficients n a r i := by
    intro i
    exact Fin.cases hr (fun _ => ha.le) i
  have hcap : ∀ i, saturatedCoefficients n a r i ≤ a := by
    intro i
    exact Fin.cases hrle (fun _ => le_rfl) i
  have hx : 0 < a-r := by linarith
  have hhalf : a < 2*(a-r) := by linarith
  have he := (actual_flat_distance_equality_iff
    (saturatedCoefficients n a r) hx ha.le ha1 hhalf hc hcap hv
    (saturated_gap_lower hn ha hr)).mpr (saturated_cap_residual_shape hr hra)
  refine ⟨hgap, hv, ?_, ?_⟩
  · rw [saturated_core_eq hr hra]
    simp
  · convert he using 2 <;> ring

/-- The unnormalized endpoint vector is `(2t,t,t,t)`. -/
def halfThresholdCoefficients (t : ℝ) : Fin 4 → ℝ :=
  Fin.cons (2*t) (fun _ : Fin 3 => t)

lemma halfThreshold_gap {t : ℝ} (ht : 0 < t) :
    supportGap (halfThresholdCoefficients t) = t := by
  apply supportGap_eq_of_gap_and_outcome
  · intro ω
    cases h0 : ω 0 <;> cases h1 : ω 1 <;>
      cases h2 : ω 2 <;> cases h3 : ω 3 <;>
      simp [rademacherSum, halfThresholdCoefficients, Fin.sum_univ_succ,
        rademacherSign, h0, h1, h2, h3] <;>
      ring_nf <;> simp [abs_mul, abs_of_nonneg ht.le] <;> linarith
  · refine ⟨Fin.cons true (fun _ => false), ?_⟩
    simp [rademacherSum, halfThresholdCoefficients, Fin.sum_univ_succ,
      rademacherSign, abs_of_nonneg ht.le]
    ring_nf
    simp [abs_of_nonneg ht.le]

/-- At the endpoint `gap = cap/2`, the actual gap core can have even size.
The quadratic normalization and all sixteen sign sums are checked. -/
theorem halfThreshold_normalized_counterexample :
    let t := 1/Real.sqrt 7
    let b := halfThresholdCoefficients t
    (∑ i, b i ^ 2) = 1 ∧
      (∀ i, 0 ≤ b i ∧ b i ≤ 2*t) ∧
      supportGap b = t ∧
      (gapCore b (supportGap b)).card = 4 ∧
      ¬ Odd (gapCore b (supportGap b)).card := by
  dsimp only
  have hs : (Real.sqrt 7)^2 = (7 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsp : 0 < Real.sqrt (7 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have ht : (0 : ℝ) < 1/Real.sqrt 7 := by positivity
  have hgap := halfThreshold_gap ht
  have hcore : gapCore (halfThresholdCoefficients (1/Real.sqrt 7))
      (supportGap (halfThresholdCoefficients (1/Real.sqrt 7))) = Finset.univ := by
    rw [hgap]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [gapCore, halfThresholdCoefficients, show
        1/Real.sqrt (7:ℝ) ≤ 2*(1/Real.sqrt 7) by linarith]
    · simp [gapCore, halfThresholdCoefficients]
  refine ⟨?_, ?_, hgap, ?_, ?_⟩
  · simp [halfThresholdCoefficients, Fin.sum_univ_succ]
    field_simp
    nlinarith only [hs]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [halfThresholdCoefficients, ht.le]
    · simp [halfThresholdCoefficients, ht.le,
        show 1/Real.sqrt (7:ℝ) ≤ 2*(1/Real.sqrt 7) by linarith]
  · rw [hcore]
    simp
  · rw [hcore]
    norm_num [Nat.odd_iff]

#print axioms saturated_inverse_equality
#print axioms halfThreshold_normalized_counterexample

end Breakthrough.GapRigidityExamples
