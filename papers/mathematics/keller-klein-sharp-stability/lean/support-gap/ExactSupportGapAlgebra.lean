import AdversarialCentralGap
import Mathlib.Data.Finset.Max

/-!
Scalar closure and actual finite-law witnesses for the coefficient-cap
signed-partition discrepancy problem. No normal comparison theorem is used.
-/

noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.ExactSupportGap
open Breakthrough.AdversarialCentralGap

set_option maxHeartbeats 2000000

lemma core_margin_le_cap {k : ℕ} {a x V : ℝ}
    (hk : 0 < k) (ha : 0 ≤ a) (hx : 0 ≤ x) (hV : 0 ≤ V)
    (hvariance : 1 - (k : ℝ) * a ^ 2 ≤ V)
    (henergy : (k : ℝ) * (x + Real.sqrt V) ^ 2 ≤ 1 - V) :
    x + Real.sqrt V ≤ a := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsq : (x + Real.sqrt V) ^ 2 ≤ a ^ 2 := by
    apply (mul_le_mul_left hkR).mp
    exact henergy.trans (by linarith)
  exact (sq_le_sq₀ (add_nonneg hx (Real.sqrt_nonneg V)) ha).mp hsq

/-- The explicit cap closure of the actual core-variance inequality. -/
theorem variance_cap_closure {k n : ℕ} {a x V : ℝ}
    (hk : 0 < k) (hkn : k ≤ n) (ha : 0 ≤ a) (hx : 0 ≤ x) (hV : 0 ≤ V)
    (hvariance : 1 - (k : ℝ) * a ^ 2 ≤ V)
    (henergy : (k : ℝ) * (x + Real.sqrt V) ^ 2 ≤ 1 - V) :
    x ≤ a - Real.sqrt (1 - (n : ℝ) * a ^ 2) := by
  have hcap := core_margin_le_cap hk ha hx hV hvariance henergy
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hmul := mul_le_mul_of_nonneg_right hknR (sq_nonneg a)
  have hroot := Real.sqrt_le_sqrt (show 1 - (n : ℝ) * a ^ 2 ≤ V by linarith)
  linarith

/-- At the active saturated value, the core count and residual variance are
forced; this is an equality consequence of the actual energy inequality. -/
theorem variance_cap_equality {k n : ℕ} {a x V : ℝ}
    (hk : 0 < k) (hkn : k ≤ n) (ha : 0 < a) (hx : 0 ≤ x) (hV : 0 ≤ V)
    (hna : (n : ℝ) * a ^ 2 ≤ 1)
    (hvariance : 1 - (k : ℝ) * a ^ 2 ≤ V)
    (henergy : (k : ℝ) * (x + Real.sqrt V) ^ 2 ≤ 1 - V)
    (heq : x = a - Real.sqrt (1 - (n : ℝ) * a ^ 2)) :
    k = n ∧ V = 1 - (n : ℝ) * a ^ 2 := by
  have hcap := core_margin_le_cap hk ha.le hx hV hvariance henergy
  have hT : 0 ≤ 1 - (n : ℝ) * a ^ 2 := by linarith
  have hroot : Real.sqrt V ≤ Real.sqrt (1 - (n : ℝ) * a ^ 2) := by linarith
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg V)
    (Real.sqrt_nonneg (1 - (n : ℝ) * a ^ 2))).mpr hroot
  rw [Real.sq_sqrt hV, Real.sq_sqrt hT] at hsq
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hmul := mul_le_mul_of_nonneg_right hknR (sq_nonneg a)
  have hVe : V = 1 - (n : ℝ) * a ^ 2 := by linarith
  have hnkR : (n : ℝ) ≤ k := by
    apply (mul_le_mul_right (sq_pos_of_pos ha)).mp
    linarith
  have hnk : n ≤ k := by exact_mod_cast hnkR
  exact ⟨Nat.le_antisymm hkn hnk, hVe⟩

/-- The actual minimum of all complete signed sums, not a continuous or
relaxed partition objective. -/
def supportGap {N : ℕ} (coeff : Fin N → ℝ) : ℝ :=
  sInf (Set.range (fun ω : BoolCube N => |rademacherSum coeff ω|))

theorem supportGap_attained {N : ℕ} (coeff : Fin N → ℝ) :
    ∃ ω : BoolCube N, supportGap coeff = |rademacherSum coeff ω| ∧
      ∀ η : BoolCube N, supportGap coeff ≤ |rademacherSum coeff η| := by
  classical
  obtain ⟨ω, hω, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun η : BoolCube N => |rademacherSum coeff η|) (by simp)
  have hall : ∀ η : BoolCube N, |rademacherSum coeff ω| ≤ |rademacherSum coeff η| := by
    intro η
    exact hmin η (Finset.mem_univ η)
  have hleast : IsLeast (Set.range (fun η : BoolCube N => |rademacherSum coeff η|))
      |rademacherSum coeff ω| := by
    refine ⟨⟨ω, rfl⟩, ?_⟩
    rintro z ⟨η, rfl⟩
    exact hall η
  have heq : supportGap coeff = |rademacherSum coeff ω| := hleast.csInf_eq
  exact ⟨ω, heq, fun η => heq ▸ hall η⟩

theorem supportGap_nonneg {N : ℕ} (coeff : Fin N → ℝ) : 0 ≤ supportGap coeff := by
  obtain ⟨ω, heq, hmin⟩ := supportGap_attained coeff
  rw [heq]
  exact abs_nonneg _

theorem le_supportGap_iff {N : ℕ} (coeff : Fin N → ℝ) (x : ℝ) :
    x ≤ supportGap coeff ↔ ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω| := by
  obtain ⟨ω, heq, hmin⟩ := supportGap_attained coeff
  constructor
  · intro h η
    exact h.trans (hmin η)
  · intro h
    rw [heq]
    exact h ω

theorem supportGap_eq_of_gap_and_outcome {N : ℕ} (coeff : Fin N → ℝ) {x : ℝ}
    (hgap : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (houtcome : ∃ ω : BoolCube N, |rademacherSum coeff ω| = x) :
    supportGap coeff = x := by
  obtain ⟨ω, hω⟩ := houtcome
  apply le_antisymm
  · obtain ⟨η, heq, hmin⟩ := supportGap_attained coeff
    simpa [hω] using hmin ω
  · exact (le_supportGap_iff coeff x).mpr hgap

theorem supportGap_abs {N : ℕ} (coeff : Fin N → ℝ) :
    supportGap (fun i => |coeff i|) = supportGap coeff := by
  have habs := (le_supportGap_iff (fun i => |coeff i|)
    (supportGap (fun i => |coeff i|))).mp le_rfl
  have horig := (le_supportGap_iff coeff (supportGap coeff)).mp le_rfl
  apply le_antisymm
  · apply (le_supportGap_iff coeff _).mpr
    intro ω
    simpa only [rademacherSum_abs_flip] using habs (coefficientSignFlip coeff ω)
  · apply (le_supportGap_iff (fun i => |coeff i|) _).mpr
    intro ω
    have he := rademacherSum_abs_flip coeff (coefficientSignFlip coeff ω)
    rw [coefficientSignFlip_involutive coeff ω] at he
    rw [he]
    exact horig (coefficientSignFlip coeff ω)

lemma flat_gap_lower {n : ℕ} (hn : Odd n) {a : ℝ} (ha : 0 < a) :
    ∀ ω : BoolCube n, a ≤ |rademacherSum (fun _ : Fin n => a) ω| := by
  have hc : nonzeroCount Finset.univ (fun _ : Fin n => a) = n := by
    simp [nonzeroCount, ha.ne']
  have h := (no_central_outcome_iff Finset.univ (fun _ : Fin n => a) ha
    (fun i hi => ⟨ha.le, le_rfl⟩)).mpr
    ⟨fun i hi => Or.inr rfl, by simpa [hc] using hn⟩
  simpa [rademacherSum] using h

lemma flat_gap_outcome {n : ℕ} (hn : Odd n) {a : ℝ} (ha : 0 < a) :
    ∃ ω : BoolCube n, |rademacherSum (fun _ : Fin n => a) ω| = a := by
  obtain ⟨ω, hω⟩ := exists_balanced_signs Finset.univ (fun _ : Fin n => a) ha.le
    (fun i hi => ⟨ha.le, le_rfl⟩)
  have hlo := flat_gap_lower hn ha ω
  exact ⟨ω, le_antisymm (by simpa [rademacherSum] using hω) hlo⟩

theorem supportGap_flat {n : ℕ} (hn : Odd n) {a : ℝ} (ha : 0 < a) :
    supportGap (fun _ : Fin n => a) = a :=
  supportGap_eq_of_gap_and_outcome _ (flat_gap_lower hn ha) (flat_gap_outcome hn ha)

/-- A concrete saturated core, with the residual in coordinate zero. -/
def saturatedCoefficients (n : ℕ) (a r : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons r (fun _ : Fin n => a)

lemma saturated_sum {n : ℕ} (a r : ℝ) (ω : BoolCube (n + 1)) :
    rademacherSum (saturatedCoefficients n a r) ω =
      r * rademacherSign (ω 0) +
        rademacherSum (fun _ : Fin n => a) (fun i => ω i.succ) := by
  simp [rademacherSum, saturatedCoefficients, Fin.sum_univ_succ]

lemma saturated_variance (n : ℕ) (a r : ℝ) :
    (∑ i, saturatedCoefficients n a r i ^ 2) = (n : ℝ) * a ^ 2 + r ^ 2 := by
  simp [saturatedCoefficients, Fin.sum_univ_succ]
  ring

lemma saturated_gap_lower {n : ℕ} (hn : Odd n) {a r : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) :
    ∀ ω : BoolCube (n + 1), a - r ≤ |rademacherSum (saturatedCoefficients n a r) ω| := by
  intro ω
  rw [saturated_sum]
  have hflat := flat_gap_lower hn ha (fun i => ω i.succ)
  have htriangle := abs_add (r * rademacherSign (ω 0) +
    rademacherSum (fun _ : Fin n => a) (fun i => ω i.succ))
    (-(r * rademacherSign (ω 0)))
  have hres : |r * rademacherSign (ω 0)| = r := by
    cases hω : ω 0 <;> simp [rademacherSign, hr, abs_of_nonneg hr]
  have he : (r * rademacherSign (ω 0) +
      rademacherSum (fun _ : Fin n => a) (fun i => ω i.succ)) +
      -(r * rademacherSign (ω 0)) =
      rademacherSum (fun _ : Fin n => a) (fun i => ω i.succ) := by ring
  rw [he, abs_neg, hres] at htriangle
  linarith

lemma saturated_gap_outcome {n : ℕ} (hn : Odd n) {a r : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ a) :
    ∃ ω : BoolCube (n + 1), |rademacherSum (saturatedCoefficients n a r) ω| = a - r := by
  obtain ⟨η, hη⟩ := flat_gap_outcome hn ha
  rcases le_total 0 (rademacherSum (fun _ : Fin n => a) η) with hp | hm
  · rw [abs_of_nonneg hp] at hη
    refine ⟨Fin.cons false η, ?_⟩
    rw [saturated_sum]
    simp only [Fin.cons_zero, Fin.cons_succ, rademacherSign, Bool.false_eq_true,
      if_false, mul_neg_one]
    rw [hη]
    rw [abs_of_nonneg (by linarith : 0 ≤ -r + a)]
    ring
  · rw [abs_of_nonpos hm] at hη
    refine ⟨Fin.cons true η, ?_⟩
    rw [saturated_sum]
    simp only [Fin.cons_zero, Fin.cons_succ, rademacherSign, if_true, mul_one]
    rw [abs_of_nonpos (by linarith : r + rademacherSum (fun _ : Fin n => a) η ≤ 0)]
    linarith

theorem supportGap_saturated {n : ℕ} (hn : Odd n) {a r : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ a) :
    supportGap (saturatedCoefficients n a r) = a - r :=
  supportGap_eq_of_gap_and_outcome _ (saturated_gap_lower hn ha hr)
    (saturated_gap_outcome hn ha hr hra)

lemma odd_core_count_le {k n : ℕ} (hk : Odd k) (hn : Odd n) {x : ℝ}
    (hx : 1 / Real.sqrt ((n : ℝ) + 2) < x)
    (henergy : (k : ℝ) * x ^ 2 ≤ 1) : k ≤ n := by
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hroot : 0 < Real.sqrt ((n : ℝ) + 2) := Real.sqrt_pos.2 hden
  have hprod : 1 < x * Real.sqrt ((n : ℝ) + 2) := (div_lt_iff₀ hroot).mp hx
  have hprodSq : 1 < (x * Real.sqrt ((n : ℝ) + 2)) ^ 2 := by nlinarith
  rw [mul_pow, Real.sq_sqrt hden.le] at hprodSq
  have hlt : k < n + 2 := by
    by_contra h
    have hnk : n + 2 ≤ k := Nat.le_of_not_gt h
    have hnkR : (n : ℝ) + 2 ≤ k := by exact_mod_cast hnk
    have hmul := mul_le_mul_of_nonneg_right hnkR (sq_nonneg x)
    nlinarith
  have hkmod := Nat.odd_iff.mp hk
  have hnmod := Nat.odd_iff.mp hn
  omega

lemma cap_lt_twice_of_above_step {n : ℕ} (hn : Odd n) {a x : ℝ}
    (ha : 0 ≤ a) (hna : (n : ℝ) * a ^ 2 ≤ 1)
    (hx : 1 / Real.sqrt ((n : ℝ) + 2) < x) : a < 2 * x := by
  have hnpos : 0 < n := by
    have hmod := Nat.odd_iff.mp hn
    omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hmul := mul_le_mul_of_nonneg_right hnR (sq_nonneg a)
  have haSq : a ^ 2 ≤ 1 := by nlinarith
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hroot : 0 < Real.sqrt ((n : ℝ) + 2) := Real.sqrt_pos.2 hden
  have hxprod : 1 < x * Real.sqrt ((n : ℝ) + 2) := (div_lt_iff₀ hroot).mp hx
  have haProdSq : (a * Real.sqrt ((n : ℝ) + 2)) ^ 2 ≤ 3 := by
    rw [mul_pow, Real.sq_sqrt hden.le]
    nlinarith
  have haProd : a * Real.sqrt ((n : ℝ) + 2) < 2 := by nlinarith
  apply (mul_lt_mul_right hroot).mp
  linarith

lemma flat_normalized {m : ℕ} (hm : 0 < m) :
    (∑ _i : Fin m, (1 / Real.sqrt (m : ℝ)) ^ 2) = 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    div_pow, one_pow, Real.sq_sqrt hmR.le]
  exact mul_div_cancel₀ 1 hmR.ne'

lemma flat_coefficient_le_cap {m : ℕ} (hm : 0 < m) {a : ℝ}
    (ha : 0 ≤ a) (hmul : 1 ≤ (m : ℝ) * a ^ 2) :
    1 / Real.sqrt (m : ℝ) ≤ a := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hroot := Real.sqrt_pos.2 hmR
  apply (div_le_iff₀ hroot).mpr
  have hp : 0 ≤ a * Real.sqrt (m : ℝ) := mul_nonneg ha hroot.le
  have he : (a * Real.sqrt (m : ℝ)) ^ 2 = a ^ 2 * m := by
    rw [mul_pow, Real.sq_sqrt hmR.le]
  nlinarith

/-- Both entries of the candidate formula are realized whenever that branch
is active. This statement gives actual normalized finite coefficient vectors. -/
theorem cap_formula_attained {n : ℕ} (hn : Odd n) {a : ℝ} (ha : 0 < a)
    (hna : (n : ℝ) * a ^ 2 ≤ 1) (hn2a : 1 ≤ ((n : ℝ) + 2) * a ^ 2) :
    ∃ N : ℕ, ∃ coeff : Fin N → ℝ,
      (∀ i, 0 ≤ coeff i ∧ coeff i ≤ a) ∧ (∑ i, coeff i ^ 2 = 1) ∧
      supportGap coeff = max (1 / Real.sqrt ((n : ℝ) + 2))
        (a - Real.sqrt (1 - (n : ℝ) * a ^ 2)) := by
  have hlambda : 0 < 1 / Real.sqrt ((n : ℝ) + 2) := by positivity
  by_cases hb : a - Real.sqrt (1 - (n : ℝ) * a ^ 2) ≤
      1 / Real.sqrt ((n : ℝ) + 2)
  · have hodd : Odd (n + 2) := by
      have hmod := Nat.odd_iff.mp hn
      apply Nat.odd_iff.mpr
      omega
    refine ⟨n + 2, fun _ => 1 / Real.sqrt ((n : ℝ) + 2), ?_, ?_, ?_⟩
    · intro i
      refine ⟨hlambda.le, ?_⟩
      have h := flat_coefficient_le_cap (show 0 < n + 2 by omega) ha.le
        (show 1 ≤ ((n + 2 : ℕ) : ℝ) * a ^ 2 by exact_mod_cast hn2a)
      simpa only [Nat.cast_add, Nat.cast_ofNat] using h
    · have h := flat_normalized (show 0 < n + 2 by omega)
      simpa only [Nat.cast_add, Nat.cast_ofNat] using h
    · rw [supportGap_flat hodd hlambda, max_eq_left hb]
  · have hg : 1 / Real.sqrt ((n : ℝ) + 2) ≤
        a - Real.sqrt (1 - (n : ℝ) * a ^ 2) := (not_le.mp hb).le
    have hr : 0 ≤ Real.sqrt (1 - (n : ℝ) * a ^ 2) := Real.sqrt_nonneg _
    have hra : Real.sqrt (1 - (n : ℝ) * a ^ 2) ≤ a := by linarith
    refine ⟨n + 1, saturatedCoefficients n a (Real.sqrt (1 - (n : ℝ) * a ^ 2)),
      ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [saturatedCoefficients] using And.intro hr hra
      · simp [saturatedCoefficients, ha.le]
    · rw [saturated_variance, Real.sq_sqrt (by linarith : 0 ≤ 1 - (n : ℝ) * a ^ 2)]
      ring
    · rw [supportGap_saturated hn ha hr hra, max_eq_right hg]

#print axioms variance_cap_closure
#print axioms variance_cap_equality
#print axioms supportGap_attained
#print axioms supportGap_flat
#print axioms supportGap_saturated
#print axioms cap_formula_attained

end Breakthrough.ExactSupportGap
