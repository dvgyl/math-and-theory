import MilneRefinement

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

def successBudgetRadius (p : ℝ) : ℝ := (1-p)/p

def successOptimalRadius (c R : ℝ) : ℝ :=
  if c ≤ 2/3 then min R (optimalFilterLength c) else R

def successEnvelopeSq (c p : ℝ) : ℝ :=
  steeringQuadratic c (successOptimalRadius c (successBudgetRadius p))

def successActivationPolynomial (c p : ℝ) : ℝ :=
  2-2*(1+p)*c+(2*p-1)*c^2

def successCriticalCenter (p : ℝ) : ℝ :=
  2/(1+p+Real.sqrt ((1-p)^2+2))

theorem successBudgetRadius_bounds {p : ℝ} (hp0 : 1/2 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ successBudgetRadius p ∧ successBudgetRadius p ≤ 1 := by
  have hp : 0 < p := by linarith
  constructor
  · exact div_nonneg (by linarith) (le_of_lt hp)
  · apply (div_le_iff₀ hp).mpr
    linarith

theorem successBudgetRadius_lt_one {p : ℝ} (hp : 1/2 < p) :
    successBudgetRadius p < 1 := by
  apply (div_lt_iff₀ (show 0 < p by linarith)).mpr
  linarith

theorem success_radius_iff {p r : ℝ} (hp : 0 < p) :
    p*(1+r) ≤ 1 ↔ r ≤ successBudgetRadius p := by
  rw [successBudgetRadius,le_div_iff₀ hp]
  constructor <;> intro h <;> nlinarith

theorem steeringQuadratic_difference (c r s : ℝ) :
    steeringQuadratic c s-steeringQuadratic c r =
      (s-r)*(2*c*(1-c)-steeringDenominator c*(s+r)) := by
  unfold steeringQuadratic steeringDenominator
  ring

theorem steeringQuadratic_mono_before_vertex {c r s : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ 2/3) (hrs : r ≤ s)
    (hs : s ≤ optimalFilterLength c) :
    steeringQuadratic c r ≤ steeringQuadratic c s := by
  have hD := steeringDenominator_pos hc0 hc
  have hv : steeringDenominator c*optimalFilterLength c = c*(1-c) := by
    unfold optimalFilterLength
    field_simp
  have hsum : s+r ≤ 2*optimalFilterLength c := by linarith
  have hm := mul_le_mul_of_nonneg_left hsum (le_of_lt hD)
  have hcoef : 0 ≤ 2*c*(1-c)-steeringDenominator c*(s+r) := by nlinarith
  have h := mul_nonneg (sub_nonneg.mpr hrs) hcoef
  rw [← steeringQuadratic_difference] at h
  linarith

theorem steeringQuadratic_mono_large {c r s : ℝ}
    (hc : 2/3 ≤ c) (hc1 : c ≤ 1) (hr0 : 0 ≤ r)
    (hrs : r ≤ s) (hs1 : s ≤ 1) :
    steeringQuadratic c r ≤ steeringQuadratic c s := by
  have hsum0 : 0 ≤ s+r := by linarith
  have hsum1 : s+r ≤ 2 := by linarith
  have hcprod : 0 ≤ c*(1-c) := mul_nonneg (by linarith) (by linarith)
  have hcoef : 0 ≤ 2*c*(1-c)-steeringDenominator c*(s+r) := by
    by_cases hD : 0 ≤ steeringDenominator c
    · have hm := mul_le_mul_of_nonneg_left hsum1 hD
      unfold steeringDenominator at hm ⊢
      nlinarith
    · have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hD) hsum0
      nlinarith
  have h := mul_nonneg (sub_nonneg.mpr hrs) hcoef
  rw [← steeringQuadratic_difference] at h
  linarith

theorem successOptimalRadius_bounds {c R : ℝ}
    (hc0 : 0 ≤ c) (hR0 : 0 ≤ R) :
    0 ≤ successOptimalRadius c R ∧ successOptimalRadius c R ≤ R := by
  unfold successOptimalRadius
  split_ifs with hc
  · have hv := steering_vertex_in_unit_interval hc0 hc
    change 0 ≤ min R (c*(1-c)/steeringDenominator c) ∧ _
    exact ⟨le_min hR0 hv.1,min_le_left _ _⟩
  · exact ⟨hR0,le_rfl⟩

/-- Exact maximum on a closed, probability-limited radius interval. -/
theorem successOptimalRadius_maximizes {c R r : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hr0 : 0 ≤ r) (hrR : r ≤ R) :
    steeringQuadratic c r ≤ steeringQuadratic c (successOptimalRadius c R) := by
  unfold successOptimalRadius
  split_ifs with hc
  · by_cases hRv : R ≤ optimalFilterLength c
    · rw [min_eq_left hRv]
      exact steeringQuadratic_mono_before_vertex hc0 hc hrR hRv
    · rw [min_eq_right (le_of_not_ge hRv)]
      have h := steeringQuadratic_small hc0 hc r
      have hv := steering_vertex_attains hc0 hc
      change steeringQuadratic c (optimalFilterLength c) = steeringEnvelopeSq c at hv
      rw [hv,steeringEnvelopeSq,if_pos hc]
      exact h
  · exact steeringQuadratic_mono_large (le_of_not_ge hc) hc1 hr0 hrR hR1

theorem steering_activation_factorization (c r : ℝ) :
    steeringQuadratic c r-1 =
      (1-r)*(steeringDenominator c*r+2-4*c+c^2) := by
  unfold steeringQuadratic steeringDenominator
  ring

theorem success_endpoint_activation_identity {p : ℝ} (hp : p ≠ 0) (c : ℝ) :
    steeringQuadratic c (successBudgetRadius p)-1 =
      (2*p-1)*successActivationPolynomial c p/p^2 := by
  unfold steeringQuadratic successBudgetRadius successActivationPolynomial
  field_simp
  ring

theorem successActivationPolynomial_iff_center {c p : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hp0 : 1/2 ≤ p) (hp1 : p ≤ 1) :
    0 < successActivationPolynomial c p ↔ c < successCriticalCenter p := by
  let s := Real.sqrt ((1-p)^2+2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2 = (1-p)^2+2 := Real.sq_sqrt (by nlinarith [sq_nonneg (1-p)])
  have hs1 : 1 ≤ s := by nlinarith
  have hden : 0 < 1+p+s := by linarith
  have hsmall : 1+p-s ≤ 1 := by linarith
  have hm := mul_le_mul_of_nonneg_right hsmall hc0
  have hsecond : 0 < 2-(1+p-s)*c := by nlinarith
  have hid : 2*successActivationPolynomial c p =
      (2-(1+p+s)*c)*(2-(1+p-s)*c) := by
    calc
      2*successActivationPolynomial c p = 4-4*(1+p)*c+((1+p)^2-s^2)*c^2 := by
        rw [hs2]
        unfold successActivationPolynomial
        ring
      _ = (2-(1+p+s)*c)*(2-(1+p-s)*c) := by ring
  change 0 < successActivationPolynomial c p ↔ c < 2/(1+p+s)
  rw [lt_div_iff₀ hden]
  constructor
  · intro h
    have hp : 0 < (2-(1+p+s)*c)*(2-(1+p-s)*c) := by nlinarith [hid]
    have hf : 0 < 2-(1+p+s)*c := (mul_pos_iff_of_pos_right hsecond).mp hp
    nlinarith
  · intro h
    have hf : 0 < 2-(1+p+s)*c := by nlinarith
    have hp := mul_pos hf hsecond
    nlinarith [hid]

/-- Exact activation condition on the radius cap.  The endpoint p=1/2
uses the interior vertex, because H(c,1)=1 for every c. -/
theorem success_violation_exists_iff_polynomial {c p : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hp0 : 1/2 ≤ p) (hp1 : p ≤ 1) :
    (∃ r : ℝ, 0 ≤ r ∧ r ≤ successBudgetRadius p ∧
      1 < steeringQuadratic c r) ↔ 0 < successActivationPolynomial c p := by
  have hp : 0 < p := by linarith
  have hR := successBudgetRadius_bounds hp0 hp1
  constructor
  · rintro ⟨r,hr0,hrR,hviol⟩
    have hr1 : r ≤ 1 := hrR.trans hR.2
    have hc : c < 2/3 := by
      by_contra hn
      have h := steeringQuadratic_large (le_of_not_gt hn) hc1 hr0 hr1
      linarith
    have hD := steeringDenominator_pos hc0 (le_of_lt hc)
    have hid := steering_activation_factorization c r
    have hlin : 0 < steeringDenominator c*r+2-4*c+c^2 := by
      by_contra hn
      have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr1)
        (le_of_not_gt hn)
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hrR (le_of_lt hD)
    have hlinR : 0 < steeringDenominator c*successBudgetRadius p+2-4*c+c^2 := by
      linarith
    have heq : successActivationPolynomial c p =
        p*(steeringDenominator c*successBudgetRadius p+2-4*c+c^2) := by
      unfold successActivationPolynomial steeringDenominator successBudgetRadius
      field_simp
      ring
    rw [heq]
    exact mul_pos hp hlinR
  · intro hg
    by_cases hhalf : p = 1/2
    · subst p
      have hc : c < 2/3 := by
        unfold successActivationPolynomial at hg
        nlinarith
      have hv := steering_vertex_in_unit_interval hc0 (le_of_lt hc)
      refine ⟨c*(1-c)/steeringDenominator c,hv.1,?_,?_⟩
      · convert hv.2 using 1 <;> norm_num [successBudgetRadius]
      · rw [steering_vertex_attains hc0 (le_of_lt hc)]
        exact steeringEnvelopeSq_gt_one hc0 hc
    · have hpf : 0 < 2*p-1 := by have : 1/2 < p := lt_of_le_of_ne hp0 (Ne.symm hhalf); linarith
      refine ⟨successBudgetRadius p,hR.1,le_rfl,?_⟩
      have hprod : 0 < (2*p-1)*successActivationPolynomial c p/p^2 :=
        div_pos (mul_pos hpf hg) (sq_pos_of_pos hp)
      rw [← success_endpoint_activation_identity (ne_of_gt hp) c] at hprod
      linarith

/-- The sharp probability-constrained envelope violates the steering bound
exactly below the explicit critical centre curve. -/
theorem successEnvelope_violation_iff_center {c p : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hp0 : 1/2 ≤ p) (hp1 : p ≤ 1) :
    1 < successEnvelopeSq c p ↔ c < successCriticalCenter p := by
  have hR := successBudgetRadius_bounds hp0 hp1
  have hr := successOptimalRadius_bounds hc0 hR.1
  have he : (1 < successEnvelopeSq c p) ↔
      (∃ r : ℝ, 0 ≤ r ∧ r ≤ successBudgetRadius p ∧
        1 < steeringQuadratic c r) := by
    constructor
    · intro h
      exact ⟨successOptimalRadius c (successBudgetRadius p),hr.1,hr.2,h⟩
    · rintro ⟨r,hr0,hrR,h⟩
      have hm := successOptimalRadius_maximizes hc0 hc1 hR.1 hR.2 hr0 hrR
      exact lt_of_lt_of_le h hm
  rw [he,success_violation_exists_iff_polynomial hc0 hc1 hp0 hp1,
    successActivationPolynomial_iff_center hc0 hc1 hp0 hp1]

/-- At success probability one half the complete normalized filter ball is
available, and the attained canonical-input envelope is the global formula. -/
theorem successEnvelope_half {c : ℝ} (hc0 : 0 ≤ c) :
    successEnvelopeSq c (1/2) = steeringEnvelopeSq c := by
  have hR : successBudgetRadius (1/2) = 1 := by norm_num [successBudgetRadius]
  rw [successEnvelopeSq,hR,successOptimalRadius]
  split_ifs with hc
  · have hv := steering_vertex_in_unit_interval hc0 hc
    change steeringQuadratic c (min 1 (c*(1-c)/steeringDenominator c)) = steeringEnvelopeSq c
    rw [min_eq_right hv.2]
    exact steering_vertex_attains hc0 hc
  · rw [steering_endpoint,steeringEnvelopeSq,if_neg hc]


end Milne

#print axioms Milne.successOptimalRadius_maximizes
#print axioms Milne.successActivationPolynomial_iff_center

#print axioms Milne.successEnvelope_violation_iff_center
#print axioms Milne.successEnvelope_half
