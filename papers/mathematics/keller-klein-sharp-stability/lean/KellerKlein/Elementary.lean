import KellerKlein.Imports

/-! Elementary analytic inequalities used in the Keller--Klein investigation.
These are auxiliary lemmas, not a formal proof of the conjecture.
-/

open Set

namespace KellerKlein

lemma nonneg_of_derivative_nonneg {f f' : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hf0 : 0 ≤ f 0)
    (hd : ∀ y ∈ Icc 0 x, HasDerivAt f (f' y) y)
    (hn : ∀ y ∈ Icc 0 x, 0 ≤ f' y) : 0 ≤ f x := by
  have hc : ContinuousOn f (Icc 0 x) := by
    intro y hy
    exact (hd y hy).continuousAt.continuousWithinAt
  have hm : MonotoneOn f (Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hc
    · intro y hy
      exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hd y (interior_subset hy)).deriv]
      exact hn y (interior_subset hy)
  exact hf0.trans (hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx)

lemma sin_lower_cubic {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have h : 0 ≤ Real.sin x - x + x ^ 3 / 6 := by
    apply nonneg_of_derivative_nonneg hx (f' := fun y => Real.cos y - 1 + y ^ 2 / 2)
    · simp
    · intro y hy
      convert ((Real.hasDerivAt_sin y).sub (hasDerivAt_id y)).add
        ((hasDerivAt_pow 3 y).div_const 6) using 1 <;> (try simp only [id_eq]) <;> ring
    · intro y hy
      linarith [Real.one_sub_sq_div_two_le_cos (x := y)]
  linarith

lemma cos_upper_quartic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have h : 0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x := by
    apply nonneg_of_derivative_nonneg hx (f' := fun y => -y + y ^ 3 / 6 + Real.sin y)
    · simp
    · intro y hy
      convert (((hasDerivAt_const y (1 : ℝ)).sub
        ((hasDerivAt_pow 2 y).div_const 2)).add
        ((hasDerivAt_pow 4 y).div_const 24)).sub (Real.hasDerivAt_cos y) using 1 <;> (try simp only [id_eq]) <;> ring
    · intro y hy
      linarith [sin_lower_cubic hy.1]
  linarith

lemma sin_upper_quintic {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have h : 0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - Real.sin x := by
    apply nonneg_of_derivative_nonneg hx
      (f' := fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y)
    · simp
    · intro y hy
      convert (((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6)).add
        ((hasDerivAt_pow 5 y).div_const 120)).sub (Real.hasDerivAt_sin y) using 1 <;> (try simp only [id_eq]) <;> ring
    · intro y hy
      linarith [cos_upper_quartic hy.1]
  linarith

lemma cos_lower_sextic {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have h : 0 ≤ Real.cos x - 1 + x ^ 2 / 2 - x ^ 4 / 24 + x ^ 6 / 720 := by
    apply nonneg_of_derivative_nonneg hx
      (f' := fun y => -Real.sin y + y - y ^ 3 / 6 + y ^ 5 / 120)
    · simp
    · intro y hy
      convert ((((Real.hasDerivAt_cos y).sub (hasDerivAt_const y (1 : ℝ))).add
        ((hasDerivAt_pow 2 y).div_const 2)).sub
        ((hasDerivAt_pow 4 y).div_const 24)).add
        ((hasDerivAt_pow 6 y).div_const 720) using 1 <;> (try simp only [id_eq]) <;> ring
    · intro y hy
      linarith [sin_upper_quintic hy.1]
  linarith

lemma cotangent_remainder_polynomial {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 5 / 2) :
    17 / 15360 ≤ (13 : ℝ) / 1440 - 11 * w / 2880 + w ^ 2 / 3840 := by
  have hprod : 0 ≤ (5 / 2 - w) * (11 / 2880 - (w + 5 / 2) / 3840) := by
    apply mul_nonneg (by linarith)
    linarith
  nlinarith

lemma tan_lower_cubic {x : ℝ} (hx : 0 ≤ x) (hxp : x < Real.pi / 2) :
    x + x ^ 3 / 3 ≤ Real.tan x := by
  have h : 0 ≤ Real.tan x - x - x ^ 3 / 3 := by
    apply nonneg_of_derivative_nonneg hx
      (f' := fun y => 1 / Real.cos y ^ 2 - 1 - y ^ 2)
    · simp
    · intro y hy
      have hc : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hy.1], hy.2.trans_lt hxp⟩
      convert ((Real.hasDerivAt_tan hc.ne').sub (hasDerivAt_id y)).sub
        ((hasDerivAt_pow 3 y).div_const 3) using 1 <;> (try simp only [id_eq]) <;> ring
    · intro y hy
      have hc : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hy.1], hy.2.trans_lt hxp⟩
      have ht := Real.le_tan hy.1 (hy.2.trans_lt hxp)
      have hid : 1 / Real.cos y ^ 2 = 1 + Real.tan y ^ 2 := by
        rw [one_div, ← Real.inv_one_add_tan_sq hc.ne', inv_inv]
      rw [hid]
      have hm : 0 ≤ (Real.tan y - y) * (Real.tan y + y) :=
        mul_nonneg (by linarith) (by linarith [hy.1])
      nlinarith
  linarith

lemma neg_log_cos_lower_quartic {x : ℝ} (hx : 0 ≤ x) (hxp : x < Real.pi / 2) :
    x ^ 2 / 2 + x ^ 4 / 12 ≤ -Real.log (Real.cos x) := by
  have h : 0 ≤ -Real.log (Real.cos x) - x ^ 2 / 2 - x ^ 4 / 12 := by
    apply nonneg_of_derivative_nonneg hx
      (f' := fun y => Real.tan y - y - y ^ 3 / 3)
    · simp
    · intro y hy
      have hc : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hy.1], hy.2.trans_lt hxp⟩
      have hdlog : HasDerivAt (fun z => -Real.log (Real.cos z)) (Real.tan y) y := by
        convert ((Real.hasDerivAt_cos y).log hc.ne').neg using 1
        rw [Real.tan_eq_sin_div_cos]
        ring
      convert (hdlog.sub ((hasDerivAt_pow 2 y).div_const 2)).sub
        ((hasDerivAt_pow 4 y).div_const 12) using 1 <;> (try simp only [id_eq]) <;> ring
    · intro y hy
      linarith [tan_lower_cubic hy.1 (hy.2.trans_lt hxp)]
  linarith

lemma log_cos_le_neg_sq_half {x : ℝ} (hx : 0 ≤ x) (hxp : x < Real.pi / 2) :
    Real.log (Real.cos x) ≤ -(x ^ 2 / 2) := by
  have h := neg_log_cos_lower_quartic hx hxp
  nlinarith [sq_nonneg (x ^ 2)]

lemma cos_le_exp_neg_sq_half {x : ℝ} (hx : 0 ≤ x) (hxp : x ≤ Real.pi / 2) :
    Real.cos x ≤ Real.exp (-(x ^ 2 / 2)) := by
  rcases hxp.eq_or_lt with h | h
  · rw [h, Real.cos_pi_div_two]
    exact (Real.exp_pos _).le
  · have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], h⟩
    simpa only [Real.exp_log hc] using
      Real.exp_le_exp.mpr (log_cos_le_neg_sq_half hx h)

lemma sin_sub_mul_cos_nonneg {x : ℝ} (hx : 0 ≤ x) (hxp : x ≤ Real.pi) :
    0 ≤ Real.sin x - x * Real.cos x := by
  apply nonneg_of_derivative_nonneg hx (f' := fun y => y * Real.sin y)
  · simp
  · intro y hy
    convert (Real.hasDerivAt_sin y).sub
      ((hasDerivAt_id y).mul (Real.hasDerivAt_cos y)) using 1 <;> (try simp only [id_eq]) <;> ring
  · intro y hy
    exact mul_nonneg hy.1 (Real.sin_nonneg_of_nonneg_of_le_pi hy.1 (hy.2.trans hxp))

lemma cotangent_upper_product {x : ℝ} (hx : 0 ≤ x) (hxp : x ≤ Real.pi) :
    x * Real.cos x ≤ (1 - x ^ 2 / 3) * Real.sin x := by
  have h : 0 ≤ (1 - x ^ 2 / 3) * Real.sin x - x * Real.cos x := by
    apply nonneg_of_derivative_nonneg hx
      (f' := fun y => y / 3 * (Real.sin y - y * Real.cos y))
    · simp
    · intro y hy
      convert (((hasDerivAt_const y (1 : ℝ)).sub
        ((hasDerivAt_pow 2 y).div_const 3)).mul (Real.hasDerivAt_sin y)).sub
        ((hasDerivAt_id y).mul (Real.hasDerivAt_cos y)) using 1 <;> (try simp only [id_eq]) <;> ring
    · intro y hy
      exact mul_nonneg (div_nonneg hy.1 (by norm_num)) (sin_sub_mul_cos_nonneg hy.1 (hy.2.trans hxp))
  linarith

lemma cotangent_lower_product {x : ℝ} (hx : 0 ≤ x) (hxp : x ≤ Real.pi / 2) :
    (1 - x ^ 2 / 3 - x ^ 4 / 32) * Real.sin x ≤ x * Real.cos x := by
  have hs : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], hxp⟩
  let Q : ℝ := 1 - x ^ 2 / 3 - x ^ 4 / 32
  by_cases hQ : 0 ≤ Q
  · have hsin := mul_le_mul_of_nonneg_left (sin_upper_quintic hx) hQ
    have hcos := mul_le_mul_of_nonneg_left (cos_lower_sextic hx) hx
    have hx2 : x ^ 2 ≤ 5 / 2 := by
      have hx' : x ≤ 63 / 40 := by linarith [Real.pi_lt_d2]
      have hm : 0 ≤ (63 / 40 - x) * (63 / 40 + x) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hpol := cotangent_remainder_polynomial (sq_nonneg x) hx2
    have hnonneg : 0 ≤ x ^ 5 *
        ((13 : ℝ) / 1440 - 11 * x ^ 2 / 2880 + (x ^ 2) ^ 2 / 3840) :=
      mul_nonneg (pow_nonneg hx _) (by linarith)
    have heq : x * (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) -
        Q * (x - x ^ 3 / 6 + x ^ 5 / 120) =
        x ^ 5 * ((13 : ℝ) / 1440 - 11 * x ^ 2 / 2880 + (x ^ 2) ^ 2 / 3840) := by
      dsimp [Q]
      ring
    rw [← heq] at hnonneg
    change Q * Real.sin x ≤ x * Real.cos x
    exact hsin.trans ((sub_nonneg.mp hnonneg).trans hcos)
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hQ) hs).trans
      (mul_nonneg hx hc)

end KellerKlein

