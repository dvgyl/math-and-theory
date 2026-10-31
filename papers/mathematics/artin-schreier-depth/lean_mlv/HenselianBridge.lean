import Mathlib

/-!
# Rational normalization of equivalent valuations

This file proves the normalization part of the missing standard-henselian
bridge. It does not assert that simple-root lifting already supplies valuation
extensions, and it does not assume such a conclusion under another name.

Two rational additive valuations which are equivalent and take value one on
the same field element agree pointwise. No algebraicity hypothesis is needed:
the denominator of each rational value reduces its comparison to an integral
power of the normalized element.
-/

noncomputable section

namespace NTCThird

/-- Integral powers of a normalized element have their specified rational value. -/
theorem rationalAddValuation_zpow_of_one
    {E : Type*} [Field E] (w : AddValuation E (WithTop ℚ))
    (t : E) (ht : w t = (1 : WithTop ℚ)) (n : ℤ) :
    w (t ^ n) = ((n : ℚ) : WithTop ℚ) := by
  cases n with
  | ofNat n =>
      simp only [Int.ofNat_eq_coe, zpow_natCast, w.map_pow, ht]
      rw [← WithTop.coe_one, ← WithTop.coe_nsmul]
      congr 1
      simp [nsmul_eq_mul]
  | negSucc n =>
      simp only [zpow_negSucc, w.map_inv, w.map_pow, ht]
      rw [← WithTop.coe_one, ← WithTop.coe_nsmul,
        ← WithTop.LinearOrderedAddCommGroup.coe_neg]
      congr 1
      simp [nsmul_eq_mul, Int.cast_negSucc]

/-- Equivalence of rational additive valuations becomes equality after fixing
one nonzero value. The hypothesis uses the actual valuation preorder. -/
theorem rationalAddValuation_eq_of_equiv_of_one
    {E : Type*} [Field E] (w₁ w₂ : AddValuation E (WithTop ℚ))
    (hequiv : w₁.IsEquiv w₂) (t : E)
    (h₁ : w₁ t = (1 : WithTop ℚ)) (h₂ : w₂ t = (1 : WithTop ℚ)) :
    w₁ = w₂ := by
  apply AddValuation.ext
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hfinite₁ : w₁ x ≠ ⊤ := w₁.ne_top_iff.mpr hx
  have hfinite₂ : w₂ x ≠ ⊤ := w₂.ne_top_iff.mpr hx
  let q₁ : ℚ := (w₁ x).untop hfinite₁
  let q₂ : ℚ := (w₂ x).untop hfinite₂
  have hq₁ : (q₁ : WithTop ℚ) = w₁ x := WithTop.coe_untop _ _
  have hq₂ : (q₂ : WithTop ℚ) = w₂ x := WithTop.coe_untop _ _
  have hden : (q₁.den : ℚ) ≠ 0 := by exact_mod_cast q₁.den_nz
  have hnum : (q₁.den : ℚ) * q₁ = (q₁.num : ℚ) := by
    simpa [mul_comm] using ((div_eq_iff hden).mp q₁.num_div_den).symm
  have hvalue₁ : w₁ (x ^ q₁.den) = w₁ (t ^ q₁.num) := by
    rw [w₁.map_pow, rationalAddValuation_zpow_of_one w₁ t h₁, ← hq₁,
      ← WithTop.coe_nsmul]
    exact congrArg (fun q : ℚ => (q : WithTop ℚ))
      (by simpa [nsmul_eq_mul] using hnum)
  have hvalue₂ : w₂ (x ^ q₁.den) = w₂ (t ^ q₁.num) :=
    hequiv.val_eq.mp hvalue₁
  rw [w₂.map_pow, rationalAddValuation_zpow_of_one w₂ t h₂, ← hq₂,
    ← WithTop.coe_nsmul, WithTop.coe_inj] at hvalue₂
  have hq : q₁ = q₂ := by
    apply (mul_left_cancel₀ hden)
    exact hnum.trans (by simpa [nsmul_eq_mul] using hvalue₂.symm)
  exact hq₁.symm.trans ((congrArg (fun q : ℚ => (q : WithTop ℚ)) hq).trans hq₂)

/-- The same normalization conclusion stated for the literal valuation rings. -/
theorem rationalAddValuation_eq_of_valuationSubring_eq_of_one
    {E : Type*} [Field E] (w₁ w₂ : AddValuation E (WithTop ℚ))
    (hring : (AddValuation.toValuation w₁).valuationSubring =
      (AddValuation.toValuation w₂).valuationSubring)
    (t : E) (h₁ : w₁ t = (1 : WithTop ℚ)) (h₂ : w₂ t = (1 : WithTop ℚ)) :
    w₁ = w₂ := by
  apply rationalAddValuation_eq_of_equiv_of_one w₁ w₂ _ t h₁ h₂
  exact (Valuation.isEquiv_iff_valuationSubring _ _).mpr hring

end NTCThird

