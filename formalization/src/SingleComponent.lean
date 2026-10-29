module
public import PolynomialDifference

@[expose] public section

noncomputable section
open Polynomial
namespace PowerRank

/-- Twisted translation never increases a coefficient polynomial's degree. -/
theorem coeffShift_natDegree_le (lam : ℂ) (P : ℂ[X]) :
    (coeffShift lam P).natDegree ≤ P.natDegree := by
  change (C lam * P.comp (X + C 1)).natDegree ≤ P.natDegree
  exact (natDegree_C_mul_le _ _).trans (translate_natDegree P).le

theorem coeffShift_coeff_of_bound (lam : ℂ) (P : ℂ[X]) (d : ℕ)
    (hd : P.natDegree ≤ d) : (coeffShift lam P).coeff d = lam * P.coeff d := by
  change (C lam * P.comp (X + C 1)).coeff d = _
  rw [coeff_C_mul, coeff_translate_of_natDegree_le P d hd]

theorem coeffShift_pow_natDegree_le (lam : ℂ) (P : ℂ[X]) (k : ℕ) :
    ((coeffShift lam ^ k) P).natDegree ≤ P.natDegree := by
  induction k with
  | zero => exact le_refl _
  | succ k ih =>
    rw [pow_succ']
    exact (coeffShift_natDegree_le lam _).trans ih

theorem coeffShift_pow_coeff_top (lam : ℂ) (P : ℂ[X]) (k : ℕ) :
    ((coeffShift lam ^ k) P).coeff P.natDegree = lam ^ k * P.leadingCoeff := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change (coeffShift lam ((coeffShift lam ^ k) P)).coeff P.natDegree = _
    rw [coeffShift_coeff_of_bound lam _ _ (coeffShift_pow_natDegree_le lam P k), ih,
      pow_succ']
    ring

theorem coeffAction_natDegree_le (lam : ℂ) (q P : ℂ[X]) :
    ((aeval (coeffShift lam) q) P).natDegree ≤ P.natDegree := by
  classical
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_smul_le _ _).trans (coeffShift_pow_natDegree_le lam P i)

/-- The leading coefficient is multiplied by q(lam), for arbitrary q. -/
theorem coeffAction_coeff_top (lam : ℂ) (q P : ℂ[X]) :
    ((aeval (coeffShift lam) q) P).coeff P.natDegree =
      q.eval lam * P.leadingCoeff := by
  classical
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, finsetSum_coeff]
  simp only [LinearMap.smul_apply, coeff_smul, coeffShift_pow_coeff_top, smul_eq_mul,
    ← mul_assoc]
  rw [← Finset.sum_mul, ← Polynomial.eval_eq_sum_range]

/-- A polynomial not vanishing at lam preserves the exact coefficient degree. -/
theorem coeffAction_natDegree (lam : ℂ) (q P : ℂ[X]) (hq : q.eval lam ≠ 0)
    (hP : P ≠ 0) : ((aeval (coeffShift lam) q) P).natDegree = P.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (coeffAction_natDegree_le lam q P)
  rw [coeffAction_coeff_top]
  exact mul_ne_zero hq (leadingCoeff_ne_zero.mpr hP)

theorem coeffAction_ne_zero (lam : ℂ) (q P : ℂ[X]) (hq : q.eval lam ≠ 0)
    (hP : P ≠ 0) : (aeval (coeffShift lam) q) P ≠ 0 := by
  intro hzero
  have hc := coeffAction_coeff_top lam q P
  rw [hzero, coeff_zero] at hc
  exact (mul_ne_zero hq (leadingCoeff_ne_zero.mpr hP)) hc.symm

theorem coeffShift_sub_scalar (lam : ℂ) :
    coeffShift lam - algebraMap ℂ (Module.End ℂ ℂ[X]) lam = lam • difference := by
  apply LinearMap.ext
  intro P
  change C lam * P.comp (X + C 1) - lam • P = lam • (P.comp (X + C 1) - P)
  simp only [smul_eq_C_mul]
  ring

/-- The root factor acts by the scaled actual forward difference. -/
theorem coeffAction_root_pow (lam : ℂ) (k : ℕ) (P : ℂ[X]) :
    (aeval (coeffShift lam) ((X - C lam) ^ k)) P =
      lam ^ k • (difference ^ k) P := by
  rw [map_pow, aeval_sub, aeval_X, aeval_C, coeffShift_sub_scalar, smul_pow]
  rfl

/-- Exact root-factor order, with no bound on polynomial degree. -/
theorem coeffAction_root_pow_eq_zero_iff (lam : ℂ) (hlam : lam ≠ 0)
    (P : ℂ[X]) (hP : P ≠ 0) (k : ℕ) :
    (aeval (coeffShift lam) ((X - C lam) ^ k)) P = 0 ↔ P.natDegree < k := by
  rw [coeffAction_root_pow, smul_eq_zero]
  simp only [pow_ne_zero _ hlam, false_or, difference_pow_eq_zero_iff P hP]

/-- Full single-component minimality against every complex polynomial. -/
theorem eventual_annihilator_expPoly_iff_dvd (lam : ℂ) (hlam : lam ≠ 0)
    (P : ℂ[X]) (hP : P ≠ 0) (q : ℂ[X]) :
    EventuallyAnnihilates q (expPoly lam P) ↔ (X - C lam) ^ (P.natDegree + 1) ∣ q := by
  rw [eventual_annihilator_iff_coeff_kernel lam hlam]
  by_cases hq : q = 0
  · simp [hq]
  obtain ⟨g, hfactor, hg⟩ := q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hq lam
  have hgeval : g.eval lam ≠ 0 := by
    intro hzero
    exact hg ((dvd_iff_isRoot).mpr hzero)
  have hQ : (aeval (coeffShift lam) g) P ≠ 0 := coeffAction_ne_zero lam g P hgeval hP
  have hdeg : ((aeval (coeffShift lam) g) P).natDegree = P.natDegree :=
    coeffAction_natDegree lam g P hgeval hP
  conv_lhs => rw [hfactor, map_mul]
  change (aeval (coeffShift lam) ((X - C lam) ^ q.rootMultiplicity lam))
      ((aeval (coeffShift lam) g) P) = 0 ↔ _
  rw [coeffAction_root_pow_eq_zero_iff lam hlam _ hQ, hdeg,
    ← q.le_rootMultiplicity_iff hq]
  omega

end PowerRank
