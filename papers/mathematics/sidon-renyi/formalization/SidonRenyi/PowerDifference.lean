import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

namespace SidonRenyi

open Set Real

/-- The algebraic identity that isolates the geometric-midpoint correction. -/
theorem power_cross_identity {a x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x ^ a + y ^ a) * (x ^ (a - 1) - y ^ (a - 1)) =
      x ^ (2 * a - 1) - y ^ (2 * a - 1) -
        (x * y) ^ (a - 1) * (x - y) := by
  have hxa : x ^ a = x ^ (a - 1) * x := by
    calc
      x ^ a = x ^ ((a - 1) + 1) := by congr 1; ring
      _ = x ^ (a - 1) * x ^ (1 : ℝ) := Real.rpow_add hx _ _
      _ = x ^ (a - 1) * x := by rw [Real.rpow_one]
  have hya : y ^ a = y ^ (a - 1) * y := by
    calc
      y ^ a = y ^ ((a - 1) + 1) := by congr 1; ring
      _ = y ^ (a - 1) * y ^ (1 : ℝ) := Real.rpow_add hy _ _
      _ = y ^ (a - 1) * y := by rw [Real.rpow_one]
  have hxk : x ^ (2 * a - 1) = x ^ (a - 1) * (x ^ (a - 1) * x) := by
    rw [← hxa, ← Real.rpow_add hx]
    congr 1
    ring
  have hyk : y ^ (2 * a - 1) = y ^ (a - 1) * (y ^ (a - 1) * y) := by
    rw [← hya, ← Real.rpow_add hy]
    congr 1
    ring
  rw [hxa, hya, hxk, hyk, Real.mul_rpow hx.le hy.le]
  ring

private theorem exp_sum_neg_strictMonoOn :
    StrictMonoOn (fun u : ℝ => Real.exp u + Real.exp (-u)) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact (Real.continuous_exp.add (Real.continuous_exp.comp continuous_neg)).continuousOn
  · intro u hu
    have hu0 : 0 < u := by simpa only [interior_Ici, mem_Ioi] using hu
    have hd : HasDerivAt (fun z : ℝ => Real.exp z + Real.exp (-z))
        (Real.exp u - Real.exp (-u)) u := by
      convert (Real.hasDerivAt_exp u).add ((hasDerivAt_id u).neg.exp) using 1 <;>
        simp only [id_eq] <;> ring
    rw [hd.deriv]
    have hh : Real.exp (-u) < Real.exp u := Real.exp_lt_exp.mpr (by linarith)
    nlinarith

/-- Strict hyperbolic-sine scaling, written entirely with exponentials. -/
theorem exp_difference_scale_lt {k u : ℝ} (hk : 1 < k) (hu : 0 < u) :
    k * (Real.exp u - Real.exp (-u)) < Real.exp (k * u) - Real.exp (-(k * u)) := by
  let f : ℝ → ℝ := fun z =>
    Real.exp (k * z) - Real.exp (-(k * z)) - k * (Real.exp z - Real.exp (-z))
  have hd (z : ℝ) : HasDerivAt f
      (k * ((Real.exp (k * z) + Real.exp (-(k * z))) -
        (Real.exp z + Real.exp (-z)))) z := by
    dsimp [f]
    convert (((hasDerivAt_id z).const_mul k).exp.sub
      (((hasDerivAt_id z).const_mul k).neg.exp)).sub
      (((Real.hasDerivAt_exp z).sub (hasDerivAt_id z).neg.exp).const_mul k) using 1 <;>
        simp only [id_eq] <;> ring
  have hm : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr (fun z => (hd z).continuousAt)).continuousOn
    · intro z hz
      have hz0 : 0 < z := by simpa only [interior_Ici, mem_Ioi] using hz
      rw [(hd z).deriv]
      apply mul_pos (by linarith : 0 < k)
      apply sub_pos.mpr
      exact exp_sum_neg_strictMonoOn (show z ∈ Set.Ici 0 from hz0.le)
        (show k * z ∈ Set.Ici 0 from mul_nonneg (by linarith) hz0.le)
        (by nlinarith)
  have hh := hm (show (0 : ℝ) ∈ Set.Ici 0 from by simp)
    (show u ∈ Set.Ici 0 from hu.le) hu
  dsimp [f] at hh
  simp only [mul_zero, neg_zero, Real.exp_zero, sub_self, mul_zero, zero_sub] at hh
  linarith

private theorem exp_power_difference (m u k : ℝ) :
    (Real.exp (m + u)) ^ k - (Real.exp (m - u)) ^ k =
      Real.exp (m * k) * (Real.exp (k * u) - Real.exp (-(k * u))) := by
  rw [← Real.exp_mul, ← Real.exp_mul]
  rw [show (m + u) * k = m * k + k * u by ring,
    show (m - u) * k = m * k + -(k * u) by ring]
  rw [Real.exp_add, Real.exp_add]
  ring

private theorem exp_power_midpoint (m u k : ℝ) :
    ((Real.exp (m + u)) * (Real.exp (m - u))) ^ ((k - 1) / 2) *
      (Real.exp (m + u) - Real.exp (m - u)) =
      Real.exp (m * k) * (Real.exp u - Real.exp (-u)) := by
  rw [← Real.exp_add, ← Real.exp_mul]
  rw [show m + u + (m - u) = 2 * m by ring]
  rw [show Real.exp (m + u) - Real.exp (m - u) =
    Real.exp m * (Real.exp u - Real.exp (-u)) by
      rw [sub_eq_add_neg m u, Real.exp_add, Real.exp_add]; ring]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- A strict lower bound on a difference of real powers by its geometric-midpoint slope. -/
theorem power_difference_lt {a x y : ℝ} (ha : 1 < a) (hy : 0 < y) (hxy : y < x) :
    (2 * a - 1) * (x * y) ^ (a - 1) * (x - y) <
      x ^ (2 * a - 1) - y ^ (2 * a - 1) := by
  have hx : 0 < x := lt_trans hy hxy
  let m := (Real.log x + Real.log y) / 2
  let u := (Real.log x - Real.log y) / 2
  let k := 2 * a - 1
  have hu : 0 < u := by
    dsimp [u]
    exact div_pos (sub_pos.mpr (Real.log_lt_log hy hxy)) (by norm_num)
  have hk : 1 < k := by dsimp [k]; linarith
  have hxe : x = Real.exp (m + u) := by
    rw [show m + u = Real.log x by dsimp [m, u]; ring]
    exact (Real.exp_log hx).symm
  have hye : y = Real.exp (m - u) := by
    rw [show m - u = Real.log y by dsimp [m, u]; ring]
    exact (Real.exp_log hy).symm
  have he : a - 1 = (k - 1) / 2 := by dsimp [k]; ring
  change k * (x * y) ^ (a - 1) * (x - y) < x ^ k - y ^ k
  rw [hxe, hye, he, exp_power_difference]
  rw [mul_assoc, exp_power_midpoint]
  have hh := mul_lt_mul_of_pos_left (exp_difference_scale_lt hk hu) (Real.exp_pos (m * k))
  nlinarith

/-- The non-strict geometric-midpoint lower bound, including equal inputs. -/
theorem power_difference_le {a x y : ℝ} (ha : 1 < a) (hy : 0 < y) (hxy : y ≤ x) :
    (2 * a - 1) * (x * y) ^ (a - 1) * (x - y) ≤
      x ^ (2 * a - 1) - y ^ (2 * a - 1) := by
  obtain hlt | heq := lt_or_eq_of_le hxy
  · exact (power_difference_lt ha hy hlt).le
  · subst x
    simp

/-- The same lower bound remains valid when the smaller input is zero. -/
theorem power_difference_le_of_nonneg {a x y : ℝ}
    (ha : 1 < a) (hy : 0 ≤ y) (hxy : y ≤ x) :
    (2 * a - 1) * (x * y) ^ (a - 1) * (x - y) ≤
      x ^ (2 * a - 1) - y ^ (2 * a - 1) := by
  obtain hypos | hyzero := lt_or_eq_of_le hy
  · exact power_difference_le ha hypos hxy
  · subst y
    have hane : a - 1 ≠ 0 := by linarith
    have hkne : 2 * a - 1 ≠ 0 := by linarith
    simp only [mul_zero, Real.zero_rpow hane, Real.zero_rpow hkne, sub_zero, zero_mul]
    exact Real.rpow_nonneg hxy _

/-- Reversed hyperbolic-sine scaling for a factor strictly between zero and one. -/
theorem exp_difference_scale_lt_of_lt_one {k u : ℝ}
    (hkpos : 0 < k) (hk : k < 1) (hu : 0 < u) :
    Real.exp (k * u) - Real.exp (-(k * u)) <
      k * (Real.exp u - Real.exp (-u)) := by
  have hki : 1 < k⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hkpos]
    simpa using hk
  have hh := exp_difference_scale_lt hki (mul_pos hkpos hu)
  have hid : k⁻¹ * (k * u) = u := by field_simp
  rw [hid] at hh
  have hh' := mul_lt_mul_of_pos_left hh hkpos
  simpa only [← mul_assoc, mul_inv_cancel₀ hkpos.ne', one_mul] using hh'

/-- For exponents between zero and one the geometric-midpoint inequality reverses. -/
theorem power_difference_lt_of_half_lt {a x y : ℝ}
    (ha : (1 : ℝ) / 2 < a) (ha1 : a < 1) (hy : 0 < y) (hxy : y < x) :
    x ^ (2 * a - 1) - y ^ (2 * a - 1) <
      (2 * a - 1) * (x * y) ^ (a - 1) * (x - y) := by
  have hx : 0 < x := lt_trans hy hxy
  let m := (Real.log x + Real.log y) / 2
  let u := (Real.log x - Real.log y) / 2
  let k := 2 * a - 1
  have hu : 0 < u := by
    dsimp [u]
    exact div_pos (sub_pos.mpr (Real.log_lt_log hy hxy)) (by norm_num)
  have hkpos : 0 < k := by dsimp [k]; linarith
  have hk : k < 1 := by dsimp [k]; linarith
  have hxe : x = Real.exp (m + u) := by
    rw [show m + u = Real.log x by dsimp [m, u]; ring]
    exact (Real.exp_log hx).symm
  have hye : y = Real.exp (m - u) := by
    rw [show m - u = Real.log y by dsimp [m, u]; ring]
    exact (Real.exp_log hy).symm
  have he : a - 1 = (k - 1) / 2 := by dsimp [k]; ring
  change x ^ k - y ^ k < k * (x * y) ^ (a - 1) * (x - y)
  rw [hxe, hye, he, exp_power_difference]
  rw [mul_assoc, exp_power_midpoint]
  have hh := mul_lt_mul_of_pos_left
    (exp_difference_scale_lt_of_lt_one hkpos hk hu) (Real.exp_pos (m * k))
  nlinarith

theorem power_difference_le_of_half_lt {a x y : ℝ}
    (ha : (1 : ℝ) / 2 < a) (ha1 : a < 1) (hy : 0 < y) (hxy : y ≤ x) :
    x ^ (2 * a - 1) - y ^ (2 * a - 1) ≤
      (2 * a - 1) * (x * y) ^ (a - 1) * (x - y) := by
  obtain hlt | heq := lt_or_eq_of_le hxy
  · exact (power_difference_lt_of_half_lt ha ha1 hy hlt).le
  · subst x
    simp

end SidonRenyi
