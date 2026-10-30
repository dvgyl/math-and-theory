import KellerKlein.Elementary
import KellerKlein.KernelDefs

noncomputable section
open Set

namespace KellerKlein

lemma rho_nonneg {u : ℝ} (hu : 0 < u) (hu1 : u < 1) : 0 ≤ rho u := by
  have hy : 0 < Real.pi * u := mul_pos Real.pi_pos hu
  have hyp : Real.pi * u < Real.pi := by nlinarith [Real.pi_pos]
  have hs : 0 < Real.sin (Real.pi * u) := Real.sin_pos_of_pos_of_lt_pi hy hyp
  have hn := sin_sub_mul_cos_nonneg
    (show 0 ≤ Real.pi - Real.pi * u by linarith)
    (show Real.pi - Real.pi * u ≤ Real.pi by linarith)
  rw [Real.sin_pi_sub, Real.cos_pi_sub] at hn
  have he : rho u = (Real.sin (Real.pi * u) +
      (Real.pi - Real.pi * u) * Real.cos (Real.pi * u)) /
      (Real.pi * Real.sin (Real.pi * u)) := by
    unfold rho
    field_simp [Real.pi_ne_zero, hs.ne']
    ring
  rw [he]
  apply div_nonneg _ (mul_pos Real.pi_pos hs).le
  nlinarith

lemma cot_le_inv_sub_third {y : ℝ} (hy : 0 < y) (hyp : y < Real.pi) :
    Real.cos y / Real.sin y ≤ 1 / y - y / 3 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hy hyp
  have hp := cotangent_upper_product hy.le hyp.le
  apply (div_le_iff₀ hs).2
  apply (mul_le_mul_right hy).mp
  calc
    Real.cos y * y = y * Real.cos y := by ring
    _ ≤ (1 - y ^ 2 / 3) * Real.sin y := hp
    _ = ((1 / y - y / 3) * Real.sin y) * y := by
      field_simp [hy.ne']
      ring

lemma rho_upper_quadratic {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    rho u ≤ 1 / (Real.pi * u) - Real.pi * u / 3 + (Real.pi * u) ^ 2 / (3 * Real.pi) := by
  have hy : 0 < Real.pi * u := mul_pos Real.pi_pos hu
  have hyp : Real.pi * u < Real.pi := by nlinarith [Real.pi_pos]
  have hc := cot_le_inv_sub_third hy hyp
  have hm := add_le_add_right (mul_le_mul_of_nonneg_left hc
    (show 0 ≤ 1 - u by linarith)) (1 / Real.pi)
  change rho u ≤ (1 - u) * (1 / (Real.pi * u) - Real.pi * u / 3) + 1 / Real.pi at hm
  convert hm using 1
  field_simp [Real.pi_ne_zero, hu.ne']
  ring

lemma rho_le_inv {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    rho u ≤ 1 / (Real.pi * u) := by
  have h := rho_upper_quadratic hu hu1
  have he : 1 / (Real.pi * u) - Real.pi * u / 3 +
      (Real.pi * u) ^ 2 / (3 * Real.pi) =
      1 / (Real.pi * u) - (1 - u) * (Real.pi * u) / 3 := by
    field_simp [Real.pi_ne_zero, hu.ne']
    ring
  rw [he] at h
  have hn : 0 ≤ (1 - u) * (Real.pi * u) / 3 :=
    div_nonneg (mul_nonneg (by linarith) (by positivity)) (by norm_num)
  linarith

lemma rho_lower_linear {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    1 / (Real.pi * u) - Real.pi * u / 2 ≤ rho u := by
  let y := Real.pi * u
  have hy : 0 < y := mul_pos Real.pi_pos hu
  have hyp : y < Real.pi := by dsimp [y]; nlinarith [Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi hy hyp
  have he : (1 - y ^ 2 / 2) / y = 1 / y - y / 2 := by
    field_simp [hy.ne']
    ring
  by_cases hsmall : y ^ 2 ≤ 2
  · have hnn : 0 ≤ 1 - y ^ 2 / 2 := by linarith
    have hc : (1 - y ^ 2 / 2) / y ≤ Real.cos y / Real.sin y := by
      apply (div_le_div_iff₀ hy hs).2
      calc
        (1 - y ^ 2 / 2) * Real.sin y ≤ (1 - y ^ 2 / 2) * y :=
          mul_le_mul_of_nonneg_left (Real.sin_le hy.le) hnn
        _ ≤ Real.cos y * y := mul_le_mul_of_nonneg_right
          (Real.one_sub_sq_div_two_le_cos (x := y)) hy.le
    have hm := add_le_add_right (mul_le_mul_of_nonneg_left hc
      (show 0 ≤ 1 - u by linarith)) (1 / Real.pi)
    have he2 : (1 - u) * ((1 - y ^ 2 / 2) / y) + 1 / Real.pi =
        1 / y - y / 2 + u * y / 2 := by
      dsimp [y]
      field_simp [Real.pi_ne_zero, hu.ne']
      ring
    rw [he2] at hm
    change 1 / y - y / 2 + u * y / 2 ≤ rho u at hm
    change 1 / y - y / 2 ≤ rho u
    have hn : 0 ≤ u * y / 2 := by positivity
    linarith
  · have hn : (1 - y ^ 2 / 2) / y ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hy.le
    rw [he] at hn
    exact hn.trans (rho_nonneg hu hu1)

lemma upperKernel_nonneg {ξ u : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2)
    (hu : 0 < u) (hu1 : u < 1) : 0 ≤ upperKernel ξ u := by
  have hz : 0 ≤ Real.pi * ξ * u := by positivity
  have hz1 : Real.pi * ξ * u ≤ Real.pi / 2 := by
    have hm : ξ * u ≤ 1 / 2 := by nlinarith
    nlinarith [Real.pi_pos]
  have hc : 0 ≤ Real.cos (Real.pi * ξ * u) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hz1⟩
  have hs : 0 ≤ Real.sin (Real.pi * ξ * u) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hz (by linarith [Real.pi_pos])
  exact add_nonneg (mul_nonneg (by linarith) hc) (mul_nonneg (rho_nonneg hu hu1) hs)

lemma upperKernel_le_one_add {ξ u : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2)
    (hu : 0 < u) (hu1 : u < 1) : upperKernel ξ u ≤ 1 + ξ := by
  have hz : 0 ≤ Real.pi * ξ * u := by positivity
  have hphase : Real.pi * ξ * u ≤ Real.pi := by
    have hm : ξ * u ≤ 1 / 2 := by nlinarith
    nlinarith [Real.pi_pos]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz hphase
  have hρ := rho_le_inv hu hu1
  have hm := mul_le_mul hρ (Real.sin_le hz) hs (by positivity : 0 ≤ 1 / (Real.pi * u))
  have he : (1 / (Real.pi * u)) * (Real.pi * ξ * u) = ξ := by
    field_simp [Real.pi_ne_zero, hu.ne']
    ring
  rw [he] at hm
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one (Real.pi * ξ * u))
    (show 0 ≤ 1 - u by linarith)
  unfold upperKernel
  nlinarith

lemma rho_reflect {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    rho (1 - t) = (1 - (Real.pi * t) * Real.cos (Real.pi * t) /
      Real.sin (Real.pi * t)) / Real.pi := by
  have hs : 0 < Real.sin (Real.pi * t) := Real.sin_pos_of_pos_of_lt_pi
    (by positivity) (by nlinarith [Real.pi_pos])
  unfold rho
  rw [mul_sub, mul_one, Real.cos_pi_sub, Real.sin_pi_sub]
  field_simp [Real.pi_ne_zero, hs.ne']
  ring

lemma rho_alias_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2) :
    rho (1 - t) ≤ Real.pi * t ^ 2 / 3 + t ^ 4 := by
  have hy : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hyp : Real.pi * t ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hs : 0 < Real.sin (Real.pi * t) := Real.sin_pos_of_pos_of_lt_pi hy
    (by linarith [Real.pi_pos])
  have hc := cotangent_lower_product hy.le hyp
  have hd : 1 - (Real.pi * t) ^ 2 / 3 - (Real.pi * t) ^ 4 / 32 ≤
      (Real.pi * t) * Real.cos (Real.pi * t) / Real.sin (Real.pi * t) :=
    (le_div_iff₀ hs).2 hc
  have hm := div_le_div_of_nonneg_right (by linarith :
      1 - ((Real.pi * t) * Real.cos (Real.pi * t) / Real.sin (Real.pi * t)) ≤
        (Real.pi * t) ^ 2 / 3 + (Real.pi * t) ^ 4 / 32) Real.pi_pos.le
  rw [← rho_reflect ht (by linarith)] at hm
  have he : ((Real.pi * t) ^ 2 / 3 + (Real.pi * t) ^ 4 / 32) / Real.pi =
      Real.pi * t ^ 2 / 3 + (Real.pi ^ 3 / 32) * t ^ 4 := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [he] at hm
  have hp : Real.pi ^ 3 ≤ 32 := by
    have hpow := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 3
    norm_num at hpow
    linarith
  have hterm : (Real.pi ^ 3 / 32) * t ^ 4 ≤ t ^ 4 := by
    have hp' : Real.pi ^ 3 / 32 ≤ 1 := by linarith
    simpa using mul_le_mul_of_nonneg_right hp' (pow_nonneg ht.le 4)
  linarith

end KellerKlein

