import FiniteEuler
import ValleyPath

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Set

namespace NesterovThreshold

/-- Every smooth valley family satisfying the proved model bounds contains a
parameter for which every actual trajectory reaches beyond a prescribed bound.
The model wrapper later supplies the scalar fields from the literal gradient ODE. -/
theorem exists_parameter_excursion {r p M : ℝ}
    (hr : 1 < r) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (hpr : p * (r - 1) ≤ 2) (hM : 2 ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ S : ValleyPath r p ε, ∃ t : ℝ, 0 ≤ t ∧ M < S.x t := by
  let B := M + 2
  let Jstar := Real.exp 1 * (r - 1) ^ 2 / 2
  let e0 := Jstar / (2 * Real.exp (M / 2))
  let C := 2 + 4 * B * (r - 1) ^ 2
  let D0 := 2 * (r - 1) ^ 2
  let c := e0 / (2 * C)
  let K := (p - 1) / (2 * B)
  let d := K * c / 2
  have hrp : 0 < r - 1 := by linarith
  have hpp : 0 < p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hB4 : 4 ≤ B := by dsimp [B]; linarith
  have hJs : 0 < Jstar := by dsimp [Jstar]; positivity
  have he0 : 0 < e0 := by dsimp [e0]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hD0 : 0 < D0 := by dsimp [D0]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨T, hT, hEuler⟩ := exists_finite_euler_obstruction hr hB.le hd
  have hTpos : 0 < T := by linarith
  let ε := min 1 (min (Jstar / ((r - 1) * Real.exp (M / 2) * T ^ 2))
    (min (e0 / (2 * D0)) (c / (6 * T ^ 2))))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεA : ε ≤ Jstar / ((r - 1) * Real.exp (M / 2) * T ^ 2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hεB : ε ≤ e0 / (2 * D0) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεC : ε ≤ c / (6 * T ^ 2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hεsq : ε ^ 2 ≤ ε := by nlinarith only [hε.le, hε1]
  have hεsq1 : ε ^ 2 ≤ 1 := hεsq.trans hε1
  have hsmallA : (r - 1) * ε * Real.exp (M / 2) * T ^ 2 ≤ Jstar := by
    have h := (le_div_iff₀ (show 0 < (r - 1) * Real.exp (M / 2) * T ^ 2 by positivity)).mp hεA
    nlinarith only [h]
  have hsmallB : D0 * ε ^ 2 ≤ e0 / 2 := by
    have h := (le_div_iff₀ (show 0 < 2 * D0 by positivity)).mp hεB
    have hm := mul_le_mul_of_nonneg_left hεsq hD0.le
    nlinarith only [h, hm]
  have hsmallC : 6 * ε * T ^ 2 ≤ c := by
    have h := (le_div_iff₀ (show 0 < 6 * T ^ 2 by positivity)).mp hεC
    nlinarith only [h]
  refine ⟨ε, hε, hε1, ?_⟩
  intro S
  by_contra hescape
  have hxbound : ∀ t ≥ 0, S.x t ≤ M := by
    intro t ht
    by_contra hn
    exact hescape ⟨t, ht, lt_of_not_ge hn⟩
  have hx2 := S.first_coordinate_ge_two hr
  have hv0 := S.velocity_nonneg hr
  have hW := fun t ht => S.bounds_W hr (t := t) ht
  have hF1 : ∀ t ≥ 0, S.F t ≤ 1 := fun t ht => (hW t ht).2.1.trans (hW t ht).2.2
  have hysq : ∀ t ≥ 0, S.y t ^ 2 ≤ 4 * B * S.F t + 2 * ε ^ 2 := by
    intro t ht
    exact S.upper_y_sq M t hM ht (hx2 t ht) (hxbound t ht) (hF1 t ht)
  have hysq' : ∀ t ≥ 0, S.y t ^ 2 ≤ 4 * B + 2 := by
    intro t ht
    have hm := mul_le_mul_of_nonneg_left (hF1 t ht) (show 0 ≤ 4 * B by positivity)
    nlinarith only [hm, hysq t ht, hεsq1]
  have hJmono := S.compensated_J_monotone hr hpr hε.le
    (M := M) (T := T) (fun t ht => hxbound t ht.1)
  have hJlower : ∀ t ∈ Icc 0 T, Jstar / 2 ≤ S.J t := by
    intro t ht
    have hm := hJmono (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl, hTpos.le⟩) ht ht.1
    dsimp only at hm
    rw [S.initial_J] at hm
    have ht2 : t ^ 2 ≤ T ^ 2 := by nlinarith only [ht.1, ht.2, hTpos]
    have hmul := mul_le_mul_of_nonneg_left ht2
      (show 0 ≤ (r - 1) * ε * Real.exp (M / 2) by positivity)
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, add_zero] at hm
    change Jstar ≤ S.J t + (r - 1) * ε * Real.exp (M / 2) * t ^ 2 / 2 at hm
    nlinarith only [hm, hmul, hsmallA]
  have hElower : ∀ t ∈ Icc 0 T, e0 ≤ S.E t := by
    intro t ht
    have hE0 : 0 ≤ S.E t := by
      unfold ValleyPath.E
      have hF0 := S.nonneg_F t ht.1
      positivity
    have he := Real.exp_le_exp.mpr (show S.x t / 2 ≤ M / 2 by linarith [hxbound t ht.1])
    have hm := mul_le_mul_of_nonneg_right he hE0
    have hj := hJlower t ht
    unfold ValleyPath.J at hj
    dsimp [e0]
    apply (div_le_iff₀ (show 0 < 2 * Real.exp (M / 2) by positivity)).mpr
    nlinarith only [hm, hj]
  have hEupper : ∀ t ∈ Icc 1 T, S.E t ≤ C * t ^ 2 * S.W t + D0 * ε ^ 2 := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
    have ht2 : 1 ≤ t ^ 2 := by nlinarith only [ht.1]
    have hF0 := S.nonneg_F t ht0
    have hW0 : 0 ≤ S.W t := hF0.trans (hW t ht0).2.1
    have hy := hysq t ht0
    have hyM := mul_le_mul_of_nonneg_left hy (sq_nonneg (r - 1))
    have hs := sq_nonneg (t * S.w t - (r - 1) * S.y t)
    have hFW := mul_le_mul_of_nonneg_left (hW t ht0).2.1
      (show 0 ≤ 4 * B * (r - 1) ^ 2 by positivity)
    have htW := mul_le_mul_of_nonneg_right ht2
      (show 0 ≤ 4 * B * (r - 1) ^ 2 * S.W t by positivity)
    have hTF := mul_nonneg (sq_nonneg t) hF0
    calc
      S.E t ≤ t ^ 2 * S.w t ^ 2 + (r - 1) ^ 2 * S.y t ^ 2 +
          t ^ 2 * S.F t := by
        unfold ValleyPath.E
        nlinarith only [hs]
      _ ≤ 2 * t ^ 2 * S.W t + (r - 1) ^ 2 * S.y t ^ 2 := by
        unfold ValleyPath.W
        nlinarith only [hTF]
      _ ≤ 2 * t ^ 2 * S.W t + 4 * B * (r - 1) ^ 2 * S.W t +
          D0 * ε ^ 2 := by
        dsimp [D0]
        nlinarith only [hyM, hFW]
      _ ≤ C * t ^ 2 * S.W t + D0 * ε ^ 2 := by
        dsimp [C]
        nlinarith only [htW]
  have hWlower : ∀ t ∈ Icc 1 T, c / t ^ 2 ≤ S.W t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have he := hElower t ⟨le_trans (by norm_num) ht.1, ht.2⟩
    have hu := hEupper t ht
    have hct : c * (2 * C) = e0 := by dsimp [c]; field_simp
    apply (div_le_iff₀ (sq_pos_of_pos htpos)).mpr
    have hh : 0 ≤ C * (S.W t * t ^ 2 - c) := by nlinarith only [he, hu, hct, hsmallB]
    have hh' := nonneg_of_mul_nonneg_right hh hC
    linarith only [hh']
  let k := (p - 1) / (4 * p * B)
  have hk : 0 < k := by dsimp [k]; positivity
  have hk_id : 4 * p * B * k = p - 1 := by dsimp [k]; field_simp
  have hk4 : 4 * B * k ≤ 1 := by
    apply (mul_le_mul_left hp0).mp
    nlinarith only [hk_id]
  have hk4small : 4 * k ≤ 1 := by nlinarith only [hk4, mul_nonneg hk.le (show 0 ≤ B - 1 by linarith only [hB4])]
  have hk2 : 2 * k ≤ 1 := by linarith only [hk4small]
  let H : ℝ → ℝ := fun t => S.x t + k * S.y t ^ 2
  let D : ℝ → ℝ := fun t => S.v t + 2 * k * S.y t * S.w t
  let DD : ℝ → ℝ := fun t => (-r / t * S.v t + S.a t) +
    2 * k * (S.w t ^ 2 + S.y t * (-r / t * S.w t - S.b t))
  have hHd : ∀ t ∈ Icc 1 T, HasDerivAt H (D t) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    convert (S.deriv_x t htpos).add (((S.deriv_y t htpos).pow 2).const_mul k) using 1
    dsimp [H, D]
    simp only [Nat.cast_ofNat, pow_one]
    ring
  have hDd : ∀ t ∈ Icc 1 T, HasDerivAt D (DD t) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    convert (S.deriv_v t htpos).add
      (((S.deriv_y t htpos).mul (S.deriv_w t htpos)).const_mul (2 * k)) using 1
    · dsimp [D]
      ext s
      ring
    · dsimp [DD]
      ring
  have hHb : ∀ t ∈ Icc 1 T, 0 ≤ H t ∧ H t ≤ B := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
    have hy := mul_le_mul_of_nonneg_left (hysq' t ht0) hk.le
    dsimp [H]
    constructor
    · nlinarith only [hx2 t ht0, mul_nonneg hk.le (sq_nonneg (S.y t))]
    · have hx := hxbound t ht0
      change S.x t + k * S.y t ^ 2 ≤ M + 2
      nlinarith only [hy, hx, hk4, hk2]
  have hD1 : -2 ≤ D 1 := by
    have hy := hysq' 1 (by norm_num)
    have hw := (hW 1 (by norm_num)).2.2
    have hF0 := S.nonneg_F 1 (by norm_num)
    have hcross : -(2 * B + 2) ≤ S.y 1 * S.w 1 := by
      unfold ValleyPath.W at hw
      nlinarith only [hy, hw, hF0, sq_nonneg (S.y 1 + S.w 1)]
    have hm := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 2 * k by positivity)
    dsimp [D]
    nlinarith only [hm, hv0 1 (by norm_num), hk4, hk4small]
  have hforce : ∀ t ∈ Icc 1 T, d / t ^ 2 ≤ DD t + r / t * D t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have ha := S.lower_a M t hM ht0 (hx2 t ht0) (hxbound t ht0) (hF1 t ht0)
    have hyb := S.upper_yb t ht0 (hx2 t ht0)
    have heq : DD t + r / t * D t = S.a t + 2 * k * (S.w t ^ 2 - S.y t * S.b t) := by
      dsimp [DD, D]
      ring
    rw [heq]
    have hK_id : 2 * K = (p - 1) / B := by dsimp [K]; ring
    have hkK : 2 * k * p = K := by dsimp [K, k]; field_simp; ring
    have hkKlo : K / 2 ≤ 2 * k := by nlinarith only [hkK, mul_nonneg hk.le (show 0 ≤ 2 - p by linarith only [hp2])]
    have hkKhi : 2 * k ≤ K := by nlinarith only [hkK, mul_nonneg hk.le hpp.le]
    have ha' : 2 * K * (S.F t - ε) ≤ S.a t := by
      rw [hK_id]
      exact ha
    have hy' := mul_le_mul_of_nonneg_left hyb (show 0 ≤ 2 * k by positivity)
    have hw' := mul_le_mul_of_nonneg_right hkKlo (sq_nonneg (S.w t))
    have hε' := mul_le_mul_of_nonneg_right hkKhi hε.le
    have he : K * S.W t - 3 * K * ε ≤ S.a t + 2 * k * (S.w t ^ 2 - S.y t * S.b t) := by
      unfold ValleyPath.W
      have hKF := congrArg (fun z : ℝ => z * S.F t) hkK
      dsimp only at hKF
      nlinarith only [ha', hy', hw', hε', hKF]
    have hw := mul_le_mul_of_nonneg_left (hWlower t ht) hK.le
    have ht2 : t ^ 2 ≤ T ^ 2 := by nlinarith only [ht.1, ht.2, hTpos]
    have htm := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ 6 * ε by positivity)
    have hsm : 6 * ε * t ^ 2 ≤ c := by linarith only [htm, hsmallC]
    have hfrac : 3 * K * ε ≤ K * c / (2 * t ^ 2) := by
      apply (le_div_iff₀ (show 0 < 2 * t ^ 2 by positivity)).mpr
      have hm := mul_le_mul_of_nonneg_left hsm hK.le
      nlinarith only [hm]
    have heqd : d / t ^ 2 = K * c / (2 * t ^ 2) := by dsimp [d]; ring
    rw [heqd]
    have heqf : K * (c / t ^ 2) = 2 * (K * c / (2 * t ^ 2)) := by ring
    nlinarith only [he, hw, hfrac, heqf]
  exact hEuler H D DD hHd hDd hHb hD1 hforce

#print axioms exists_parameter_excursion

end NesterovThreshold
