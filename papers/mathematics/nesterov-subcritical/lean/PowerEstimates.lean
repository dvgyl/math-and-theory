import PowerAlgebra

set_option autoImplicit false
set_option maxHeartbeats 0

namespace NesterovThresholdModel

theorem power_norm_estimates (q : PowerExponent) {h b R : ℝ} (hR : 0≤R)
    (h0 : 0≤h) (h1 : h≤1) (hb : |b|≤1) (hle : h^q.n+b^q.n=1) :
    0≤R-R*h^(q.n-1) ∧
    R*(1-h)≤R-R*h^(q.n-1) ∧
    (q.p-1)*(R-R*h^(q.n-1))≤R*(1-h) ∧
    R*b^(q.n-1)*b≤q.p*(R-R*h^(q.n-1)) ∧
    (R*b^(q.n-1))^2≤(R-R*h^(q.n-1))*(R+R*h^(q.n-1)) := by
  have hnq : (2:ℝ)≤q.n := by exact_mod_cast q.two_le
  have hm : (0:ℝ)<(q.n:ℝ)-1 := by linarith
  have hcast : ((q.n-1:ℕ):ℝ)=(q.n:ℝ)-1 := by
    rw [Nat.cast_sub (show 1≤q.n by have:=q.two_le;omega),Nat.cast_one]
  have hpow : h^(q.n-1)≤1 := pow_le_one₀ h0 h1
  have hv : 0≤R-R*h^(q.n-1) := by nlinarith [mul_nonneg hR (sub_nonneg.mpr hpow)]
  have hu : R*(1-h)≤R-R*h^(q.n-1) := by
    have hh := mul_le_mul_of_nonneg_left (one_sub_pow_lower h0 h1 q.pred_pos) hR
    nlinarith
  have hp : (q.p-1)*((q.n:ℝ)-1)=1 := by nlinarith [q.p_mul_pred]
  have hlo : (q.p-1)*(R-R*h^(q.n-1))≤R*(1-h) := by
    have hh := one_sub_pow_upper h0 (q.n-1)
    rw [hcast] at hh
    calc
      (q.p-1)*(R-R*h^(q.n-1))=(q.p-1)*R*(1-h^(q.n-1)) := by ring
      _≤(q.p-1)*R*(((q.n:ℝ)-1)*(1-h)) :=
        mul_le_mul_of_nonneg_left hh (mul_nonneg (by linarith [q.p_gt_one]) hR)
      _=R*((q.p-1)*((q.n:ℝ)-1))*(1-h) := by ring
      _=R*(1-h) := by rw [hp];ring
  have hy : R*b^(q.n-1)*b≤q.p*(R-R*h^(q.n-1)) := by
    have hh := consecutive_power_bound h0 (q.n-1)
    rw [q.pred_succ,hcast] at hh
    have hbq : b^(q.n-1)*b=b^q.n := by rw [←pow_succ,q.pred_succ]
    apply (mul_le_mul_left hm).mp
    calc
      ((q.n:ℝ)-1)*(R*b^(q.n-1)*b)=R*(((q.n:ℝ)-1)*(1-h^q.n)) := by
        rw [mul_assoc R, hbq]
        rw [(eq_sub_iff_add_eq').mpr hle]
        ring
      _≤R*((((q.n:ℝ)-1)+1)*(1-h^(q.n-1))) := mul_le_mul_of_nonneg_left hh hR
      _=((q.n:ℝ)-1)*(q.p*(R-R*h^(q.n-1))) := by
        have he := q.p_mul_pred
        calc
          _=(q.n:ℝ)*(R-R*h^(q.n-1)) := by ring
          _=(q.p*((q.n:ℝ)-1))*(R-R*h^(q.n-1)) := by rw [he]
          _=_ := by ring
  have hnorm : (h^(q.n-1))^2+(b^(q.n-1))^2≤1 := by
    have hh := even_power_double_pred_bound q h0 h1 hb
    rw [hle] at hh
    simpa only [←pow_mul,Nat.mul_comm] using hh
  have hs : (R*b^(q.n-1))^2≤(R-R*h^(q.n-1))*(R+R*h^(q.n-1)) := by
    have hh := mul_nonneg (sq_nonneg R) (sub_nonneg.mpr hnorm)
    nlinarith
  exact ⟨hv,hu,hlo,hy,hs⟩

end NesterovThresholdModel
