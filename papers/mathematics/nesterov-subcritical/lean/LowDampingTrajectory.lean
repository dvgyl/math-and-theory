import LowDampingPotential
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace NesterovLowDamping
variable {r : ℝ}

def speed (r : ℝ) : ℝ := 4/(r+3)
def tail (r t : ℝ) : ℝ := if r=1 then Real.log t else (t^(1-r)-1)/(1-r)
def position (r t : ℝ) : ℝ :=
  if t≤1 then t^2-beta r*t^4 else edge r+speed r*tail r t
def velocity (r t : ℝ) : ℝ :=
  if t≤1 then 2*t-4*beta r*t^3 else speed r*t^(-r)
def acceleration (r t : ℝ) : ℝ :=
  if t≤1 then 2-12*beta r*t^2 else -(r*speed r)*t^(-r-1)

lemma speed_pos (hr : 0<r) : 0<speed r := by unfold speed; positivity

lemma beta_speed (hr : 0<r) : 2-4*beta r=speed r := by
  unfold beta speed
  field_simp
  ring

lemma beta_accel (hr : 0<r) : 2-12*beta r= -r*speed r := by
  unfold beta speed
  field_simp
  ring

lemma tail_one (r : ℝ) : tail r 1=0 := by simp [tail]

lemma tail_hasDerivAt {t : ℝ} (ht : 0<t) : HasDerivAt (tail r) (t^(-r)) t := by
  by_cases hr : r=1
  · subst r
    have heq : tail 1 = Real.log := by funext s; simp [tail]
    rw [heq]
    simpa only [Real.rpow_neg_one] using Real.hasDerivAt_log ht.ne'
  · have hn : 1-r≠0 := sub_ne_zero.mpr (Ne.symm hr)
    have h := ((Real.hasDerivAt_rpow_const (p := 1-r) (Or.inl ht.ne')).sub_const 1).div_const (1-r)
    have heq : tail r = fun s => (s^(1-r)-1)/(1-r) := by
      funext s
      exact if_neg hr
    rw [heq]
    convert h using 1
    rw [show 1-r-1 = -r by ring]
    field_simp

lemma hasDerivAt_if_le {f g : ℝ → ℝ} {c d : ℝ}
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (he : f c=g c) :
    HasDerivAt (fun t => if t≤c then f t else g t) d c := by
  have hl : HasDerivWithinAt (fun t => if t≤c then f t else g t) d (Iic c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro t ht
      exact if_pos ht
    · simp
  have hh : HasDerivWithinAt (fun t => if t≤c then f t else g t) d (Ici c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      by_cases htc : t≤c
      · have hc : t=c := le_antisymm htc ht
        simpa only [hc, le_refl, if_true] using he
      · simp [htc]
    · simpa using he
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hh

lemma position_hasDerivAt (hr : 0<r) (t : ℝ) :
    HasDerivAt (position r) (velocity r t) t := by
  have hp (s : ℝ) : HasDerivAt (fun t : ℝ => t^2-beta r*t^4)
      (2*s-4*beta r*s^3) s := by
    convert ((hasDerivAt_id s).pow 2).sub (((hasDerivAt_id s).pow 4).const_mul (beta r)) using 1
    simp only [id_eq, Nat.cast_ofNat, pow_one]
    ring
  have ht (s : ℝ) (hs : 0<s) :
      HasDerivAt (fun t => edge r+speed r*tail r t) (speed r*s^(-r)) s :=
    (tail_hasDerivAt hs).const_mul (speed r) |>.const_add (edge r)
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · have hh := hp t
    rw [velocity, if_pos hlt.le]
    apply hh.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hlt] with s hs
    simp only [position, if_pos hs.le]
  · subst t
    have hp1 : HasDerivAt (fun t : ℝ => t^2-beta r*t^4) (speed r) 1 := by
      simpa only [one_pow, mul_one, beta_speed hr] using hp 1
    have ht1 : HasDerivAt (fun t => edge r+speed r*tail r t) (speed r) 1 := by
      simpa using ht 1 (by norm_num)
    have he : (1:ℝ)^2-beta r*1^4=edge r+speed r*tail r 1 := by simp [tail_one, edge]
    have hh := hasDerivAt_if_le hp1 ht1 he
    simpa only [position, velocity, le_refl, if_true, one_pow, mul_one, beta_speed hr] using hh
  · rw [velocity, if_neg (not_le.mpr hgt)]
    apply (ht t (by linarith)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hgt] with s hs
    simp only [position, if_neg (not_le.mpr hs)]

lemma velocity_hasDerivAt (hr : 0<r) (t : ℝ) :
    HasDerivAt (velocity r) (acceleration r t) t := by
  have hp (s : ℝ) : HasDerivAt (fun t : ℝ => 2*t-4*beta r*t^3)
      (2-12*beta r*s^2) s := by
    convert ((hasDerivAt_id s).const_mul 2).sub (((hasDerivAt_id s).pow 3).const_mul (4*beta r)) using 1
    simp only [id_eq, Nat.cast_ofNat, pow_one]
    ring
  have ht (s : ℝ) (hs : 0<s) :
      HasDerivAt (fun t => speed r*t^(-r)) (-(r*speed r)*s^(-r-1)) s := by
    convert (Real.hasDerivAt_rpow_const (p := -r) (Or.inl hs.ne')).const_mul (speed r) using 1
    ring
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · rw [acceleration, if_pos hlt.le]
    apply (hp t).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hlt] with s hs
    simp only [velocity, if_pos hs.le]
  · subst t
    have hp1 : HasDerivAt (fun t : ℝ => 2*t-4*beta r*t^3) (-r*speed r) 1 := by
      simpa only [one_pow, mul_one, beta_accel hr] using hp 1
    have ht1 : HasDerivAt (fun t => speed r*t^(-r)) (-r*speed r) 1 := by
      convert ht 1 (by norm_num) using 1
      simp
    have he : 2*(1:ℝ)-4*beta r*1^3=speed r*1^(-r) := by
      simp only [one_pow, mul_one, Real.one_rpow]
      exact beta_speed hr
    have hh := hasDerivAt_if_le hp1 ht1 he
    simpa only [velocity, acceleration, le_refl, if_true, one_pow, mul_one, beta_accel hr] using hh
  · rw [acceleration, if_neg (not_le.mpr hgt)]
    apply (ht t (by linarith)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hgt] with s hs
    simp only [velocity, if_neg (not_le.mpr hs)]

lemma tail_nonneg (hr1 : r≤1) {t : ℝ} (ht : 1≤t) : 0≤tail r t := by
  by_cases he : r=1
  · simp only [tail, if_pos he]
    exact Real.log_nonneg ht
  · have hpow : 1≤t^(1-r) := Real.one_le_rpow ht (by linarith)
    simp only [tail, if_neg he]
    exact div_nonneg (sub_nonneg.mpr hpow) (by linarith)

lemma force_on_first_segment (hr : 0<r) (hr1 : r≤1) {t : ℝ} (ht : t∈Icc 0 1) :
    force r (t^2-beta r*t^4)=2*(r+1)*(1-t^2) := by
  have hb := beta_bounds hr hr1
  have ht2 : 0≤t^2 ∧ t^2≤1 := ⟨sq_nonneg _, by nlinarith [ht.1, ht.2]⟩
  have hq0 : 0≤t^2-beta r*t^4 := by
    have hm := mul_le_mul_of_nonneg_left ht2.2 hb.1.le
    nlinarith [mul_nonneg ht2.1 (show 0≤1-beta r*t^2 by nlinarith)]
  have hq1 : t^2-beta r*t^4≤edge r := by
    unfold edge
    have hm := mul_nonneg (sub_nonneg.mpr ht2.2)
      (show 0≤1-beta r*(1+t^2) by nlinarith [mul_le_mul_of_nonneg_left ht2.2 hb.1.le])
    nlinarith
  have hs : 0≤1-2*beta r*t^2 := by nlinarith [mul_le_mul_of_nonneg_left ht2.2 hb.1.le]
  have hroot : root r (t^2-beta r*t^4)=1-2*beta r*t^2 := by
    rw [root, clip_eq_self hr hr1 ⟨hq0,hq1⟩]
    have he : 1-4*beta r*(t^2-beta r*t^4)=(1-2*beta r*t^2)^2 := by ring
    rw [he, Real.sqrt_sq hs]
  unfold force
  rw [hroot]
  field_simp [hb.1.ne']

lemma ode_identity (hr : 0<r) (hr1 : r≤1) {t : ℝ} (ht : 0<t) :
    acceleration r t= -(r/t)*velocity r t+force r (position r t) := by
  by_cases ht1 : t≤1
  · simp only [acceleration, velocity, position, if_pos ht1]
    rw [force_on_first_segment hr hr1 ⟨ht.le,ht1⟩]
    unfold beta
    field_simp
    ring
  · have htp : 1≤t := (lt_of_not_ge ht1).le
    have hq : edge r≤position r t := by
      simp only [position, if_neg ht1]
      exact le_add_of_nonneg_right (mul_nonneg (speed_pos hr).le (tail_nonneg hr1 htp))
    rw [force_eq_zero hr hr1 hq]
    simp only [acceleration, velocity, if_neg ht1, add_zero]
    rw [Real.rpow_sub ht, Real.rpow_one]
    ring

lemma position_tendsto (hr : 0<r) (hr1 : r≤1) :
    Tendsto (position r) atTop atTop := by
  have htail : Tendsto (tail r) atTop atTop := by
    by_cases he : r=1
    · subst r
      have heq : tail 1 = Real.log := by funext s; simp [tail]
      rw [heq]
      exact Real.tendsto_log_atTop
    · have hpos : 0<1-r := by apply sub_pos.mpr; exact lt_of_le_of_ne hr1 he
      have hp := tendsto_rpow_atTop hpos
      have hm : Tendsto (fun t : ℝ => t^(1-r)-1) atTop atTop := by
        simpa only [sub_eq_add_neg] using hp.atTop_add (tendsto_const_nhds (x := (-1:ℝ)))
      have hd := hm.atTop_div_const hpos
      have heq : tail r = fun s => (s^(1-r)-1)/(1-r) := by
        funext s
        exact if_neg he
      rw [heq]
      exact hd
  have hh : Tendsto (fun t => edge r+speed r*tail r t) atTop atTop :=
    (tendsto_const_nhds (x := edge r)).add_atTop (htail.const_mul_atTop (speed_pos hr))
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
  simp only [position, if_neg (not_le.mpr ht)]

@[simp] lemma position_zero (r : ℝ) : position r 0=0 := by norm_num [position]
@[simp] lemma velocity_zero (r : ℝ) : velocity r 0=0 := by norm_num [velocity]

#print axioms ode_identity
#print axioms position_tendsto
end NesterovLowDamping
