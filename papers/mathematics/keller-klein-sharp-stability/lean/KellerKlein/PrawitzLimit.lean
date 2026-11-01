import KellerKlein.PrawitzRecurrence
import KellerKlein.PrawitzOscillation

noncomputable section
open MeasureTheory Filter Topology
open Causalean.Stat.CLT.BerryEsseen

namespace KellerKlein

theorem prawitzA_nat_add_one (n : ℕ) : prawitzA ((n : ℝ) + 1) = 1 := by
  induction n with
  | zero => simpa using prawitzA_one
  | succ n ih =>
    have hp : 0 < (n : ℝ) + 1 := by positivity
    have hs : Real.sin (Real.pi * ((n : ℝ)+1)) = 0 := by
      rw [mul_add, mul_one, Real.sin_add_pi, mul_comm Real.pi (n : ℝ),
        Real.sin_nat_mul_pi]
      simp
    have h := prawitzA_shift hp
    rw [hs] at h
    simp only [zero_div, zero_pow (by decide : 2 ≠ 0), sub_eq_zero] at h
    norm_num only [Nat.cast_add, Nat.cast_one] at *
    linarith

theorem prawitzA_difference_integral (x y : ℝ) :
    prawitzA (x+y) - prawitzA y = 4 *
      ∫ t in (0 : ℝ)..1, (prawitzSineWeight t * Real.sin (Real.pi * x * t)) *
        Real.cos (2 * Real.pi * t * (y + x/2)) := by
  rw [prawitzA_eq (x+y), prawitzA_eq y, ← mul_sub,
    ← intervalIntegral.integral_sub (prawitzA_integrand_integrable (x+y))
      (prawitzA_integrand_integrable y)]
  have heq : (fun t : ℝ =>
      prawitzSineWeight t * Real.sin (2 * Real.pi * (x+y) * t) -
        prawitzSineWeight t * Real.sin (2 * Real.pi * y * t)) =
      (fun t : ℝ => 2 * ((prawitzSineWeight t * Real.sin (Real.pi * x * t)) *
        Real.cos (2 * Real.pi * t * (y+x/2)))) := by
    funext t
    rw [← mul_sub, Real.sin_sub_sin]
    rw [show (2*Real.pi*(x+y)*t-2*Real.pi*y*t)/2=Real.pi*x*t by ring,
      show (2*Real.pi*(x+y)*t+2*Real.pi*y*t)/2=2*Real.pi*t*(y+x/2) by ring]
    ring
  rw [heq, intervalIntegral.integral_const_mul]
  ring

theorem prawitzA_tendsto_nat_add (x : ℝ) :
    Tendsto (fun n : ℕ => prawitzA (x + (n : ℝ))) atTop (𝓝 1) := by
  have hi : IntervalIntegrable
      (fun t : ℝ => prawitzSineWeight t * Real.sin (Real.pi*x*t)) volume 0 1 := by
    simpa only [mul_comm (Real.pi*x)] using prawitz_sine_intervalIntegrable (Real.pi*x)
  have hfreq : Tendsto (fun n : ℕ => (n : ℝ)+1+x/2) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hz := ((tendsto_intervalIntegral_mul_cos_atTop hi).comp hfreq).const_mul 4
  have heq (n : ℕ) :
      4 * (∫ t in (0 : ℝ)..1,
        (prawitzSineWeight t * Real.sin (Real.pi*x*t)) *
          Real.cos (2*Real.pi*t*((n : ℝ)+1+x/2))) =
        prawitzA (x+((n : ℝ)+1)) - 1 := by
    rw [← prawitzA_difference_integral x ((n : ℝ)+1), prawitzA_nat_add_one]
  simp only [Function.comp_apply, heq, mul_zero] at hz
  have h := hz.add_const 1
  simp only [sub_add_cancel, zero_add] at h
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using h

def prawitzS (x : ℝ) : ℝ := (Real.sin (Real.pi*x)/Real.pi)^2

theorem prawitzS_add_one (x : ℝ) : prawitzS (x+1) = prawitzS x := by
  simp only [prawitzS, mul_add, mul_one, Real.sin_add_pi, neg_div, neg_sq]

theorem prawitzS_add_nat (x : ℝ) (n : ℕ) : prawitzS (x+(n : ℝ)) = prawitzS x := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc, prawitzS_add_one] using ih

theorem prawitzA_monotone_nat {x : ℝ} (hx : 0 < x) :
    Monotone (fun n : ℕ => prawitzA (x+(n : ℝ))) := by
  apply monotone_nat_of_le_succ
  intro n
  have hp : 0 < x+(n : ℝ) := add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg n)
  have h := prawitzA_shift hp
  have hn : 0 ≤ (Real.sin (Real.pi*(x+(n : ℝ)))/Real.pi)^2 /
      ((x+(n : ℝ))^2*(x+(n : ℝ)+1)^2) := by positivity
  simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
  linarith

theorem prawitzA_le_one {x : ℝ} (hx : 0 < x) : prawitzA x ≤ 1 := by
  simpa using (prawitzA_monotone_nat hx).ge_of_tendsto (prawitzA_tendsto_nat_add x) 0

theorem prawitzA_plus_tail_shift {x : ℝ} (hx : 0 < x) :
    prawitzA (x+1) + prawitzS (x+1)/(x+1)^2 ≤ prawitzA x+prawitzS x/x^2 := by
  rw [prawitzS_add_one]
  have hx1 : 0 < x+1 := by linarith
  have hs : 0 ≤ prawitzS x := by unfold prawitzS; positivity
  have h := prawitzA_shift hx
  change prawitzA (x+1)-prawitzA x=prawitzS x/(x^2*(x+1)^2) at h
  have hd : prawitzS x/(x^2*(x+1)^2)+prawitzS x/(x+1)^2 ≤ prawitzS x/x^2 := by
    have heq : prawitzS x/x^2 -
        (prawitzS x/(x^2*(x+1)^2)+prawitzS x/(x+1)^2) =
        2*prawitzS x/(x*(x+1)^2) := by
      field_simp
      ring
    have hh : 0 ≤ 2*prawitzS x/(x*(x+1)^2) := by positivity
    linarith
  linarith

theorem prawitzA_plus_tail_antitone_nat {x : ℝ} (hx : 0 < x) :
    Antitone (fun n : ℕ => prawitzA (x+(n : ℝ))+
      prawitzS (x+(n : ℝ))/(x+(n : ℝ))^2) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := prawitzA_plus_tail_shift (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg n))
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h

theorem one_le_prawitzA_plus_tail {x : ℝ} (hx : 0 < x) :
    1 ≤ prawitzA x+prawitzS x/x^2 := by
  have hinv : Tendsto (fun n : ℕ => (1:ℝ)/(x+(n : ℝ))) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have htail : Tendsto (fun n : ℕ => prawitzS (x+(n : ℝ))/(x+(n : ℝ))^2)
      atTop (𝓝 0) := by
    have h := (hinv.pow 2).const_mul (prawitzS x)
    simpa only [prawitzS_add_nat, div_pow, one_pow, mul_zero, zero_pow (by decide : 2 ≠ 0),
      mul_one_div] using h
  have h := (prawitzA_tendsto_nat_add x).add htail
  simpa using (prawitzA_plus_tail_antitone_nat hx).le_of_tendsto h 0

end KellerKlein
