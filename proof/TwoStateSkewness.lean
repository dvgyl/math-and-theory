module
public import CumulantAlgebra
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
The two-state cycle, represented by two parallel reaction edges, has the
quadratic characteristic polynomial X² + (u0+u1+v0+v1)X.  This file checks
the stronger coefficient-ratio interval [1/4,1] for that small boundary
case. It is a completeness lemma, not the new arbitrary-size argument.
-/

namespace UnicyclicTwoState

noncomputable section

open UnicyclicCumulant

theorem quadratic_skewness_formula (a U V : ℝ) (ha : a ≠ 0) (hUV : U ≠ V) :
    third a 1 0 U V / first a U V =
      1-6*(U+V)/a^2+12*(U-V)^2/a^4 := by
  have hd : U-V ≠ 0 := sub_ne_zero.mpr hUV
  dsimp [third,second,first]
  field_simp [ha,hd]
  ring

theorem quadratic_scalar_interval (a α β : ℝ)
    (ha : 0<a) (hα : 0≤α) (hβ : 0≤β) (hab : 2*(α+β)≤a) :
    (1/4 : ℝ) ≤ 1-6*(α^2+β^2)/a^2+12*(α^2-β^2)^2/a^4 ∧
      1-6*(α^2+β^2)/a^2+12*(α^2-β^2)^2/a^4 ≤ 1 := by
  have hs : 0≤α+β := add_nonneg hα hβ
  have hp : 0≤α*β := mul_nonneg hα hβ
  have ha2 : 4*(α+β)^2≤a^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hab) (by positivity : 0≤a+2*(α+β))
    nlinarith only [hh]
  have hc : (α-β)^2≤(α+β)^2 := by nlinarith only [hp]
  have hlower := mul_nonneg (sub_nonneg.mpr ha2)
    (show 0≤a^2-4*(α-β)^2 by nlinarith only [ha2,hc])
  have hsum : 0≤α^2+β^2 := add_nonneg (sq_nonneg α) (sq_nonneg β)
  have hgap : 0≤a^2-2*(α^2+β^2) := by nlinarith only [ha2,hp,hsum]
  have hupper := mul_nonneg hsum hgap
  have hcross : 0≤α^2*β^2 := mul_nonneg (sq_nonneg α) (sq_nonneg β)
  have ha4 : 0<a^4 := pow_pos ha 4
  have heq : 1-6*(α^2+β^2)/a^2+12*(α^2-β^2)^2/a^4 =
      (a^4-6*(α^2+β^2)*a^2+12*(α^2-β^2)^2)/a^4 := by
    field_simp [ne_of_gt ha]
    ring
  rw [heq]
  constructor
  · apply (le_div_iff₀ ha4).mpr
    nlinarith only [hlower]
  · apply (div_le_iff₀ ha4).mpr
    nlinarith only [hupper,hcross]

theorem two_state_coefficient_skewness_interval
    (u0 u1 v0 v1 : ℝ) (hu0 : 0<u0) (hu1 : 0<u1)
    (hv0 : 0<v0) (hv1 : 0<v1) (hUV : u0*u1 ≠ v0*v1) :
    let a := u0+u1+v0+v1
    (1/4 : ℝ) ≤ third a 1 0 (u0*u1) (v0*v1) / first a (u0*u1) (v0*v1) ∧
      third a 1 0 (u0*u1) (v0*v1) / first a (u0*u1) (v0*v1) ≤ 1 := by
  dsimp only
  have ha : 0<u0+u1+v0+v1 := by positivity
  rw [quadratic_skewness_formula _ _ _ (ne_of_gt ha) hUV]
  have hα := Real.sqrt_nonneg (u0*u1)
  have hβ := Real.sqrt_nonneg (v0*v1)
  have hα2 := Real.sq_sqrt (mul_pos hu0 hu1).le
  have hβ2 := Real.sq_sqrt (mul_pos hv0 hv1).le
  have hαsum : 2*Real.sqrt (u0*u1)≤u0+u1 := by
    nlinarith [sq_nonneg (u0-u1)]
  have hβsum : 2*Real.sqrt (v0*v1)≤v0+v1 := by
    nlinarith [sq_nonneg (v0-v1)]
  have hab : 2*(Real.sqrt (u0*u1)+Real.sqrt (v0*v1))≤u0+u1+v0+v1 := by
    linarith only [hαsum,hβsum]
  simpa only [hα2,hβ2] using quadratic_scalar_interval
    (u0+u1+v0+v1) (Real.sqrt (u0*u1)) (Real.sqrt (v0*v1)) ha hα hβ hab

#print axioms two_state_coefficient_skewness_interval

end
end UnicyclicTwoState
