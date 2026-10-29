import SquareEstimate
import Mathlib.Analysis.Polynomial.Basic

noncomputable section
open Polynomial Filter
open scoped Topology
namespace PowerRank

/-- Real constituent polynomials, evaluated at the original integer argument. -/
def EventuallyQuasipolynomial (f : ℕ → ℝ) : Prop :=
  ∃ (l : ℕ) (hl : 0 < l), ∃ P : Fin l → ℝ[X], ∃ N : ℕ,
    ∀ M ≥ N, f M = (P ⟨M % l, Nat.mod_lt M hl⟩).eval (M : ℝ)

/-- A positive square-root correction cannot agree with a real polynomial
on any cofinal positive sequence, even with a bounded error. -/
theorem polynomial_not_sqrt_approx (p : ℝ[X]) (x : ℕ → ℝ)
    (hx : Tendsto x atTop atTop) (c : ℝ) (hc : 0 < c)
    (herror : ∀ᶠ n in atTop, |p.eval (x n) - c * Real.sqrt (x n)| ≤ 2) : False := by
  have hsqrt := Real.tendsto_sqrt_atTop.comp hx
  have hpTop : Tendsto (fun n => p.eval (x n)) atTop atTop := by
    have hlower : Tendsto (fun n => c * Real.sqrt (x n) - 2) atTop atTop := by
      simpa only [sub_eq_add_neg, Function.comp_def] using
        (tendsto_atTop_add_const_right atTop (-2 : ℝ) (hsqrt.const_mul_atTop hc))
    apply tendsto_atTop_mono' atTop _ hlower
    filter_upwards [herror] with n hn
    have h := (abs_le.mp hn).1
    linarith
  have hratio : Tendsto (fun n => p.eval (x n) / x n) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n => c * (Real.sqrt (x n))⁻¹ + 2 * (x n)⁻¹)
        atTop (𝓝 0) := by
      simpa using ((tendsto_inv_atTop_zero.comp hsqrt).const_mul c).add
        ((tendsto_inv_atTop_zero.comp hx).const_mul 2)
    have habs : Tendsto (fun n => |p.eval (x n) / x n|) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _)) _ hupper
      filter_upwards [herror, hx.eventually (eventually_gt_atTop 0)] with n hn hxn
      have htri : |p.eval (x n)| ≤ c * Real.sqrt (x n) + 2 := by
        have h := abs_add_le (p.eval (x n) - c * Real.sqrt (x n)) (c * Real.sqrt (x n))
        rw [sub_add_cancel] at h
        rw [abs_of_nonneg (mul_nonneg hc.le (Real.sqrt_nonneg _))] at h
        linarith
      rw [abs_div, abs_of_pos hxn]
      calc
        _ ≤ (c * Real.sqrt (x n) + 2) / x n := (div_le_div_iff_of_pos_right hxn).mpr htri
        _ = _ := by rw [add_div, mul_div_assoc, Real.sqrt_div_self]; ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using habs.neg) habs
      (Eventually.of_forall (fun n => neg_abs_le _))
      (Eventually.of_forall (fun n => le_abs_self _))
  by_cases hzero : p.natDegree = 0
  · have hpconst : p = C (p.coeff 0) := p.eq_C_of_natDegree_eq_zero hzero
    conv at hpTop => arg 1; intro n; rw [hpconst, eval_C]
    exact not_tendsto_const_atTop _ _ hpTop
  · have hpne : p ≠ 0 := by intro h; simp [h] at hzero
    have hdeg : 1 ≤ p.natDegree := by omega
    by_cases hone : p.natDegree = 1
    · have hd : p.degree = (X : ℝ[X]).degree := by
        rw [degree_eq_natDegree hpne, hone, degree_X]
        rfl
      have hlim := (p.div_tendsto_atTop_leadingCoeff_div_of_degree_eq X hd).comp hx
      simp only [eval_X, leadingCoeff_X, div_one, Function.comp_def] at hlim
      have heq : p.leadingCoeff = 0 := tendsto_nhds_unique hlim hratio
      exact hpne (leadingCoeff_eq_zero.mp heq)
    · have hd : (X : ℝ[X]).degree < p.degree := by
        rw [degree_eq_natDegree hpne, degree_X]
        exact_mod_cast (show 1 < p.natDegree by omega)
      have hlim := (p.abs_div_tendsto_atTop_atTop_of_degree_gt X hd X_ne_zero).comp hx
      simp only [eval_X] at hlim
      exact not_tendsto_atTop_of_tendsto_nhds (hratio.abs) hlim

/-- The exact rank sequence has no eventual quasipolynomial description with
real coefficients. The zero residue alone already contradicts the estimate. -/
theorem mainPower_not_eventuallyQuasipolynomial :
    ¬ EventuallyQuasipolynomial (fun M => (recurrenceRank (mainPowerSequence M) : ℝ)) := by
  rintro ⟨l, hl, P, N, hP⟩
  let cubic : ℝ[X] := (X + 1) * (2 * X + 1) * (7 * X + 6) * C (1 / 6)
  let p : ℝ[X] := cubic - P ⟨0, hl⟩
  let x : ℕ → ℝ := fun n => ((l * n : ℕ) : ℝ)
  have hx : Tendsto x atTop atTop := by
    dsimp [x]
    simp only [Nat.cast_mul]
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by exact_mod_cast hl)
  apply polynomial_not_sqrt_approx p x hx (Real.sqrt 3 - 1)
  · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  · filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hln : n ≤ l * n := by nlinarith
    have hM : N ≤ l * n := le_trans (le_trans (le_max_left N 1) hn) hln
    have hpos : 1 ≤ l * n := le_trans (le_trans (le_max_right N 1) hn) hln
    have h := mainPower_sqrt_error (l * n) hpos
    have heval : p.eval (x n) = rankCubicValue (l * n) -
        (recurrenceRank (mainPowerSequence (l * n)) : ℝ) := by
      have hPeq := hP (l * n) hM
      dsimp only at hPeq
      rw [hPeq]
      simp [p, cubic, x, rankCubicValue]
      ring
    simpa only [heval, x] using h

end PowerRank
