import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace DiscreteNesterov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Stability of one actual extrapolated-gradient step against two ODE samples.
The only consistency assumptions are the displayed Taylor remainders. -/
theorem extrapolated_step_error {G : E → E} (hG : LipschitzWith 1 G)
    {h β η U : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hη : 0 ≤ η)
    {z w y zn wn q u qn un : E}
    (hy : y = z + (h * β) • w)
    (hv : wn = β • w - h • G y)
    (hx : zn = z + h • wn)
    (hU : ‖u‖ ≤ U)
    (hvr : ‖un - β • u + h • G q‖ ≤ h * η)
    (hqr : ‖qn - q - h • un‖ ≤ h * η) :
    ‖zn - qn‖ + ‖wn - un‖ ≤
      (1 + 3*h) * (‖z - q‖ + ‖w - u‖) + h * (2*h*U + 3*η) := by
  have hU0 : 0 ≤ U := (norm_nonneg u).trans hU
  have hhb : 0 ≤ h * β := mul_nonneg hh.le hβ
  have hw : ‖w‖ ≤ ‖w - u‖ + U := by
    calc
      ‖w‖ = ‖w - u + u‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - u‖ + ‖u‖ := norm_add_le _ _
      _ ≤ ‖w - u‖ + U := add_le_add_left hU _
  have harg : ‖y - q‖ ≤ ‖z - q‖ + (h * β) * ‖w‖ := by
    rw [hy, show z + (h * β) • w - q = (z - q) + (h * β) • w by module]
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hhb] using
      norm_add_le (z - q) ((h * β) • w)
  have hgrad : ‖G y - G q‖ ≤ ‖z - q‖ + h * β * (‖w - u‖ + U) := by
    have hg := hG.dist_le_mul y q
    simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hg
    exact hg.trans (harg.trans (add_le_add_left (mul_le_mul_of_nonneg_left hw hhb) _))
  have hvpre : ‖wn - un‖ ≤
      β * ‖w - u‖ + h * (‖z - q‖ + h * β * (‖w - u‖ + U)) + h * η := by
    have he : wn - un = β • (w - u) - h • (G y - G q) -
        (un - β • u + h • G q) := by rw [hv]; module
    calc
      ‖wn - un‖ ≤ ‖β • (w - u)‖ + ‖h • (G y - G q)‖ +
          ‖un - β • u + h • G q‖ := by
        rw [he]
        exact (norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
      _ = β * ‖w - u‖ + h * ‖G y - G q‖ + ‖un - β • u + h • G q‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hβ, abs_of_pos hh]
      _ ≤ β * ‖w - u‖ + h * (‖z - q‖ + h * β * (‖w - u‖ + U)) + h * η :=
        add_le_add (add_le_add_left (mul_le_mul_of_nonneg_left hgrad hh.le) _) hvr
  have hvbound : ‖wn - un‖ ≤
      (1+h^2) * ‖w - u‖ + h * ‖z - q‖ + h^2 * U + h * η := by
    have hbD := mul_le_mul_of_nonneg_right hβ1 (norm_nonneg (w - u))
    have hbW := mul_le_mul_of_nonneg_right hβ1
      (show 0 ≤ h^2 * (‖w - u‖ + U) by positivity)
    nlinarith only [hvpre, hbD, hbW]
  have hpbound : ‖zn - qn‖ ≤ ‖z - q‖ + h * ‖wn - un‖ + h * η := by
    have he : zn - qn = (z - q) + h • (wn - un) - (qn - q - h • un) := by
      rw [hx]
      module
    calc
      ‖zn - qn‖ ≤ ‖z - q‖ + ‖h • (wn - un)‖ + ‖qn - q - h • un‖ := by
        rw [he]
        exact (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ = ‖z - q‖ + h * ‖wn - un‖ + ‖qn - q - h • un‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      _ ≤ ‖z - q‖ + h * ‖wn - un‖ + h * η := add_le_add_left hqr _
  have hh2 : h^2 ≤ h := by nlinarith only [hh.le, hh1]
  have hh3 : h^3 ≤ h^2 := by
    have hm := mul_le_mul_of_nonneg_left hh2 hh.le
    nlinarith only [hm]
  have hWcoef : (1+h)*(1+h^2) ≤ 1+3*h := by nlinarith only [hh2, hh3]
  have hZcoef : 1+(1+h)*h ≤ 1+3*h := by nlinarith only [hh2, hh.le]
  have hUcoef : (1+h)*h^2 ≤ 2*h^2 := by nlinarith only [hh3]
  have hηcoef : (1+h)*h+h ≤ 3*h := by nlinarith only [hh2]
  have hmW := mul_le_mul_of_nonneg_right hWcoef (norm_nonneg (w-u))
  have hmZ := mul_le_mul_of_nonneg_right hZcoef (norm_nonneg (z-q))
  have hmU := mul_le_mul_of_nonneg_right hUcoef hU0
  have hmη := mul_le_mul_of_nonneg_right hηcoef hη
  have hmv := mul_le_mul_of_nonneg_left hvbound (show 0 ≤ 1+h by linarith only [hh])
  nlinarith only [hpbound, hmv, hmW, hmZ, hmU, hmη]

/-- A discrete Gronwall estimate whose constants do not contain the singular
damping coefficient r/t. -/
theorem finite_discrete_gronwall {e : ℕ → ℝ} {h D T : ℝ} {N : ℕ}
    (hh : 0 ≤ h) (hD : 0 ≤ D) (he0 : 0 ≤ e 0)
    (hNT : (N : ℝ) * h ≤ T)
    (hstep : ∀ k < N, e (k+1) ≤ (1+3*h)*e k+h*D) :
    e N ≤ Real.exp (3*T) * (e 0+T*D) := by
  have hc : 1 ≤ 1+3*h := by linarith only [hh]
  have hpow : ∀ k ≤ N, e k ≤ (1+3*h)^k * (e 0+(k:ℝ)*h*D) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hkN : k < N := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hki : k ≤ N := hkN.le
      have h1 := mul_le_mul_of_nonneg_left (ih hki) (by linarith : 0 ≤ 1+3*h)
      have h2 := mul_le_mul_of_nonneg_right (one_le_pow₀ hc : 1 ≤ (1+3*h)^(k+1))
        (mul_nonneg hh hD)
      have hs := hstep k hkN
      rw [pow_succ] at h2 ⊢
      push_cast
      nlinarith only [hs, h1, h2]
  have hexp : (1+3*h)^N ≤ Real.exp (3*T) := by
    have hcExp : 1+3*h ≤ Real.exp (3*h) := by
      simpa only [add_comm] using Real.add_one_le_exp (3*h)
    calc
      (1+3*h)^N ≤ (Real.exp (3*h))^N :=
        pow_le_pow_left₀ (by linarith : 0 ≤ 1+3*h) hcExp N
      _ = Real.exp ((N:ℝ)*(3*h)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (3*T) := Real.exp_le_exp.mpr (by nlinarith only [hNT])
  have hbase : 0 ≤ e 0+(N:ℝ)*h*D := by positivity
  have hTD := mul_le_mul_of_nonneg_right hNT hD
  exact (hpow N le_rfl).trans
    ((mul_le_mul_of_nonneg_right hexp hbase).trans
      (mul_le_mul_of_nonneg_left (by linarith only [hTD]) (Real.exp_pos _).le))

end DiscreteNesterov
