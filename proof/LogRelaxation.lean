module
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! An analytic auxiliary lemma, not a formalization of the Markov theorem. -/
namespace UnicyclicLog
noncomputable section
set_option maxHeartbeats 1000000

def gap (r : ℝ) : ℝ :=
  2*r + (2/3 : ℝ)*r^3 + (2/5 : ℝ)*r^5 +
    2*r^7/(7*(1-r^2)) - Real.log (1+r) + Real.log (1-r)

theorem gap_deriv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasDerivAt gap (4*r^8/(7*(1-r^2)^2)) r := by
  have hp : 0 < 1+r := by linarith
  have hm : 0 < 1-r := by linarith
  have hsq : 0 < 1-r^2 := by nlinarith
  have hd : 7*(1-r^2) ≠ 0 := ne_of_gt (mul_pos (by norm_num) hsq)
  have hi := hasDerivAt_id r
  have hd' : HasDerivAt (fun x : ℝ => 7*(1-x^2)) (-14*r) r := by
    convert (((hasDerivAt_const r (1 : ℝ)).sub (hi.pow 2)).const_mul 7) using 1 <;>
      (try simp only [id_eq, Pi.sub_apply, Pi.pow_apply]) <;> ring
  have hq := ((hi.pow 7).const_mul 2).div hd' hd
  have hlp := (hi.const_add 1).log (ne_of_gt hp)
  have hlm := ((hasDerivAt_const r (1 : ℝ)).sub hi).log (ne_of_gt hm)
  have ht := (((((hi.const_mul 2).add ((hi.pow 3).const_mul (2/3 : ℝ))).add
    ((hi.pow 5).const_mul (2/5 : ℝ))).add hq).sub hlp).add hlm
  convert ht using 1
  · funext x
    simp only [gap, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, id_eq]
  · simp only [id_eq, Pi.sub_apply, Pi.pow_apply]
    field_simp [ne_of_gt hp, ne_of_gt hm, ne_of_gt hsq] <;> ring

theorem gap_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : 0 ≤ gap r := by
  have hh : ∀ x ∈ Set.Icc (0 : ℝ) r,
      HasDerivAt gap (4*x^8/(7*(1-x^2)^2)) x := by
    intro x hx
    exact gap_deriv hx.1 (lt_of_le_of_lt hx.2 hr1)
  have hc : ContinuousOn gap (Set.Icc (0 : ℝ) r) := by
    intro x hx
    exact (hh x hx).continuousAt.continuousWithinAt
  have hm : MonotoneOn gap (Set.Icc (0 : ℝ) r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r) hc
      (fun x hx => (hh x (interior_subset hx)).hasDerivWithinAt)
      (fun x _ => by positivity)
  have h := hm ⟨le_rfl, hr0⟩ ⟨hr0, le_rfl⟩ hr0
  simpa [gap] using h

theorem log_ratio_upper {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.log ((1+r)/(1-r)) ≤
      2*r+(2/3 : ℝ)*r^3+(2/5 : ℝ)*r^5+2*r^7/(7*(1-r^2)) := by
  have hp : 1+r ≠ 0 := by linarith
  have hm : 1-r ≠ 0 := by linarith
  rw [Real.log_div hp hm]
  have h := gap_nonneg hr0 hr1
  dsimp [gap] at h
  linarith

#print axioms UnicyclicLog.log_ratio_upper
end
end UnicyclicLog
