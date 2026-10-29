module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact polynomial inequalities for the actual scalar hinge used in the
smooth strongly convex ADMM counterexample. -/

namespace ADMMHinge
noncomputable section

def psi (t : ℝ) : ℝ :=
  if t ≤ -1 then 0 else if t ≤ 0 then (t + 1)^3 - (t + 1)^4 / 2 else t + 1 / 2

theorem psi_zero_below (t : ℝ) (h : t ≤ -1) : psi t = 0 := by
  simp [psi, h]

theorem psi_zero : psi 0 = 1 / 2 := by norm_num [psi]

theorem psi_nonneg (t : ℝ) : 0 ≤ psi t := by
  unfold psi
  split_ifs with hneg hnonpos
  · exact le_rfl
  · have hbase : 0 ≤ t + 1 := by linarith
    have hfactor : 0 ≤ 1 - (t + 1) / 2 := by linarith
    calc
      0 ≤ (t + 1)^3 * (1 - (t + 1) / 2) :=
        mul_nonneg (pow_nonneg hbase 3) hfactor
      _ = (t + 1)^3 - (t + 1)^4 / 2 := by ring
  · linarith

theorem psi_support (t : ℝ) : t + 1 / 2 ≤ psi t := by
  unfold psi
  split_ifs with hneg hnonpos
  · linarith
  · have hleft : 0 ≤ -t := by linarith
    have hright : 0 ≤ t + 2 := by linarith
    have hprod : 0 ≤ (-t)^3 * (t + 2) / 2 :=
      div_nonneg (mul_nonneg (pow_nonneg hleft 3) hright) (by norm_num)
    have hid : (t + 1)^3 - (t + 1)^4 / 2 - (t + 1 / 2) =
        (-t)^3 * (t + 2) / 2 := by ring
    linarith
  · exact le_rfl

end
end ADMMHinge

#print axioms ADMMHinge.psi_support
