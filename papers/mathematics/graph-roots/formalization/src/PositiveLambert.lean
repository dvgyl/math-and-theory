import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

noncomputable section
namespace SquareFlowerCompletion.Radius

theorem mul_exp_strictMonoOn : StrictMonoOn (fun x : ℝ => x * Real.exp x) (Set.Ici 0) := by
  intro x hx y hy hxy
  have he : Real.exp x < Real.exp y := Real.exp_lt_exp.mpr hxy
  exact (mul_lt_mul_of_pos_right hxy (Real.exp_pos x)).trans_le
    (mul_le_mul_of_nonneg_left he.le hy)

theorem exists_positive_lambert (s : ℝ) (hs : 0 < s) :
    ∃ w : ℝ, 0 < w ∧ w * Real.exp w = s := by
  have he : 1 ≤ Real.exp s := Real.one_le_exp_iff.mpr hs.le
  have hb : s ≤ s * Real.exp s := by nlinarith
  have hc : Continuous (fun x : ℝ => x * Real.exp x) := continuous_id.mul Real.continuous_exp
  obtain ⟨w, hw, heq⟩ := intermediate_value_Icc hs.le hc.continuousOn
    (show s ∈ Set.Icc ((0 : ℝ) * Real.exp 0) (s * Real.exp s) by simpa using And.intro hs.le hb)
  refine ⟨w, ?_, heq⟩
  by_contra h
  have hw0 : w = 0 := le_antisymm (le_of_not_gt h) hw.1
  simp [hw0] at heq
  linarith

def positiveLambert (s : ℝ) : ℝ :=
  if hs : 0 < s then Classical.choose (exists_positive_lambert s hs) else 0

theorem positiveLambert_spec {s : ℝ} (hs : 0 < s) :
    0 < positiveLambert s ∧ positiveLambert s * Real.exp (positiveLambert s) = s := by
  simpa [positiveLambert, hs] using Classical.choose_spec (exists_positive_lambert s hs)

theorem positiveLambert_unique {s w : ℝ} (hs : 0 < s) (hw : 0 < w)
    (heq : w * Real.exp w = s) : w = positiveLambert s := by
  apply mul_exp_strictMonoOn.injOn hw.le (positiveLambert_spec hs).1.le
  exact heq.trans (positiveLambert_spec hs).2.symm

theorem positiveLambert_log_equation {s : ℝ} (hs : 0 < s) :
    positiveLambert s + Real.log (positiveLambert s) = Real.log s := by
  have h := congrArg Real.log (positiveLambert_spec hs).2
  rw [Real.log_mul (ne_of_gt (positiveLambert_spec hs).1) (ne_of_gt (Real.exp_pos _)),
    Real.log_exp] at h
  linarith

theorem exp_positiveLambert {s : ℝ} (hs : 0 < s) :
    Real.exp (positiveLambert s) = s / positiveLambert s := by
  apply (eq_div_iff (ne_of_gt (positiveLambert_spec hs).1)).mpr
  simpa [mul_comm] using (positiveLambert_spec hs).2

#print axioms mul_exp_strictMonoOn
#print axioms exists_positive_lambert
#print axioms positiveLambert_spec
#print axioms positiveLambert_unique
#print axioms positiveLambert_log_equation
#print axioms exp_positiveLambert
end SquareFlowerCompletion.Radius
