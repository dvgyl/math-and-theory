import NAGBasic
import HighDamping

noncomputable section
open Set InnerProductSpace
open scoped Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace DiscreteNesterov
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem quadratic_upper {F : E → ℝ} {G : E → E}
    (hG : ∀ x, HasGradientAt F (G x) x) (hL : LipschitzWith 1 G) (x y : E) :
    F y≤F x+⟪G x,y-x⟫_ℝ+‖y-x‖^2/2 := by
  let d := y-x
  let f : ℝ → ℝ := fun t => F (x+t • d)-t*⟪G x,d⟫_ℝ-t^2*‖d‖^2/2
  have hd (t : ℝ) : HasDerivAt f
      (⟪G (x+t • d),d⟫_ℝ-⟪G x,d⟫_ℝ-t*‖d‖^2) t := by
    have hp : HasDerivAt (fun t : ℝ => x+t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hf := (hG (x+t • d)).hasFDerivAt.comp_hasDerivAt t hp
    convert (hf.sub ((hasDerivAt_id t).mul_const ⟪G x,d⟫_ℝ)).sub
      ((((hasDerivAt_id t).pow 2).mul_const (‖d‖^2)).div_const 2) using 1 <;>
      simp only [toDual_apply, smul_eq_mul, id_eq] <;> ring
  have hn (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
      ⟪G (x+t • d),d⟫_ℝ-⟪G x,d⟫_ℝ-t*‖d‖^2≤0 := by
    have hl := hL.dist_le_mul (x+t • d) x
    simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hl
    have hsub : x+t • d-x=t • d := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at hl
    have hi := real_inner_le_norm (G (x+t • d)-G x) d
    rw [inner_sub_left] at hi
    nlinarith [mul_le_mul_of_nonneg_right hl (norm_nonneg d)]
  have hm : AntitoneOn f (Icc (0:ℝ) 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _) (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [(hd t).deriv]; exact hn t (by simpa using ht))
  have hb := hm (by simp) (by simp) (by norm_num : (0:ℝ)≤1)
  dsimp [f,d] at hb
  simp only [one_smul, zero_smul, add_zero, add_sub_cancel, one_mul, zero_mul,
    one_pow, zero_pow (by decide : 2≠0), zero_div, sub_zero] at hb
  linarith

end DiscreteNesterov
