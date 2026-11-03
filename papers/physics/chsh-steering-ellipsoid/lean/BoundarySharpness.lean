import CHSHQuantum

/-!
The actual rank-two separable density family behind the sharp uniform rigidity
exponent. The operators, all Pauli readouts, and purity deficit are checked.
The arbitrary-LU trace-norm lower bound is proved in the written report, not
claimed as a theorem of this module.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false

namespace BoundarySharpness
noncomputable section
open CHSHPhysical (Mat Vec Density outer quadratic pauli tensor)

def u (a b : ℝ) : Vec := ![(a : ℂ), 0, (b : ℂ), 0]
def v (a b : ℝ) : Vec := ![0, (a : ℂ), 0, (-b : ℂ)]
def state (a b : ℝ) : Mat := outer (u a b) + outer (v a b)
def centreZ (a b : ℝ) : ℝ := 2 * (a ^ 2 - b ^ 2)
def correl (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 4 * a * b; 0, 0, 0; 0, 0, 0]

theorem state_trace (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1 / 2) :
    (state a b).trace = 1 := by
  apply Complex.ext <;>
    norm_num [state, outer, u, v, Matrix.trace, Matrix.diag, Matrix.add_apply,
      Fin.sum_univ_four, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Matrix.one_apply, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.star_def, pow_two] <;> nlinarith

theorem state_is_density (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1 / 2) :
    Density (state a b) := by
  refine ⟨?_, state_trace a b h, ?_⟩
  · unfold state
    rw [Matrix.conjTranspose_add, CHSHPhysical.outer_hermitian,
      CHSHPhysical.outer_hermitian]
  · intro w
    unfold state quadratic
    rw [Matrix.add_mulVec, dotProduct_add]
    have h0 := CHSHPhysical.outer_quadratic_nonneg (u a b) w
    have h1 := CHSHPhysical.outer_quadratic_nonneg (v a b) w
    unfold quadratic at h0 h1
    simpa only [Complex.add_re] using add_nonneg h0 h1

theorem alice_readout (a b : ℝ) (i : Fin 3) :
    (state a b * tensor (pauli i) 1).trace =
      ((![0, 0, centreZ a b] i : ℝ) : ℂ) := by
  fin_cases i <;> apply Complex.ext <;>
    norm_num [state, outer, u, v, tensor, pauli, centreZ,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_four, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Matrix.one_apply, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.star_def, pow_two] <;> ring

theorem bob_readout (a b : ℝ) (i : Fin 3) :
    (state a b * tensor 1 (pauli i)).trace = 0 := by
  fin_cases i <;> apply Complex.ext <;>
    norm_num [state, outer, u, v, tensor, pauli,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_four, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Matrix.one_apply, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.star_def, pow_two]

theorem correlation_readout (a b : ℝ) (i j : Fin 3) :
    (state a b * tensor (pauli i) (pauli j)).trace = (correl a b i j : ℂ) := by
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [state, outer, u, v, tensor, pauli, correl,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_four, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Matrix.one_apply, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.star_def, pow_two] <;> ring

/-- The family is a scalar multiple of an orthogonal projection. -/
theorem projection_identity (a b : ℝ) :
    state a b * state a b = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) • state a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [state, outer, u, v, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Fin.sum_univ_four, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead,
      Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go,
      Fin.succ, Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.star_def, pow_two] <;> ring

/-- The nonzero eigenvalues are 1/2; this avoids a spectral API. -/
theorem half_projection (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1 / 2) :
    state a b * state a b = (1 / 2 : ℂ) • state a b := by
  rw [projection_identity, h]
  norm_num

theorem state_purity (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1 / 2) :
    (state a b * state a b).trace = (1 / 2 : ℂ) := by
  rw [half_projection a b h, Matrix.trace_smul, state_trace a b h]
  simp

theorem correlation_length (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1 / 2) :
    (4 * a * b) ^ 2 = 1 - centreZ a b ^ 2 := by
  have hh : (a ^ 2 + b ^ 2) ^ 2 = 1 / 4 := by rw [h]; norm_num
  unfold centreZ
  nlinarith only [hh]

theorem purity_deficit (c : ℝ) :
    1 - c + c ^ 2 / 2 - 1 / 2 = (1 - c) ^ 2 / 2 := by ring


open CertifiedCHSH

def ex : V := ![1, 0, 0]
def ez : V := ![0, 0, 1]

theorem ex_unit : Unit ex := by
  norm_num [CertifiedCHSH.Unit, nsq, dot, dotProduct, ex, Fin.sum_univ_three,
    Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]

theorem ez_unit : Unit ez := by
  norm_num [CertifiedCHSH.Unit, nsq, dot, dotProduct, ez, Fin.sum_univ_three,
    Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]

theorem image_norm (a b : ℝ) (x : V) :
    nsq ((correl a b).mulVec x) =
      0 * x 0 ^ 2 + 0 * x 1 ^ 2 + (4 * a * b) ^ 2 * x 2 ^ 2 := by
  norm_num [nsq, dot, dotProduct, Matrix.mulVec, correl,
    Fin.sum_univ_three, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
    Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff]
  ring

theorem plane_bound (a b : ℝ) : PlaneBound (correl a b).mulVec ((4 * a * b) ^ 2) := by
  simpa only [zero_add] using
    plane_of_diagonal_norm (correl a b).mulVec 0 0 ((4 * a * b) ^ 2)
      (le_refl 0) (sq_nonneg _) (image_norm a b)

theorem all_settings_upper (a b : ℝ) (u u' v v' : V)
    (hu : Unit u) (hu' : Unit u') (hv : Unit v) (hv' : Unit v') :
    modulus (expect (state a b) (bell u u' v v')) ≤ 2 * |4 * a * b| := by
  have hh := bell_norm_le_of_plane (state a b) (correl a b)
    (correlation_readout a b) ((4 * a * b) ^ 2) (sq_nonneg _) (plane_bound a b)
    u u' v v' hu hu' hv hv'
  simpa only [Real.sqrt_sq_eq_abs] using hh

theorem attaining_settings (a b : ℝ) :
    modulus (expect (state a b) (bell ex ex ez ez)) = 2 * |4 * a * b| := by
  rw [bell_norm_correlation (state a b) (correl a b) (correlation_readout a b)]
  have hi : dot ex ((correl a b).mulVec (ez + ez)) +
      dot ex ((correl a b).mulVec (ez - ez)) = 2 * (4 * a * b) := by
    norm_num [dot, dotProduct, Matrix.mulVec, correl, ex, ez,
      Fin.sum_univ_three, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff]
    ring
  rw [hi, abs_mul]
  norm_num

/-- Exact actual-operator CHSH supremum of the sharpness family. -/
theorem beta_exact (a b : ℝ) : beta (state a b) = 2 * |4 * a * b| := by
  unfold beta
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨ex, ex, ez, ez, ex_unit, ex_unit, ez_unit, ez_unit,
      (attaining_settings a b).symm⟩
  · intro z hz
    obtain ⟨u, u', v, v', hu, hu', hv, hv', rfl⟩ := hz
    exact all_settings_upper a b u u' v v' hu hu' hv hv'

/-- For a nonnegative centre coordinate, this is the actual canonical CHSH gap. -/
theorem centre_coordinate_gap (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1 / 2) :
    2 * (1 - centreZ a b) - beta (state a b) ^ 2 / 4 = (1 - centreZ a b) ^ 2 := by
  rw [beta_exact]
  have hk := correlation_length a b h
  have hab := sq_abs (4 * a * b)
  nlinarith only [hk, hab]

end
end BoundarySharpness
