import CHSHQuantum
import Mathlib.Tactic.FieldSimp

/-!
A fully physical tilted-filter witness for an oblate steering ellipsoid.
The module proves complex PSD/trace, all Pauli readouts, centre and the standard
ellipsoid-matrix formula, the all-settings CHSH upper bound, actual attaining
unit Bell settings, and the exact CHSH supremum. No Horodecki theorem is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false

namespace CertifiedCHSH
noncomputable section

/-- Every real Pauli direction is a Hermitian quantum observable. -/
theorem spin_hermitian (x : V) : (spin x).conjTranspose = spin x := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [spin, CHSHPhysical.pauli, Matrix.conjTranspose_apply,
      Matrix.sum_apply, Matrix.smul_apply, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, Complex.mul_re, Complex.mul_im,
      Complex.star_def]

/-- Unit Pauli directions have the required dichotomic observable square. -/
theorem spin_square_unit (x : V) (hx : Unit x) : spin x * spin x = 1 := by
  have hs : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by
    simpa only [Unit, nsq, dot, dotProduct, Fin.sum_univ_three, pow_two] using hx
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [spin, CHSHPhysical.pauli, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply,
      Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, Complex.mul_re, Complex.mul_im] <;>
    nlinarith

end
end CertifiedCHSH

namespace CHSHAxialWitness
noncomputable section

open CertifiedCHSH
open CHSHPhysical (Mat Vec outer quadratic Density tensor pauli outer_quadratic_nonneg)

def k : ℝ := Real.sqrt 5
def f : ℝ := Real.sqrt 10
def g : ℝ := Real.sqrt 430

theorem k_square : k ^ 2 = 5 := Real.sq_sqrt (by norm_num)
theorem f_square : f ^ 2 = 10 := Real.sq_sqrt (by norm_num)
theorem g_square : g ^ 2 = 430 := Real.sq_sqrt (by norm_num)
theorem f_positive : 0 < f := Real.sqrt_pos.mpr (by norm_num)
theorem g_positive : 0 < g := Real.sqrt_pos.mpr (by norm_num)

def rho : Mat := (1 / 160 : ℂ) •
  !![81, -9 * (k : ℂ), 45, 15 * (k : ℂ);
     -9 * (k : ℂ), 21, -9 * (k : ℂ), -15;
     45, -9 * (k : ℂ), 39, 9 * (k : ℂ);
     15 * (k : ℂ), -15, 9 * (k : ℂ), 19]

def w0 : Vec := ![1, -(k : ℂ) / 9, 5 / 9, 5 * (k : ℂ) / 27]
def w1 : Vec := ![0, 1, -(k : ℂ) / 4, -5 / 12]
def w2 : Vec := ![0, 0, 1, -(k : ℂ) / 9]
def w3 : Vec := ![0, 0, 0, 1]

/-- Exact LDL decomposition expressed as positive weighted outer products. -/
theorem rho_decomposition :
    rho = ((81 / 160 : ℝ) : ℂ) • outer w0 + ((1 / 10 : ℝ) : ℂ) • outer w1 +
      ((9 / 160 : ℝ) : ℂ) • outer w2 + ((1 / 90 : ℝ) : ℂ) • outer w3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [rho, outer, w0, w1, w2, w3, Matrix.smul_apply, Matrix.add_apply,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.star_def] <;> nlinarith [k_square]

theorem weighted_outer_nonneg (v w : Vec) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (quadratic ((t : ℂ) • outer v) w).re := by
  have h := outer_quadratic_nonneg v w
  unfold quadratic at h ⊢
  rw [Matrix.smul_mulVec_assoc, dotProduct_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_nonneg ht h

theorem rho_trace : rho.trace = 1 := by
  norm_num [rho, Matrix.trace, Matrix.diag, Fin.sum_univ_four, Matrix.smul_apply,
    Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
    Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
    Fin.val_natCast, Fin.coe_ofNat_eq_mod]

theorem rho_hermitian : rho.conjTranspose = rho := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [rho, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.star_def]

theorem rho_is_density : Density rho := by
  refine ⟨rho_hermitian, rho_trace, ?_⟩
  intro w
  have h0 := weighted_outer_nonneg w0 w (81 / 160) (by norm_num)
  have h1 := weighted_outer_nonneg w1 w (1 / 10) (by norm_num)
  have h2 := weighted_outer_nonneg w2 w (9 / 160) (by norm_num)
  have h3 := weighted_outer_nonneg w3 w (1 / 90) (by norm_num)
  rw [rho_decomposition]
  unfold quadratic at h0 h1 h2 h3 ⊢
  simp only [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  linarith

def alice : V := ![3 / 8, 0, 11 / 40]
def bob : V := ![0, 0, 1 / 2]
def T : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3 * k / 40, 0, 3 / 4;
     0, -3 * k / 10, 0;
     -9 * k / 40, 0, 1 / 4]

theorem alice_readout (i : Fin 3) : expect rho (tensor (pauli i) 1) = (alice i : ℂ) := by
  fin_cases i <;> apply Complex.ext <;>
    norm_num [expect, tensor, pauli, alice, rho, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.one_apply,
      Matrix.smul_apply, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem bob_readout (i : Fin 3) : expect rho (tensor 1 (pauli i)) = (bob i : ℂ) := by
  fin_cases i <;> apply Complex.ext <;>
    norm_num [expect, tensor, pauli, bob, rho, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.one_apply,
      Matrix.smul_apply, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem correlation_readout (i j : Fin 3) :
    expect rho (tensor (pauli i) (pauli j)) = (T i j : ℂ) := by
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [expect, tensor, pauli, T, rho, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.one_apply,
      Matrix.smul_apply, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

def centre : V := fun i => (alice i - (T.mulVec bob) i) / (1 - dotProduct bob bob)
def dyad (x y : V) : Matrix (Fin 3) (Fin 3) ℝ := fun i j => x i * y j
def K : Matrix (Fin 3) (Fin 3) ℝ := T - dyad alice bob
/-- Standard nonsingular steering-ellipsoid matrix in terms of actual Bloch readouts. -/
def shape : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / (1 - dotProduct bob bob)) •
    (K * (1 + (1 / (1 - dotProduct bob bob)) • dyad bob bob) * K.transpose)

theorem bob_length_square : dotProduct bob bob = 1 / 4 := by
  norm_num [dotProduct, bob, Fin.sum_univ_three, Matrix.vecCons, Matrix.vecHead,
    Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]

theorem centre_value : centre = ![0, 0, (1 / 5 : ℝ)] := by
  ext i
  fin_cases i <;>
    norm_num [centre, alice, T, bob, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff]

theorem shape_value : shape = !![(3 / 5 : ℝ), 0, 0; 0, 3 / 5, 0; 0, 0, 9 / 25] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shape, K, dyad, alice, bob, T, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.one_apply,
      dotProduct, Fin.sum_univ_three, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead,
      Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ,
      Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod] <;> nlinarith [k_square]

/-- Exact diagonal Bob Gram form of the actual density matrix. -/
theorem image_norm (x : V) :
    nsq (T.mulVec x) = (9 / 32) * x 0 ^ 2 + (9 / 20) * x 1 ^ 2 + (5 / 8) * x 2 ^ 2 := by
  have hi : nsq (T.mulVec x) =
      (9 / 160) * k ^ 2 * x 0 ^ 2 + (9 / 100) * k ^ 2 * x 1 ^ 2 + (5 / 8) * x 2 ^ 2 := by
    norm_num [nsq, dot, dotProduct, Matrix.mulVec, T, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff]
    ring
  rw [hi, k_square]
  ring

theorem plane_bound : PlaneBound T.mulVec (43 / 40) := by
  have he : (9 / 20 : ℝ) + 5 / 8 = 43 / 40 := by norm_num
  rw [← he]
  exact plane_of_diagonal_norm T.mulVec (9 / 32) (9 / 20) (5 / 8)
    (by norm_num) (by norm_num) image_norm

def u : V := ![3 / f, 0, 1 / f]
def u' : V := ![0, -1, 0]
def v : V := ![0, 6 * k / g, 5 * f / g]
def v' : V := ![0, -6 * k / g, 5 * f / g]

theorem settings_unit : Unit u ∧ Unit u' ∧ Unit v ∧ Unit v' := by
  have hfn := ne_of_gt f_positive
  have hgn := ne_of_gt g_positive
  constructor
  · norm_num [CertifiedCHSH.Unit, nsq, dot, dotProduct, u, Fin.sum_univ_three,
      Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
    field_simp [hfn]
    nlinarith [f_square]
  · constructor
    · norm_num [CertifiedCHSH.Unit, nsq, dot, dotProduct, u', Fin.sum_univ_three,
        Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
    · constructor <;>
        norm_num [CertifiedCHSH.Unit, nsq, dot, dotProduct, v, v', Fin.sum_univ_three,
          Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
        field_simp [hgn] <;> nlinarith [k_square, f_square, g_square]

theorem setting_scalar_value : dot u (T.mulVec (v + v')) + dot u' (T.mulVec (v - v')) = g / 10 := by
  have hfn := ne_of_gt f_positive
  have hgn := ne_of_gt g_positive
  have hi : dot u (T.mulVec (v + v')) + dot u' (T.mulVec (v - v')) =
      (25 + (18 / 5) * k ^ 2) / g := by
    norm_num [dot, dotProduct, Matrix.mulVec, T, u, u', v, v', Fin.sum_univ_three,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff]
    field_simp [hfn, hgn]
    ring
  rw [hi, k_square]
  norm_num
  field_simp [hgn]
  nlinarith [g_square]

theorem setting_quantum_value : modulus (expect rho (bell u u' v v')) = g / 10 := by
  rw [bell_norm_correlation rho T correlation_readout, setting_scalar_value]
  exact abs_of_nonneg (div_nonneg (le_of_lt g_positive) (by norm_num))

theorem value_eq_two_sqrt : g / 10 = 2 * Real.sqrt (43 / 40) := by
  have hs : Real.sqrt (43 / 40 : ℝ) ^ 2 = 43 / 40 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (43 / 40 : ℝ)
  have hg := g_positive
  nlinarith [g_square]

theorem all_settings_upper (a a' b b' : V) (ha : Unit a) (ha' : Unit a')
    (hb : Unit b) (hb' : Unit b') :
    modulus (expect rho (bell a a' b b')) ≤ g / 10 := by
  rw [value_eq_two_sqrt]
  exact bell_norm_le_of_plane rho T correlation_readout (43 / 40)
    (by norm_num) plane_bound a a' b b' ha ha' hb hb'

/-- Exact CHSH supremum over all physical unit-direction Bell settings. -/
theorem beta_exact : beta rho = g / 10 := by
  unfold beta
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨h1, h2, h3, h4⟩ := settings_unit
    exact ⟨u, u', v, v', h1, h2, h3, h4, setting_quantum_value.symm⟩
  · intro z hz
    obtain ⟨a, a', b, b', ha, ha', hb, hb', rfl⟩ := hz
    exact all_settings_upper a a' b b' ha ha' hb hb'

theorem strict_chsh_violation : 2 < beta rho := by
  rw [beta_exact]
  have hp := g_positive
  nlinarith [g_square]

/-- One end-to-end physical witness, with all computational definitions explicit. -/
theorem certified_axial_witness :
    Density rho ∧ centre = ![0, 0, (1 / 5 : ℝ)] ∧
      shape = !![(3 / 5 : ℝ), 0, 0; 0, 3 / 5, 0; 0, 0, 9 / 25] ∧
      beta rho = Real.sqrt 430 / 10 ∧ 2 < beta rho := by
  exact ⟨rho_is_density, centre_value, shape_value, beta_exact, strict_chsh_violation⟩

end
end CHSHAxialWitness
