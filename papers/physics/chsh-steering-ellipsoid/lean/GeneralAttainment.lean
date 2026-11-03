import ExplicitCriticalState
import Mathlib.Tactic.FieldSimp

/-!
A genuine complex density-operator family attaining the joint centre/marginal
CHSH envelope. This module verifies positivity, trace, all Pauli readouts,
steering centre and Gram characteristic roots. The general Horodecki theorem
identifying the CHSH supremum with the two largest Gram roots is not reproved.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false

namespace GeneralAttainment
noncomputable section

open ExplicitCriticalState (Mat Vec outer quadratic Density outer_hermitian
  outer_quadratic_nonneg pauli tensor)

def v0 (a r : ℝ) : Vec :=
  ![(((1 + r) / 2 : ℝ) : ℂ), (((r - 1) / 2 : ℝ) : ℂ), ((a / 2 : ℝ) : ℂ), ((a / 2 : ℝ) : ℂ)]
def v1 (d : ℝ) : Vec := ![((d / 2 : ℝ) : ℂ), ((d / 2 : ℝ) : ℂ), 0, 0]
def state (a d r : ℝ) : Mat := outer (v0 a r) + outer (v1 d)
def readout (a d r : ℝ) (A : Mat) : ℂ := (state a d r * A).trace

def alice (a r : ℝ) : Fin 3 → ℝ := ![r * a, 0, 1 - a ^ 2]
def bob (r : ℝ) : Fin 3 → ℝ := ![0, 0, r]
def T (a r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![r * a, 0, a; 0, -a, 0; -a ^ 2, 0, r]

theorem state_trace (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2) :
    (state a d r).trace = 1 := by
  apply Complex.ext <;>
    norm_num [state, outer, v0, v1, Matrix.trace, Matrix.diag, Matrix.add_apply,
      Fin.sum_univ_four, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.star_def, pow_two] <;> nlinarith

theorem state_is_density (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2) :
    Density (state a d r) := by
  refine ⟨?_, state_trace a d r hb, ?_⟩
  · unfold state
    rw [Matrix.conjTranspose_add, outer_hermitian, outer_hermitian]
  · intro w
    unfold state quadratic
    rw [Matrix.add_mulVec, dotProduct_add]
    have h0 := outer_quadratic_nonneg (v0 a r) w
    have h1 := outer_quadratic_nonneg (v1 d) w
    unfold quadratic at h0 h1
    simpa only [Complex.add_re] using add_nonneg h0 h1

theorem alice_readout (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2) (i : Fin 3) :
    readout a d r (tensor (pauli i) 1) = (alice a r i : ℂ) := by
  fin_cases i <;> apply Complex.ext <;>
    norm_num [readout, tensor, pauli, alice, state, outer, v0, v1,
      Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_four, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.star_def, pow_two] <;> nlinarith

theorem bob_readout (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2) (i : Fin 3) :
    readout a d r (tensor 1 (pauli i)) = (bob r i : ℂ) := by
  fin_cases i <;> apply Complex.ext <;>
    norm_num [readout, tensor, pauli, bob, state, outer, v0, v1,
      Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_four, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.star_def, pow_two] <;> nlinarith

theorem correlation_readout (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2)
    (i j : Fin 3) :
    readout a d r (tensor (pauli i) (pauli j)) = (T a r i j : ℂ) := by
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [readout, tensor, pauli, T, state, outer, v0, v1,
      Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_four, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff,
      Fin.val_natCast, Fin.coe_ofNat_eq_mod, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.star_def, pow_two] <;> nlinarith

def centre (a r : ℝ) : Fin 3 → ℝ := fun i =>
  (alice a r i - ((T a r).mulVec (bob r)) i) / (1 - dotProduct (bob r) (bob r))

theorem bob_length_square (r : ℝ) : dotProduct (bob r) (bob r) = r ^ 2 := by
  norm_num [dotProduct, bob, Fin.sum_univ_three, Matrix.vecCons, Matrix.vecHead,
    Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ]
  ring

theorem centre_value (c a r : ℝ) (hr : r ^ 2 < 1)
    (ha : a ^ 2 = (1 - c) * (1 - r ^ 2)) :
    centre a r = ![0, 0, c] := by
  have hne : 1 - r ^ 2 ≠ 0 := by linarith
  ext i
  fin_cases i <;>
    norm_num [centre, alice, T, bob, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, mul_comm]
  apply (div_eq_iff (show 1 - r * r ≠ 0 by nlinarith)).mpr
  nlinarith

/-- Concrete correlation Gram matrix of the physical family. -/
def G (a r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a ^ 2 * (1 + r ^ 2), 0, r * a * (1 - a ^ 2);
     0, a ^ 2, 0;
     r * a * (1 - a ^ 2), 0, a ^ 4 + r ^ 2]

theorem correlation_gram (a r : ℝ) : (T a r) * (T a r).transpose = G a r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [T, G, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_three, Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
      Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff] <;> ring

/-- Complete factorization: q=a², h=a²+r² and qh are the only Gram roots. -/
theorem gram_characteristic (a r t : ℝ) :
    Matrix.det (t • (1 : Matrix (Fin 3) (Fin 3) ℝ) - G a r) =
      (t - (a ^ 2 + r ^ 2)) * (t - a ^ 2) * (t - a ^ 2 * (a ^ 2 + r ^ 2)) := by
  rw [Matrix.det_fin_three]
  norm_num [G, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail,
    Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Fin.succ, Fin.ext_iff]
  ring

theorem gram_root_iff (a r t : ℝ) :
    Matrix.det (t • (1 : Matrix (Fin 3) (Fin 3) ℝ) - G a r) = 0 ↔
      t = a ^ 2 + r ^ 2 ∨ t = a ^ 2 ∨ t = a ^ 2 * (a ^ 2 + r ^ 2) := by
  rw [gram_characteristic]
  simp only [mul_eq_zero, sub_eq_zero]
  tauto

theorem ordered_roots (a d r : ℝ) (hb : a ^ 2 + d ^ 2 = 1 - r ^ 2) :
    0 ≤ a ^ 2 * (a ^ 2 + r ^ 2) ∧
    a ^ 2 * (a ^ 2 + r ^ 2) ≤ a ^ 2 ∧
    a ^ 2 ≤ a ^ 2 + r ^ 2 ∧ a ^ 2 + r ^ 2 ≤ 1 := by
  have hq : 0 ≤ a ^ 2 := sq_nonneg a
  have hr : 0 ≤ r ^ 2 := sq_nonneg r
  have hd : 0 ≤ d ^ 2 := sq_nonneg d
  have hh : a ^ 2 + r ^ 2 ≤ 1 := by linarith
  have hh0 : 0 ≤ a ^ 2 + r ^ 2 := by positivity
  have hqh : a ^ 2 * (a ^ 2 + r ^ 2) ≤ a ^ 2 := by
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hh)]
  exact ⟨mul_nonneg hq hh0, hqh, by linarith, hh⟩

/-- The two largest actual Gram roots attain the stated joint envelope exactly. -/
theorem joint_envelope_attained (c a r : ℝ)
    (ha : a ^ 2 = (1 - c) * (1 - r ^ 2)) :
    (a ^ 2 + r ^ 2) + a ^ 2 = 1 + (1 - 2 * c) * (1 - r ^ 2) := by
  nlinarith

/-- Square-root choices exist at every physical centre and every r²≤1. -/
theorem square_root_parameters (c r : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr : r ^ 2 ≤ 1) :
    let a := Real.sqrt ((1 - c) * (1 - r ^ 2))
    let d := Real.sqrt (c * (1 - r ^ 2))
    a ^ 2 = (1 - c) * (1 - r ^ 2) ∧
    d ^ 2 = c * (1 - r ^ 2) ∧ a ^ 2 + d ^ 2 = 1 - r ^ 2 := by
  have hp : 0 ≤ 1 - c := by linarith
  have hs : 0 ≤ 1 - r ^ 2 := by linarith
  have ha := Real.sq_sqrt (mul_nonneg hp hs)
  have hd := Real.sq_sqrt (mul_nonneg hc0 hs)
  dsimp only
  exact ⟨ha, hd, by nlinarith⟩

/-- One assembled physical attainment theorem for every admissible centre and marginal. -/
theorem physical_attainment (c r : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr : r ^ 2 < 1) :
    ∃ a d : ℝ,
      Density (state a d r) ∧
      (∀ i, readout a d r (tensor (pauli i) 1) = (alice a r i : ℂ)) ∧
      (∀ i, readout a d r (tensor 1 (pauli i)) = (bob r i : ℂ)) ∧
      (∀ i j, readout a d r (tensor (pauli i) (pauli j)) = (T a r i j : ℂ)) ∧
      centre a r = ![0, 0, c] ∧
      dotProduct (bob r) (bob r) = r ^ 2 ∧
      (∀ t, Matrix.det (t • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
        (T a r) * (T a r).transpose) =
        (t - (a ^ 2 + r ^ 2)) * (t - a ^ 2) * (t - a ^ 2 * (a ^ 2 + r ^ 2))) ∧
      (0 ≤ a ^ 2 * (a ^ 2 + r ^ 2) ∧
        a ^ 2 * (a ^ 2 + r ^ 2) ≤ a ^ 2 ∧
        a ^ 2 ≤ a ^ 2 + r ^ 2 ∧ a ^ 2 + r ^ 2 ≤ 1) ∧
      (a ^ 2 + r ^ 2) + a ^ 2 = 1 + (1 - 2 * c) * (1 - r ^ 2) := by
  let a := Real.sqrt ((1 - c) * (1 - r ^ 2))
  let d := Real.sqrt (c * (1 - r ^ 2))
  obtain ⟨ha, _, hb⟩ := square_root_parameters c r hc0 hc1 (le_of_lt hr)
  refine ⟨a, d, state_is_density a d r hb,
    alice_readout a d r hb, bob_readout a d r hb, correlation_readout a d r hb,
    centre_value c a r hr ha, bob_length_square r, ?_, ordered_roots a d r hb,
    joint_envelope_attained c a r ha⟩
  intro t
  rw [correlation_gram]
  exact gram_characteristic a r t

end
end GeneralAttainment
