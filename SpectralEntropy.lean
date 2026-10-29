module
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Group.Semiconj.Units


@[expose] public section

/-! # Entropy of flat-spectrum Hermitian matrices

The entropy below is defined using the actual eigenvalues supplied by Mathlib's
spectral theorem. The identity `M * M = c • M` forces each eigenvalue to be either
zero or `c`; trace one then yields entropy `-log c`.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace CMICounterexample

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def vonNeumannEntropy (M : Matrix n n ℂ) (hM : M.IsHermitian) : ℝ :=
  -∑ i, hM.eigenvalues i * Real.log (hM.eigenvalues i)

/-- On Hermitian matrices, the trace norm is the sum of the absolute eigenvalues. -/
noncomputable def traceNorm (M : Matrix n n ℂ) (hM : M.IsHermitian) : ℝ :=
  ∑ i, |hM.eigenvalues i|

theorem trace_eq_sum_hermitian_eigenvalues (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    M.trace = ∑ i, (hM.eigenvalues i : ℂ) := by
  calc
    M.trace = (hM.eigenvectorUnitary.1 *
        diagonal (Complex.ofReal ∘ hM.eigenvalues) *
        star hM.eigenvectorUnitary.1).trace := congrArg Matrix.trace hM.spectral_theorem
    _ = (star hM.eigenvectorUnitary.1 * hM.eigenvectorUnitary.1 *
        diagonal (Complex.ofReal ∘ hM.eigenvalues)).trace := Matrix.trace_mul_cycle _ _ _
    _ = ∑ i, (hM.eigenvalues i : ℂ) := by
      rw [Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
      rfl

theorem sum_hermitian_eigenvalues_of_trace_one (M : Matrix n n ℂ)
    (hM : M.IsHermitian) (htrace : M.trace = 1) :
    ∑ i, hM.eigenvalues i = 1 := by
  have h := congrArg Complex.re (trace_eq_sum_hermitian_eigenvalues M hM)
  simpa [htrace] using h.symm

theorem trace_pow_eq_sum_hermitian_eigenvalues (M : Matrix n n ℂ)
    (hM : M.IsHermitian) (k : ℕ) :
    (M ^ k).trace = ∑ i, (hM.eigenvalues i : ℂ) ^ k := by
  let U : (Matrix n n ℂ)ˣ := Unitary.toUnits hM.eigenvectorUnitary
  let D : Matrix n n ℂ := diagonal (Complex.ofReal ∘ hM.eigenvalues)
  have hs : M = (U : Matrix n n ℂ) * D * (↑U⁻¹ : Matrix n n ℂ) := hM.spectral_theorem
  calc
    (M ^ k).trace = (((U : Matrix n n ℂ) * D * (↑U⁻¹ : Matrix n n ℂ)) ^ k).trace :=
      congrArg (fun K : Matrix n n ℂ => (K ^ k).trace) hs
    _ = (D ^ k).trace := by rw [Units.conj_pow, Matrix.trace_units_conj]
    _ = ∑ i, (hM.eigenvalues i : ℂ) ^ k := by
      dsimp [D]
      rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
      rfl

theorem sum_sq_hermitian_eigenvalues (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    ∑ i, (hM.eigenvalues i) ^ 2 = (M * M).trace.re := by
  have h := congrArg Complex.re (trace_pow_eq_sum_hermitian_eigenvalues M hM 2)
  simpa [Complex.mul_re, pow_two] using h.symm

theorem traceNorm_nonneg (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    0 ≤ traceNorm M hM := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem traceNorm_sq_le_card_mul_trace_square (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    (traceNorm M hM) ^ 2 ≤ Fintype.card n * (M * M).trace.re := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n)
    (fun i => |hM.eigenvalues i|) (fun _ => (1 : ℝ))
  simpa [traceNorm, sq_abs, sum_sq_hermitian_eigenvalues, mul_comm] using h

theorem eigenvalue_zero_or_flat (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (c : ℝ) (hflat : M * M = c • M) (i : n) :
    hM.eigenvalues i = 0 ∨ hM.eigenvalues i = c := by
  let v : n → ℂ := hM.eigenvectorBasis i
  have hv : v ≠ 0 := by
    intro h
    apply hM.eigenvectorBasis.orthonormal.ne_zero i
    ext j
    exact congrFun h j
  have hev : M *ᵥ v = (hM.eigenvalues i) • v := hM.mulVec_eigenvectorBasis i
  have heq : (hM.eigenvalues i * hM.eigenvalues i) • v =
      (c * hM.eigenvalues i) • v := by
    have h := congrArg (fun K : Matrix n n ℂ => K *ᵥ v) hflat
    simpa only [← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.smul_mulVec,
      hev, smul_smul] using h
  have hp : hM.eigenvalues i * (hM.eigenvalues i - c) = 0 := by
    have h := smul_left_injective ℝ hv heq
    nlinarith
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem flat_posSemidef (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (c : ℝ) (hc : 0 ≤ c) (hflat : M * M = c • M) : M.PosSemidef := by
  apply (Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg hM).mpr
  intro i
  rcases eigenvalue_zero_or_flat M hM c hflat i with h | h
  · simp [h]
  · rwa [h]

theorem vonNeumannEntropy_of_flat (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (c : ℝ) (hflat : M * M = c • M) (htrace : M.trace = 1) :
    vonNeumannEntropy M hM = -Real.log c := by
  have hsum := sum_hermitian_eigenvalues_of_trace_one M hM htrace
  have hent : (∑ i, hM.eigenvalues i * Real.log (hM.eigenvalues i)) =
      (∑ i, hM.eigenvalues i) * Real.log c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rcases eigenvalue_zero_or_flat M hM c hflat i with h | h <;> simp [h]
  unfold vonNeumannEntropy
  rw [hent, hsum, one_mul]

theorem eigenvalue_sq_of_square_scalar (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (c : ℝ) (hsq : M * M = c • (1 : Matrix n n ℂ)) (i : n) :
    (hM.eigenvalues i) ^ 2 = c := by
  let v : n → ℂ := hM.eigenvectorBasis i
  have hv : v ≠ 0 := by
    intro h
    apply hM.eigenvectorBasis.orthonormal.ne_zero i
    ext j
    exact congrFun h j
  have hev : M *ᵥ v = (hM.eigenvalues i) • v := hM.mulVec_eigenvectorBasis i
  have heq : (hM.eigenvalues i * hM.eigenvalues i) • v = c • v := by
    have h := congrArg (fun K : Matrix n n ℂ => K *ᵥ v) hsq
    simpa only [← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.smul_mulVec,
      Matrix.one_mulVec, hev, smul_smul] using h
  simpa only [pow_two] using smul_left_injective ℝ hv heq

theorem traceNorm_of_square_scalar (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (q : ℝ) (hq : 0 ≤ q) (hsq : M * M = (q ^ 2) • (1 : Matrix n n ℂ)) :
    traceNorm M hM = Fintype.card n * q := by
  have hev : ∀ i, |hM.eigenvalues i| = q := by
    intro i
    apply (sq_eq_sq₀ (abs_nonneg _) hq).mp
    simpa only [sq_abs] using eigenvalue_sq_of_square_scalar M hM (q ^ 2) hsq i
  simp [traceNorm, hev]

theorem eigenvalue_cube_of_cube_scalar (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (c : ℝ) (hcube : M * M * M = c • M) (i : n) :
    (hM.eigenvalues i) ^ 3 = c * hM.eigenvalues i := by
  let v : n → ℂ := hM.eigenvectorBasis i
  have hv : v ≠ 0 := by
    intro h
    apply hM.eigenvectorBasis.orthonormal.ne_zero i
    ext j
    exact congrFun h j
  have hev : M *ᵥ v = (hM.eigenvalues i) • v := hM.mulVec_eigenvectorBasis i
  have heq : (hM.eigenvalues i * (hM.eigenvalues i * hM.eigenvalues i)) • v =
      (c * hM.eigenvalues i) • v := by
    have h := congrArg (fun K : Matrix n n ℂ => K *ᵥ v) hcube
    simpa only [← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.smul_mulVec,
      hev, smul_smul] using h
  have h := smul_left_injective ℝ hv heq
  nlinarith

theorem traceNorm_mul_of_cube_scalar (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (c : ℝ) (hc : 0 ≤ c) (hcube : M * M * M = (c ^ 2) • M) :
    c * traceNorm M hM = (M * M).trace.re := by
  have heq : ∀ i, c * |hM.eigenvalues i| = (hM.eigenvalues i) ^ 2 := by
    intro i
    have hh := eigenvalue_cube_of_cube_scalar M hM (c ^ 2) hcube i
    have hp : hM.eigenvalues i * ((hM.eigenvalues i) ^ 2 - c ^ 2) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hp with hz | hs
    · simp [hz]
    · have hs' : (hM.eigenvalues i) ^ 2 = c ^ 2 := sub_eq_zero.mp hs
      have ha : |hM.eigenvalues i| = c := by
        apply (sq_eq_sq₀ (abs_nonneg _) hc).mp
        simpa only [sq_abs] using hs'
      rw [ha, hs', pow_two]
  unfold traceNorm
  rw [Finset.mul_sum]
  simp only [heq]
  exact sum_sq_hermitian_eigenvalues M hM

theorem traceNorm_of_cube_scalar (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (c : ℝ) (hc : 0 < c) (hcube : M * M * M = (c ^ 2) • M) :
    traceNorm M hM = (M * M).trace.re / c := by
  apply (eq_div_iff hc.ne').mpr
  simpa only [mul_comm] using traceNorm_mul_of_cube_scalar M hM c hc.le hcube

end CMICounterexample
