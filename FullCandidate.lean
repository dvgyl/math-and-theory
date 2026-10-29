module

public import QICFoundation
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Order.Star.Pi
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Three-state root-fidelity entropy proof

QICFoundation supplies the attributed prior work.
No new axiom or bypass of kernel checking is introduced.
-/


/- BEGIN ORIGINAL SOURCE: BlockAlgebra.lean -/
section

/-!
# Block-diagonal changes of basis

The index convention is `n × s`, where `n` is the internal coordinate and
`s` labels blocks. These identities are purely algebraic and are preparatory
lemmas for the Li--Zhang decomposition.
-/

open scoped Matrix

namespace Fidelity

variable {n s : Type*} [Fintype n] [Fintype s] [DecidableEq n] [DecidableEq s]

def matrixBlock (A : Matrix (n × s) (n × s) ℂ) (i j : s) : Matrix n n ℂ :=
  A.submatrix (fun r => (r, i)) (fun r => (r, j))

def scalarSlice (A : Matrix (n × s) (n × s) ℂ) (r : n) : Matrix s s ℂ :=
  A.submatrix (fun i => (r, i)) (fun i => (r, i))

theorem blockDiagonal_mem_unitary (U : s → Matrix.unitaryGroup n ℂ) :
    Matrix.blockDiagonal (fun i => (U i : Matrix n n ℂ)) ∈
      Matrix.unitaryGroup (n × s) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  have h : (fun i => (U i : Matrix n n ℂ)ᴴ * (U i : Matrix n n ℂ)) =
      (fun _ : s => (1 : Matrix n n ℂ)) := by
    funext i
    simpa only [Matrix.star_eq_conjTranspose] using (U i).property.1
  rw [h]
  exact Matrix.blockDiagonal_one

omit [DecidableEq n] in
theorem matrixBlock_mul_blockDiagonal [DecidableEq n] (A : Matrix (n × s) (n × s) ℂ)
    (U : s → Matrix n n ℂ) (i j : s) :
    matrixBlock (A * Matrix.blockDiagonal U) i j = matrixBlock A i j * U j := by
  ext r t
  simp [matrixBlock, Matrix.mul_apply, Matrix.blockDiagonal_apply,
    ← Finset.univ_product_univ, Finset.sum_product]

omit [DecidableEq n] in
theorem matrixBlock_blockDiagonal_mul [DecidableEq n] (A : Matrix (n × s) (n × s) ℂ)
    (U : s → Matrix n n ℂ) (i j : s) :
    matrixBlock (Matrix.blockDiagonal U * A) i j = U i * matrixBlock A i j := by
  ext r t
  simp [matrixBlock, Matrix.mul_apply, Matrix.blockDiagonal_apply,
    ← Finset.univ_product_univ, Finset.sum_product]

theorem matrixBlock_blockDiagonal_conjugate (A : Matrix (n × s) (n × s) ℂ)
    (U : s → Matrix n n ℂ) (i j : s) :
    matrixBlock (Matrix.blockDiagonal U * A * (Matrix.blockDiagonal U)ᴴ) i j =
      U i * matrixBlock A i j * (U j)ᴴ := by
  rw [Matrix.blockDiagonal_conjTranspose, matrixBlock_mul_blockDiagonal,
    matrixBlock_blockDiagonal_mul]

theorem scalarSlice_blockDiagonal_conjugate (A : Matrix (n × s) (n × s) ℂ)
    (U : s → Matrix n n ℂ) (r : n) (i j : s) :
    scalarSlice (Matrix.blockDiagonal U * A * (Matrix.blockDiagonal U)ᴴ) r i j =
      (U i * matrixBlock A i j * (U j)ᴴ) r r := by
  exact congrArg (fun M : Matrix n n ℂ => M r r)
    (matrixBlock_blockDiagonal_conjugate A U i j)

end Fidelity
end
/- END ORIGINAL SOURCE: BlockAlgebra.lean -/


/- BEGIN ORIGINAL SOURCE: StructuralSpectral.lean -/
section

/-!
# Spectral and nuclear-norm helpers

These use the proved same-space Gram-matrix isometry and unitary invariance
from QICLean. The polar factor is obtained from the positive square root,
as in QICLean's `PolarUnitaryCorrection` proof. The nuclear norm is the
conventional real trace of `sqrt(Aᴴ A)`.
No matrix inequality is assumed as a new axiom.
-/

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

namespace Fidelity

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def nuclear (A : Matrix n n ℂ) : ℝ := (CFC.abs A).trace.re

theorem nuclear_eq_traceNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    nuclear A = Matrix.traceNorm A :=
  (Matrix.traceNorm_eq_re_trace_abs A).symm

theorem exists_unitary_polar (A : Matrix n n ℂ) :
    ∃ (U : Matrix.unitaryGroup n ℂ) (P : Matrix n n ℂ),
      P.PosSemidef ∧ A = (U : Matrix n n ℂ) * P := by
  let P := CFC.sqrt (Aᴴ * A)
  have hP : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hsq : P * P = Aᴴ * A :=
    CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  obtain ⟨U, hU⟩ := Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq A P
    (by rw [hP.isHermitian.eq, hsq])
  exact ⟨U, P, hP, hU⟩

theorem exists_right_unitary_polar (A : Matrix n n ℂ) :
    ∃ (P : Matrix n n ℂ) (U : Matrix.unitaryGroup n ℂ),
      P.PosSemidef ∧ A = P * (U : Matrix n n ℂ) := by
  obtain ⟨U, P, hP, hU⟩ := exists_unitary_polar Aᴴ
  refine ⟨P, U⁻¹, hP, ?_⟩
  have h := congrArg Matrix.conjTranspose hU
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    hP.isHermitian.eq, Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose] using h

theorem nuclear_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    nuclear A = A.trace.re := by
  unfold nuclear
  rw [CFC.abs_of_nonneg A hA.nonneg]

theorem nuclear_posSemidef_complex {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (nuclear A : ℂ) = A.trace := by
  rw [nuclear_posSemidef hA]
  simp only [Matrix.trace, Complex.re_sum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun i _ => hA.isHermitian.coe_re_apply_self i)

theorem nuclear_unitary_mul (U : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    nuclear ((U : Matrix n n ℂ) * A) = nuclear A := by
  unfold nuclear
  rw [Matrix.abs_unitary_mul U.property]

theorem nuclear_mul_unitary (U : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    nuclear (A * (U : Matrix n n ℂ)) = nuclear A := by
  have hU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.property.2
  unfold nuclear
  rw [Matrix.abs_mul_unitary U.property, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

theorem nuclear_unitary_mul_unitary (U V : Matrix.unitaryGroup n ℂ)
    (A : Matrix n n ℂ) :
    nuclear ((U : Matrix n n ℂ) * A * (V : Matrix n n ℂ)) = nuclear A := by
  rw [nuclear_mul_unitary, nuclear_unitary_mul]

theorem nuclear_smul_nonneg (A : Matrix n n ℂ) (t : ℝ) (ht : 0 ≤ t) :
    nuclear (t • A) = t * nuclear A := by
  simp only [nuclear, CFC.abs_smul, Matrix.trace_smul, Complex.smul_re,
    Real.norm_eq_abs, abs_of_nonneg ht, smul_eq_mul]

theorem nuclear_add_smul_one {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) :
    nuclear (A + t • (1 : Matrix n n ℂ)) = nuclear A + (Fintype.card n : ℝ) * t := by
  have hpos : (A + t • (1 : Matrix n n ℂ)).PosSemidef :=
    hA.add (Matrix.PosSemidef.one.smul ht)
  rw [nuclear_posSemidef hpos, nuclear_posSemidef hA, Matrix.trace_add, Matrix.trace_smul]
  simp [Matrix.trace_one, mul_comm]

end Fidelity
end
/- END ORIGINAL SOURCE: StructuralSpectral.lean -/


/- BEGIN ORIGINAL SOURCE: UnitaryDiagonal.lean -/
section

open scoped Matrix ComplexOrder
open Matrix

namespace Fidelity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A unitary is diagonal in an orthonormal basis, with unit-modulus diagonal.
The proof uses simultaneous diagonalization of its commuting Hermitian parts. -/
theorem unitary_diagonalization (W : Matrix.unitaryGroup n ℂ) :
    ∃ (V : Matrix.unitaryGroup n ℂ) (phase : n → ℂ),
      (V : Matrix n n ℂ)ᴴ * (W : Matrix n n ℂ) * (V : Matrix n n ℂ) = diagonal phase ∧
        ∀ i, ‖phase i‖ = 1 := by
  classical
  let A : Matrix n n ℂ := W
  let H : Matrix n n ℂ := (1 / 2 : ℂ) • (A + Aᴴ)
  let K : Matrix n n ℂ := (Complex.I / 2 : ℂ) • (Aᴴ - A)
  have hH : H.IsHermitian := by
    change Hᴴ = H
    dsimp [H]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, star_div₀, star_one, star_ofNat, add_comm]
  have hK : K.IsHermitian := by
    change Kᴴ = K
    dsimp [K]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, star_div₀, star_ofNat,
      Complex.star_def, Complex.conj_I]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hAA : Commute A Aᴴ := by
    have h₁ : A * Aᴴ = 1 := by
      simpa only [A, Matrix.star_eq_conjTranspose] using W.property.2
    have h₂ : Aᴴ * A = 1 := by
      simpa only [A, Matrix.star_eq_conjTranspose] using W.property.1
    exact h₁.trans h₂.symm
  have hHK : H * K = K * H := by
    have hs : Commute (A + Aᴴ) (Aᴴ - A) :=
      (hAA.add_left (Commute.refl Aᴴ)).sub_right ((Commute.refl A).add_left hAA.symm)
    exact ((hs.smul_left (1 / 2 : ℂ)).smul_right (Complex.I / 2 : ℂ)).eq
  obtain ⟨V, a, b, hVV, hVV', hHa, hKb⟩ := Matrix.exists_unitary_diagonal_of_commute hH hK hHK
  have hV : V ∈ Matrix.unitaryGroup n ℂ := by
    exact Matrix.mem_unitaryGroup_iff'.mpr hVV
  let VU : Matrix.unitaryGroup n ℂ := ⟨V, hV⟩
  let phase : n → ℂ := fun i => (a i : ℂ) + Complex.I * (b i : ℂ)
  have hparts : A = H + Complex.I • K := by
    have hi : (Complex.I : ℂ) * (Complex.I / 2) = -(1 / 2 : ℂ) := by
      rw [← mul_div_assoc, Complex.I_mul_I]
      ring
    dsimp [H, K]
    rw [smul_smul, hi]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hcancel (D : Matrix n n ℂ) : Vᴴ * (V * D * Vᴴ) * V = D := by
    calc
      Vᴴ * (V * D * Vᴴ) * V = (Vᴴ * V) * D * (Vᴴ * V) := by
        simp only [Matrix.mul_assoc]
      _ = D := by rw [hVV, Matrix.one_mul, Matrix.mul_one]
  have hd : Vᴴ * A * V = diagonal phase := by
    calc
      Vᴴ * A * V = Vᴴ * (H + Complex.I • K) * V := by rw [hparts]
      _ = Vᴴ * H * V + Complex.I • (Vᴴ * K * V) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = diagonal (fun i => (a i : ℂ)) +
          Complex.I • diagonal (fun i => (b i : ℂ)) := by rw [hHa, hKb, hcancel, hcancel]
      _ = diagonal phase := by
        ext i j
        by_cases hij : i = j <;> simp [hij, phase]
  have hdu : diagonal phase ∈ Matrix.unitaryGroup n ℂ := by
    have h : ((VU⁻¹ * W * VU : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) = diagonal phase := by
      simpa only [Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.inv_val,
        Matrix.star_eq_conjTranspose, VU, A] using hd
    rw [← h]
    exact (VU⁻¹ * W * VU).property
  refine ⟨VU, phase, hd, ?_⟩
  intro i
  have hscalar := congrArg (fun M : Matrix n n ℂ => M i i) hdu.1
  have hnorm := congrArg norm hscalar
  simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diagonal_apply, Matrix.one_apply_eq, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hnorm
  simp only [norm_mul, norm_star, norm_one] at hnorm
  nlinarith [norm_nonneg (phase i)]

end Fidelity
end
/- END ORIGINAL SOURCE: UnitaryDiagonal.lean -/


/- BEGIN ORIGINAL SOURCE: DiagonalAttainment.lean -/
section

/-!
# Simultaneous attainment of three block nuclear norms

This is the algebraic construction underlying Li--Zhang (2014), Theorem 1.
It is not a new spectral or norm theorem.
-/

open scoped Matrix ComplexOrder
open Matrix

namespace Fidelity

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def diagonalNorm (A : Matrix n n ℂ) : ℝ := ∑ r, ‖A r r‖

def gauge (L R : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (L : Matrix n n ℂ) * A * (R : Matrix n n ℂ)ᴴ

theorem gauge_comp (L₁ L₂ R₁ R₂ : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    gauge (L₁ * L₂) (R₁ * R₂) A = gauge L₁ R₁ (gauge L₂ R₂ A) := by
  simp only [gauge, Matrix.UnitaryGroup.mul_val, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem gauge_same_mul (U : Matrix.unitaryGroup n ℂ) (A B : Matrix n n ℂ) :
    gauge U U (A * B) = gauge U U A * gauge U U B := by
  have hU : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.property.1
  symm
  calc
    gauge U U A * gauge U U B =
        (U : Matrix n n ℂ) * A * ((U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ)) * B *
          (U : Matrix n n ℂ)ᴴ := by simp only [gauge, Matrix.mul_assoc]
    _ = gauge U U (A * B) := by rw [hU]; simp only [gauge, Matrix.mul_one, Matrix.mul_assoc]

theorem nuclear_gauge (L R : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    nuclear (gauge L R A) = nuclear A := by
  simpa only [gauge, Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose] using
    nuclear_unitary_mul_unitary L R⁻¹ A

theorem gauge_posSemidef (U : Matrix.unitaryGroup n ℂ) {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : (gauge U U A).PosSemidef :=
  hA.mul_mul_conjTranspose_same (U : Matrix n n ℂ)

theorem diagonalNorm_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    diagonalNorm A = nuclear A := by
  rw [nuclear_posSemidef hA]
  unfold diagonalNorm
  simp only [Matrix.trace, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (0 : ℂ) ≤ A i i := hA.diag_nonneg
  calc
    ‖A i i‖ = ‖((A i i).re : ℂ)‖ :=
      congrArg (fun z : ℂ => ‖z‖) (hA.isHermitian.coe_re_apply_self i).symm
    _ = (A i i).re := Complex.norm_of_nonneg (RCLike.nonneg_iff.mp hi).1

theorem diagonalNorm_mul_diagonal {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (phase : n → ℂ) (hphase : ∀ r, ‖phase r‖ = 1) :
    diagonalNorm (A * diagonal phase) = nuclear A := by
  rw [← diagonalNorm_posSemidef hA]
  unfold diagonalNorm
  simp only [Matrix.mul_diagonal, norm_mul, hphase, mul_one]

omit [DecidableEq n] in
theorem diagonalNorm_conjTranspose [DecidableEq n] (A : Matrix n n ℂ) :
    diagonalNorm Aᴴ = diagonalNorm A := by
  simp only [diagonalNorm, Matrix.conjTranspose_apply, norm_star]

theorem nuclear_conjTranspose (A : Matrix n n ℂ) : nuclear Aᴴ = nuclear A := by
  obtain ⟨U, P, hP, hA⟩ := exists_unitary_polar A
  rw [hA, Matrix.conjTranspose_mul, hP.isHermitian.eq, nuclear_unitary_mul]
  simpa only [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose] using
    nuclear_mul_unitary U⁻¹ P

/-- The three edge matrices of a triangle admit vertex unitaries for which
the sum of the absolute diagonal entries attains every nuclear norm. -/
theorem exists_triangle_diagonal_attainment (A B C : Matrix n n ℂ) :
    ∃ U₀ U₁ U₂ : Matrix.unitaryGroup n ℂ,
      diagonalNorm (gauge U₀ U₁ A) = nuclear A ∧
      diagonalNorm (gauge U₀ U₂ B) = nuclear B ∧
      diagonalNorm (gauge U₁ U₂ C) = nuclear C := by
  obtain ⟨UA, PA, hPA, hA⟩ := exists_unitary_polar A
  obtain ⟨PC, UC, hPC, hC⟩ := exists_right_unitary_polar C
  have hga : gauge UA⁻¹ 1 A = PA := by
    have hUA : (UA : Matrix n n ℂ)ᴴ * (UA : Matrix n n ℂ) = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using UA.property.1
    simp only [gauge, Matrix.UnitaryGroup.inv_val, Matrix.UnitaryGroup.one_val,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_one, Matrix.mul_one, hA]
    rw [← Matrix.mul_assoc, hUA, Matrix.one_mul]
  have hgc : gauge 1 UC C = PC := by
    have hUC : (UC : Matrix n n ℂ) * (UC : Matrix n n ℂ)ᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using UC.property.2
    simp only [gauge, Matrix.UnitaryGroup.one_val, Matrix.one_mul, hC]
    rw [Matrix.mul_assoc, hUC, Matrix.mul_one]
  let Q := gauge UA⁻¹ UC B
  obtain ⟨P, W, hP, hQ⟩ := exists_right_unitary_polar Q
  obtain ⟨V, phase, hV, hphase⟩ := unitary_diagonalization W
  have hWV : gauge V⁻¹ V⁻¹ (W : Matrix n n ℂ) = diagonal phase := by
    simpa only [gauge, Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using hV
  have hBform : gauge (V⁻¹ * UA⁻¹) (V⁻¹ * UC) B =
      gauge V⁻¹ V⁻¹ P * diagonal phase := by
    rw [gauge_comp, ← show Q = gauge UA⁻¹ UC B from rfl, hQ, gauge_same_mul, hWV]
  have hnP : nuclear (gauge V⁻¹ V⁻¹ P) = nuclear B := by
    calc
      nuclear (gauge V⁻¹ V⁻¹ P) = nuclear P := nuclear_gauge _ _ _
      _ = nuclear (P * (W : Matrix n n ℂ)) := (nuclear_mul_unitary W P).symm
      _ = nuclear Q := by rw [hQ]
      _ = nuclear B := nuclear_gauge _ _ _
  refine ⟨V⁻¹ * UA⁻¹, V⁻¹ * 1, V⁻¹ * UC, ?_, ?_, ?_⟩
  · have hpos : (gauge (V⁻¹ * UA⁻¹) (V⁻¹ * 1) A).PosSemidef := by
      rw [gauge_comp, hga]
      exact gauge_posSemidef _ hPA
    exact (diagonalNorm_posSemidef hpos).trans (nuclear_gauge _ _ _)
  · rw [hBform]
    exact (diagonalNorm_mul_diagonal (gauge_posSemidef _ hP) phase hphase).trans hnP
  · have hpos : (gauge (V⁻¹ * 1) (V⁻¹ * UC) C).PosSemidef := by
      rw [gauge_comp, hgc]
      exact gauge_posSemidef _ hPC
    exact (diagonalNorm_posSemidef hpos).trans (nuclear_gauge _ _ _)

end Fidelity
end
/- END ORIGINAL SOURCE: DiagonalAttainment.lean -/


/- BEGIN ORIGINAL SOURCE: AbsThree.lean -/
section

/-!
Elementary positivity facts for entrywise absolute values of three-by-three
Hermitian matrices. This file is supporting work, not the entropy theorem.
-/

open scoped ComplexOrder
open Matrix

namespace Fidelity

noncomputable section

def entryAbs {n : Type*} (A : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => (‖A i j‖ : ℂ)

theorem entryAbs_isHermitian {n : Type*} {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : (entryAbs A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star (‖A j i‖ : ℂ) = (‖A i j‖ : ℂ)
  rw [Complex.star_def, Complex.conj_ofReal, ← hA.apply i j, norm_star]

theorem posSemidef_det_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) : 0 ≤ A.det := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_nonneg
  intro i _
  exact (Complex.nonneg_iff).2 ⟨hA.eigenvalues_nonneg i, by simp⟩

theorem diag_re_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (i : n) : 0 ≤ (A i i).re := by
  exact (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).1

theorem entryAbs_diag {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (i : n) :
    entryAbs A i i = A i i := by
  change (‖A i i‖ : ℂ) = A i i
  conv_lhs => rw [← hA.isHermitian.coe_re_apply_self i]
  change (‖((A i i).re : ℂ)‖ : ℂ) = A i i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (diag_re_nonneg hA i)]
  exact hA.isHermitian.coe_re_apply_self i

/-- Positive determinant after every nonnegative scalar shift forces a
Hermitian matrix to be positive definite. -/
theorem posDef_of_det_shift_pos {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hdet : ∀ t : ℝ, 0 ≤ t → 0 < ((t • (1 : Matrix n n ℂ)) + A).det.re) :
    A.PosDef := by
  have heig : ∀ i, 0 < hA.eigenvalues i := by
    intro i
    by_contra h
    have hEv : hA.eigenvalues i ≤ 0 := le_of_not_gt h
    let t : ℝ := -hA.eigenvalues i
    let v : n → ℂ := ⇑(hA.eigenvectorBasis i)
    have hv : v ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2
      (hA.eigenvectorBasis.orthonormal.ne_zero i)
    have hM : ((t • (1 : Matrix n n ℂ)) + A) *ᵥ v = 0 := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      dsimp only [v]
      rw [hA.mulVec_eigenvectorBasis]
      simp [t]
    have hne : ((t • (1 : Matrix n n ℂ)) + A).det ≠ 0 := by
      intro hz
      have hp := hdet t (neg_nonneg.mpr hEv)
      rw [hz, Complex.zero_re] at hp
      exact (lt_irrefl 0) hp
    have hu : IsUnit ((t • (1 : Matrix n n ℂ)) + A) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.mpr hne)
    apply hv
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hu)
    simpa using hM
  exact hA.posDef_iff_eigenvalues_pos.mpr heig

def hermitianThree (a b c : ℝ) (u v w : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(a : ℂ), u, v; star u, (b : ℂ), w; star v, star w, (c : ℂ)]

theorem det_hermitianThree_re (a b c : ℝ) (u v w : ℂ) :
    (hermitianThree a b c u v w).det.re =
      a * b * c + 2 * (u * w * star v).re -
        a * ‖w‖ ^ 2 - b * ‖v‖ ^ 2 - c * ‖u‖ ^ 2 := by
  simp only [hermitianThree, Matrix.det_fin_three]
  simp [Complex.mul_re, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem eq_hermitianThree {A : Matrix (Fin 3) (Fin 3) ℂ} (hA : A.IsHermitian) :
    A = hermitianThree (A 0 0).re (A 1 1).re (A 2 2).re (A 0 1) (A 0 2) (A 1 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianThree, hA.apply]
  all_goals exact (hA.coe_re_apply_self _).symm

theorem entryAbs_hermitianThree (a b c : ℝ) (u v w : ℂ) :
    entryAbs (hermitianThree a b c u v w) =
      hermitianThree |a| |b| |c| (‖u‖ : ℂ) (‖v‖ : ℂ) (‖w‖ : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [entryAbs, hermitianThree, Complex.norm_real, Real.norm_eq_abs]

theorem det_entryAbs_hermitianThree_le (a b c : ℝ) (u v w : ℂ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (hermitianThree a b c u v w).det.re ≤
      (entryAbs (hermitianThree a b c u v w)).det.re := by
  rw [entryAbs_hermitianThree, abs_of_nonneg ha, abs_of_nonneg hb,
    abs_of_nonneg hc, det_hermitianThree_re, det_hermitianThree_re]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm,
    Complex.star_def, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  have h := Complex.re_le_norm (u * w * star v)
  simp only [norm_mul, norm_star] at h
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im] at h
  nlinarith

theorem det_entryAbs_ge {A : Matrix (Fin 3) (Fin 3) ℂ} (hA : A.PosSemidef) :
    A.det.re ≤ (entryAbs A).det.re := by
  have h := det_entryAbs_hermitianThree_le
    (A 0 0).re (A 1 1).re (A 2 2).re (A 0 1) (A 0 2) (A 1 2)
    (diag_re_nonneg hA 0) (diag_re_nonneg hA 1) (diag_re_nonneg hA 2)
  rwa [← eq_hermitianThree hA.isHermitian] at h

theorem entryAbs_pair_product {n : Type*} {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (i j : n) :
    entryAbs A i j * entryAbs A j i = A i j * A j i := by
  have hji : A j i = star (A i j) := (hA.apply j i).symm
  change (‖A i j‖ : ℂ) * (‖A j i‖ : ℂ) = A i j * A j i
  rw [hji, norm_star, ← Complex.ofReal_mul, ← pow_two, Complex.sq_norm,
    Complex.star_def, Complex.mul_conj]

theorem minor_re_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (i j : n) :
    0 ≤ (A i i * A j j - A i j * A j i).re := by
  let e : Fin 2 → n := ![i, j]
  have h := (Complex.nonneg_iff.mp (posSemidef_det_nonneg (hA.submatrix e))).1
  rw [Matrix.det_fin_two] at h
  simpa [e] using h

theorem entryAbs_minor {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (i j : n) :
    entryAbs A i i * entryAbs A j j - entryAbs A i j * entryAbs A j i =
      A i i * A j j - A i j * A j i := by
  rw [entryAbs_diag hA i, entryAbs_diag hA j, entryAbs_pair_product hA.isHermitian]

theorem det_shift_three_re (A : Matrix (Fin 3) (Fin 3) ℂ) (t : ℝ) :
    (t • (1 : Matrix (Fin 3) (Fin 3) ℂ) + A).det.re =
      t ^ 3 + ((A 0 0).re + (A 1 1).re + (A 2 2).re) * t ^ 2 +
        ((A 0 0 * A 1 1 - A 0 1 * A 1 0).re +
          (A 0 0 * A 2 2 - A 0 2 * A 2 0).re +
          (A 1 1 * A 2 2 - A 1 2 * A 2 1).re) * t + A.det.re := by
  have hc : (t • (1 : Matrix (Fin 3) (Fin 3) ℂ) + A).det =
      (t : ℂ) ^ 3 + (A 0 0 + A 1 1 + A 2 2) * (t : ℂ) ^ 2 +
        ((A 0 0 * A 1 1 - A 0 1 * A 1 0) +
          (A 0 0 * A 2 2 - A 0 2 * A 2 0) +
          (A 1 1 * A 2 2 - A 1 2 * A 2 1)) * (t : ℂ) + A.det := by
    simp [Matrix.det_fin_three, Complex.real_smul]
    ring
  have hr := congrArg Complex.re hc
  simpa [Complex.add_re, Complex.mul_re, Complex.mul_im, pow_succ] using hr

/-- Entrywise absolute values preserve positive definiteness in dimension three. -/
theorem entryAbs_posDef_three {A : Matrix (Fin 3) (Fin 3) ℂ} (hA : A.PosDef) :
    (entryAbs A).PosDef := by
  apply posDef_of_det_shift_pos (entryAbs_isHermitian hA.isHermitian)
  intro t ht
  rw [det_shift_three_re, entryAbs_minor hA.posSemidef 0 1,
    entryAbs_minor hA.posSemidef 0 2, entryAbs_minor hA.posSemidef 1 2,
    entryAbs_diag hA.posSemidef 0, entryAbs_diag hA.posSemidef 1,
    entryAbs_diag hA.posSemidef 2]
  have hd : 0 < (entryAbs A).det.re :=
    lt_of_lt_of_le (Complex.pos_iff.mp hA.det_pos).1 (det_entryAbs_ge hA.posSemidef)
  have htr : 0 ≤ (A 0 0).re + (A 1 1).re + (A 2 2).re :=
    add_nonneg (add_nonneg (diag_re_nonneg hA.posSemidef 0)
      (diag_re_nonneg hA.posSemidef 1)) (diag_re_nonneg hA.posSemidef 2)
  have hm : 0 ≤ (A 0 0 * A 1 1 - A 0 1 * A 1 0).re +
      (A 0 0 * A 2 2 - A 0 2 * A 2 0).re +
      (A 1 1 * A 2 2 - A 1 2 * A 2 1).re :=
    add_nonneg (add_nonneg (minor_re_nonneg hA.posSemidef 0 1)
      (minor_re_nonneg hA.posSemidef 0 2)) (minor_re_nonneg hA.posSemidef 1 2)
  nlinarith [pow_nonneg ht 3, mul_nonneg htr (sq_nonneg t), mul_nonneg hm ht]

#print axioms entryAbs_posDef_three

/-- The analogous shifted-determinant criterion includes zero eigenvalues. -/
theorem posSemidef_of_det_shift_pos {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hdet : ∀ t : ℝ, 0 < t → 0 < ((t • (1 : Matrix n n ℂ)) + A).det.re) :
    A.PosSemidef := by
  have heig : ∀ i, 0 ≤ hA.eigenvalues i := by
    intro i
    by_contra h
    have hEv : hA.eigenvalues i < 0 := lt_of_not_ge h
    let t : ℝ := -hA.eigenvalues i
    let v : n → ℂ := ⇑(hA.eigenvectorBasis i)
    have hv : v ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2
      (hA.eigenvectorBasis.orthonormal.ne_zero i)
    have hM : ((t • (1 : Matrix n n ℂ)) + A) *ᵥ v = 0 := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      dsimp only [v]
      rw [hA.mulVec_eigenvectorBasis]
      simp [t]
    have hne : ((t • (1 : Matrix n n ℂ)) + A).det ≠ 0 := by
      intro hz
      have hp := hdet t (neg_pos.mpr hEv)
      rw [hz, Complex.zero_re] at hp
      exact (lt_irrefl 0) hp
    have hu : IsUnit ((t • (1 : Matrix n n ℂ)) + A) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.mpr hne)
    apply hv
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hu)
    simpa using hM
  exact hA.posSemidef_iff_eigenvalues_nonneg.mpr heig

/-- Entrywise absolute values preserve positive semidefiniteness in dimension three. -/
theorem entryAbs_posSemidef_three {A : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : A.PosSemidef) : (entryAbs A).PosSemidef := by
  apply posSemidef_of_det_shift_pos (entryAbs_isHermitian hA.isHermitian)
  intro t ht
  rw [det_shift_three_re, entryAbs_minor hA 0 1, entryAbs_minor hA 0 2,
    entryAbs_minor hA 1 2, entryAbs_diag hA 0, entryAbs_diag hA 1,
    entryAbs_diag hA 2]
  have hd : 0 ≤ (entryAbs A).det.re :=
    le_trans (Complex.nonneg_iff.mp (posSemidef_det_nonneg hA)).1 (det_entryAbs_ge hA)
  have htr : 0 ≤ (A 0 0).re + (A 1 1).re + (A 2 2).re :=
    add_nonneg (add_nonneg (diag_re_nonneg hA 0)
      (diag_re_nonneg hA 1)) (diag_re_nonneg hA 2)
  have hm : 0 ≤ (A 0 0 * A 1 1 - A 0 1 * A 1 0).re +
      (A 0 0 * A 2 2 - A 0 2 * A 2 0).re +
      (A 1 1 * A 2 2 - A 1 2 * A 2 1).re :=
    add_nonneg (add_nonneg (minor_re_nonneg hA 0 1)
      (minor_re_nonneg hA 0 2)) (minor_re_nonneg hA 1 2)
  nlinarith [pow_pos ht 3, mul_nonneg htr (sq_nonneg t), mul_nonneg hm ht.le]

#print axioms entryAbs_posSemidef_three

end
end Fidelity
end
/- END ORIGINAL SOURCE: AbsThree.lean -/


/- BEGIN ORIGINAL SOURCE: BlockDecomposition.lean -/
section

/-!
# The Li--Zhang three-block decomposition

This file formalizes the decomposition from Li and Zhang (2014), Theorem 1.
It records the unitary gauge explicitly, proves positivity of the scalar
principal submatrices, and proves exact entrywise recovery of every block
nuclear norm after taking absolute values and summing the scalar matrices.
It does not itself prove an entropy inequality.
-/

open scoped Matrix ComplexOrder
open Matrix

namespace Fidelity

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem gauge_conjTranspose (L R : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    gauge R L Aᴴ = (gauge L R A)ᴴ := by
  simp only [gauge, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

omit [Fintype n] [DecidableEq n] in
theorem matrixBlock_flip [Fintype n] [DecidableEq n] {s : Type*} [Fintype s] [DecidableEq s]
    {G : Matrix (n × s) (n × s) ℂ} (hG : G.IsHermitian) (i j : s) :
    matrixBlock G j i = (matrixBlock G i j)ᴴ := by
  ext r t
  exact congrArg (fun M : Matrix (n × s) (n × s) ℂ => M (r, j) (t, i)) hG.eq.symm

noncomputable def normCompression3 (G : Matrix (n × Fin 3) (n × Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => (nuclear (matrixBlock G i j) : ℂ)

/-- Every positive three-by-three block matrix has a block-diagonal unitary
gauge in which scalar internal slices attain all the block nuclear norms. -/
theorem exists_three_block_diagonal_attainment
    {G : Matrix (n × Fin 3) (n × Fin 3) ℂ} (hG : G.PosSemidef) :
    ∃ U : Fin 3 → Matrix.unitaryGroup n ℂ,
      let D := Matrix.blockDiagonal (fun i => (U i : Matrix n n ℂ))
      (∀ r, (scalarSlice (D * G * Dᴴ) r).PosSemidef) ∧
      (∀ i j, (∑ r, ‖scalarSlice (D * G * Dᴴ) r i j‖) =
        nuclear (matrixBlock G i j)) := by
  classical
  obtain ⟨U₀, U₁, U₂, h01, h02, h12⟩ := exists_triangle_diagonal_attainment
    (matrixBlock G 0 1) (matrixBlock G 0 2) (matrixBlock G 1 2)
  let U : Fin 3 → Matrix.unitaryGroup n ℂ := ![U₀, U₁, U₂]
  let D := Matrix.blockDiagonal (fun i => (U i : Matrix n n ℂ))
  have hd (i : Fin 3) : diagonalNorm (gauge (U i) (U i) (matrixBlock G i i)) =
      nuclear (matrixBlock G i i) := by
    have hi : (matrixBlock G i i).PosSemidef := hG.submatrix (fun r => (r, i))
    exact (diagonalNorm_posSemidef (gauge_posSemidef (U i) hi)).trans
      (nuclear_gauge _ _ _)
  have h01' : diagonalNorm (gauge (U 0) (U 1) (matrixBlock G 0 1)) =
      nuclear (matrixBlock G 0 1) := by simpa [U] using h01
  have h02' : diagonalNorm (gauge (U 0) (U 2) (matrixBlock G 0 2)) =
      nuclear (matrixBlock G 0 2) := by simpa [U] using h02
  have h12' : diagonalNorm (gauge (U 1) (U 2) (matrixBlock G 1 2)) =
      nuclear (matrixBlock G 1 2) := by simpa [U] using h12
  have hreverse (i j : Fin 3)
      (h : diagonalNorm (gauge (U i) (U j) (matrixBlock G i j)) =
        nuclear (matrixBlock G i j)) :
      diagonalNorm (gauge (U j) (U i) (matrixBlock G j i)) =
        nuclear (matrixBlock G j i) := by
    rw [matrixBlock_flip hG.isHermitian i j, gauge_conjTranspose,
      diagonalNorm_conjTranspose, nuclear_conjTranspose]
    exact h
  have hall (i j : Fin 3) : diagonalNorm (gauge (U i) (U j) (matrixBlock G i j)) =
      nuclear (matrixBlock G i j) := by
    fin_cases i <;> fin_cases j
    · exact hd 0
    · exact h01'
    · exact h02'
    · exact hreverse 0 1 h01'
    · exact hd 1
    · exact h12'
    · exact hreverse 0 2 h02'
    · exact hreverse 1 2 h12'
    · exact hd 2
  refine ⟨U, ?_, ?_⟩
  · intro r
    exact (hG.mul_mul_conjTranspose_same D).submatrix (fun i => (r, i))
  · intro i j
    simp_rw [scalarSlice_blockDiagonal_conjugate]
    exact hall i j

/-- The exact finite decomposition used before the entropy argument. -/
theorem exists_li_zhang_decomposition
    {G : Matrix (n × Fin 3) (n × Fin 3) ℂ} (hG : G.PosSemidef) :
    ∃ U : Fin 3 → Matrix.unitaryGroup n ℂ,
      let D := Matrix.blockDiagonal (fun i => (U i : Matrix n n ℂ))
      let H := scalarSlice (D * G * Dᴴ)
      (∀ r, (H r).PosSemidef) ∧
      normCompression3 G = ∑ r, entryAbs (H r) := by
  obtain ⟨U, hpos, hnorm⟩ := exists_three_block_diagonal_attainment hG
  refine ⟨U, hpos, ?_⟩
  ext i j
  simp only [normCompression3, Matrix.sum_apply, entryAbs]
  rw [← Complex.ofReal_sum]
  exact congrArg (fun x : ℝ => (x : ℂ)) (hnorm i j).symm

/-- Three-block nuclear-norm compression is positive semidefinite. This is
the known Li--Zhang/Drury positivity theorem, included as a consequence. -/
theorem normCompression3_posSemidef
    {G : Matrix (n × Fin 3) (n × Fin 3) ℂ} (hG : G.PosSemidef) :
    (normCompression3 G).PosSemidef := by
  classical
  obtain ⟨U, hpos, hnorm⟩ := exists_li_zhang_decomposition hG
  rw [hnorm]
  exact Matrix.posSemidef_sum Finset.univ
    (fun r _ => entryAbs_posSemidef_three (hpos r))

/-- A block-diagonal unitary preserves positive definiteness. -/
theorem blockDiagonal_conjugate_posDef {s : Type*} [Fintype s] [DecidableEq s]
    {G : Matrix (n × s) (n × s) ℂ} (hG : G.PosDef)
    (U : s → Matrix.unitaryGroup n ℂ) :
    let D := Matrix.blockDiagonal (fun i => (U i : Matrix n n ℂ))
    (D * G * Dᴴ).PosDef := by
  let DU : Matrix.unitaryGroup (n × s) ℂ :=
    ⟨Matrix.blockDiagonal (fun i => (U i : Matrix n n ℂ)), blockDiagonal_mem_unitary U⟩
  exact hG.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit (Unitary.isUnit_coe (U := DU)))

/-- Internal scalar slices are positive definite when the original matrix is. -/
theorem scalarSlice_blockDiagonal_conjugate_posDef
    {s : Type*} [Fintype s] [DecidableEq s]
    {G : Matrix (n × s) (n × s) ℂ} (hG : G.PosDef)
    (U : s → Matrix.unitaryGroup n ℂ) (r : n) :
    let D := Matrix.blockDiagonal (fun i => (U i : Matrix n n ℂ))
    (scalarSlice (D * G * Dᴴ) r).PosDef := by
  exact (blockDiagonal_conjugate_posDef hG U).submatrix
    (fun i j h => (Prod.mk.inj h).2)

/-- The same exact decomposition with positive-definite scalar summands. -/
theorem exists_li_zhang_decomposition_posDef
    {G : Matrix (n × Fin 3) (n × Fin 3) ℂ} (hG : G.PosDef) :
    ∃ U : Fin 3 → Matrix.unitaryGroup n ℂ,
      let D := Matrix.blockDiagonal (fun i => (U i : Matrix n n ℂ))
      let H := scalarSlice (D * G * Dᴴ)
      (∀ r, (H r).PosDef) ∧
      normCompression3 G = ∑ r, entryAbs (H r) := by
  obtain ⟨U, _, hsum⟩ := exists_li_zhang_decomposition hG.posSemidef
  exact ⟨U, scalarSlice_blockDiagonal_conjugate_posDef hG U, hsum⟩

theorem normCompression3_posDef [Nonempty n]
    {G : Matrix (n × Fin 3) (n × Fin 3) ℂ} (hG : G.PosDef) :
    (normCompression3 G).PosDef := by
  obtain ⟨U, hpos, hsum⟩ := exists_li_zhang_decomposition_posDef hG
  rw [hsum]
  exact Matrix.posDef_sum Finset.univ_nonempty
    (fun r _ => entryAbs_posDef_three (hpos r))

end Fidelity
end
/- END ORIGINAL SOURCE: BlockDecomposition.lean -/


/- BEGIN ORIGINAL SOURCE: BlockEntropy.lean -/
section

/-! Direct-sum and block-pinching identities. These statements concern
matrices and quantumRelativeEntropy. -/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Matrix

namespace Fidelity

noncomputable section

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

def blockOf (G : Matrix (n × ι) (n × ι) ℂ) (i j : ι) : Matrix n n ℂ :=
  G.submatrix (fun r => (r, i)) (fun s => (s, j))

def blockPinch (G : Matrix (n × ι) (n × ι) ℂ) : Matrix (n × ι) (n × ι) ℂ :=
  Matrix.blockDiagonal fun i => blockOf G i i

omit [Fintype n] [DecidableEq n] [Fintype ι] in
theorem blockDiagonal_isHermitian [Fintype n] [DecidableEq n] [Fintype ι] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) : (Matrix.blockDiagonal A).IsHermitian := by
  change (Matrix.blockDiagonal A)ᴴ = Matrix.blockDiagonal A
  rw [Matrix.blockDiagonal_conjTranspose]
  congr 1
  funext i
  exact (hA i).eq

/-- Block diagonals form a real star-algebra embedding. -/
def blockDiagonalStarAlgHom :
    (ι → Matrix n n ℂ) →⋆ₐ[ℝ] Matrix (n × ι) (n × ι) ℂ :=
  { Matrix.blockDiagonalRingHom n ι ℂ with
    toFun := Matrix.blockDiagonal
    commutes' := fun r => by
      simp only [Algebra.algebraMap_eq_smul_one, Matrix.blockDiagonal_smul,
        Matrix.blockDiagonal_one]
    map_star' := fun A => by
      simp only [Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_conjTranspose]
      rfl }

@[simp] theorem blockDiagonalStarAlgHom_apply (A : ι → Matrix n n ℂ) :
    blockDiagonalStarAlgHom A = Matrix.blockDiagonal A := rfl

/-- Positivity of a finite block diagonal follows from the order preservation
of its star-algebra embedding. -/
theorem blockDiagonal_posSemidef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) : (Matrix.blockDiagonal A).PosSemidef := by
  have ha : (0 : ι → Matrix n n ℂ) ≤ A := fun i => (hA i).nonneg
  have hm := OrderHomClass.mono (blockDiagonalStarAlgHom (n := n) (ι := ι)) ha
  have hn : (0 : Matrix (n × ι) (n × ι) ℂ) ≤ Matrix.blockDiagonal A := by
    simpa only [map_zero, blockDiagonalStarAlgHom_apply] using hm
  exact Matrix.nonneg_iff_posSemidef.mp hn

theorem blockDiagonal_posDef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosDef) : (Matrix.blockDiagonal A).PosDef := by
  have hpsd := blockDiagonal_posSemidef A fun i => (hA i).posSemidef
  apply hpsd.posDef_iff_isUnit.mpr
  have hu : IsUnit A := Pi.isUnit_iff.mpr fun i => (hA i).isUnit
  exact hu.map (Matrix.blockDiagonalRingHom n ι ℂ)

set_option backward.isDefEq.respectTransparency false in
/-- Real functional calculus acts separately on the diagonal blocks. -/
theorem cfc_blockDiagonal (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.blockDiagonal A) = Matrix.blockDiagonal fun i => cfc f (A i) := by
  let : CStarAlgebra (ι → Matrix n n ℂ) := inferInstance
  let : ContinuousFunctionalCalculus ℝ (ι → Matrix n n ℂ) IsSelfAdjoint :=
    (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
      (A := ι → Matrix n n ℂ)).toContinuousFunctionalCalculus
  let φ := blockDiagonalStarAlgHom (n := n) (ι := ι)
  have ha : IsSelfAdjoint A := funext fun i => (hA i).eq
  have hspec : ContinuousOn f (⋃ i, spectrum ℝ (A i)) :=
    (Set.finite_iUnion fun i => (A i).finite_real_spectrum).continuousOn f
  have hf : ContinuousOn f (spectrum ℝ A) := by
    rwa [Pi.spectrum_eq]
  have hφ : Continuous φ := φ.toLinearMap.continuous_of_finiteDimensional
  have hnat := φ.map_cfc f A hf hφ ha (ha.map φ)
  rw [cfc_map_pi (S := ℝ) f A hspec ha (fun i => (hA i).isSelfAdjoint)] at hnat
  simpa only [φ, blockDiagonalStarAlgHom_apply] using hnat.symm

theorem log_blockDiagonal (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) :
    CFC.log (Matrix.blockDiagonal A) = Matrix.blockDiagonal fun i => CFC.log (A i) :=
  cfc_blockDiagonal A hA Real.log

/-- Relative entropy is additive over a finite direct sum, without normalization. -/
theorem relativeEntropy_blockDiagonal (A B : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hB : ∀ i, (B i).IsHermitian) :
    quantumRelativeEntropy (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) =
      ∑ i, quantumRelativeEntropy (A i) (B i) := by
  simp only [quantumRelativeEntropy, log_blockDiagonal A hA, log_blockDiagonal B hB,
    ← Matrix.blockDiagonal_sub, ← Matrix.blockDiagonal_mul,
    Matrix.trace_blockDiagonal, Complex.re_sum, Pi.sub_apply]

theorem entropy_blockDiagonal (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) :
    vonNeumannEntropy (Matrix.blockDiagonal A) (blockDiagonal_isHermitian A hA) =
      ∑ i, vonNeumannEntropy (A i) (hA i) := by
  simp only [vonNeumannEntropy_eq_neg_trace_mul_log, log_blockDiagonal A hA,
    ← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal, Complex.re_sum,
    Finset.sum_neg_distrib]

theorem trace_mul_blockDiagonal (G : Matrix (n × ι) (n × ι) ℂ)
    (B : ι → Matrix n n ℂ) :
    (G * Matrix.blockDiagonal B).trace = ∑ i, (blockOf G i i * B i).trace := by
  calc
    (G * Matrix.blockDiagonal B).trace =
        ∑ i, (blockOf (G * Matrix.blockDiagonal B) i i).trace := by
      simp only [Matrix.trace, Matrix.diag_apply, blockOf, Matrix.submatrix_apply,
        Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ = ∑ i, (blockOf G i i * B i).trace := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg Matrix.trace (matrixBlock_mul_blockDiagonal G B i i)

omit [Fintype n] [DecidableEq n] [Fintype ι] in
theorem blockOf_blockPinch_diag [Fintype n] [DecidableEq n] [Fintype ι] (G : Matrix (n × ι) (n × ι) ℂ) (i : ι) :
    blockOf (blockPinch G) i i = blockOf G i i := by
  ext r s
  simp [blockOf, blockPinch, Matrix.blockDiagonal_apply]

theorem blockPinch_isHermitian {G : Matrix (n × ι) (n × ι) ℂ}
    (hG : G.IsHermitian) : (blockPinch G).IsHermitian :=
  blockDiagonal_isHermitian _ fun i => hG.submatrix (fun r => (r, i))

theorem blockPinch_posDef {G : Matrix (n × ι) (n × ι) ℂ}
    (hG : G.PosDef) : (blockPinch G).PosDef := by
  apply blockDiagonal_posDef
  intro i
  exact hG.submatrix (fun _ _ h => (Prod.mk.inj h).1)

/-- The relative entropy to the block diagonal equals the block entropy loss. -/
theorem relativeEntropy_blockPinch_eq {G : Matrix (n × ι) (n × ι) ℂ}
    (hG : G.IsHermitian) :
    quantumRelativeEntropy G (blockPinch G) =
      vonNeumannEntropy (blockPinch G) (blockPinch_isHermitian hG) -
        vonNeumannEntropy G hG := by
  have hblocks : ∀ i, (blockOf G i i).IsHermitian :=
    fun i => hG.submatrix (fun r => (r, i))
  have hlog : CFC.log (blockPinch G) =
      Matrix.blockDiagonal fun i => CFC.log (blockOf G i i) :=
    log_blockDiagonal _ hblocks
  have ht : (G * CFC.log (blockPinch G)).trace =
      (blockPinch G * CFC.log (blockPinch G)).trace := by
    rw [hlog, trace_mul_blockDiagonal, trace_mul_blockDiagonal]
    simp only [blockOf_blockPinch_diag]
  rw [quantumRelativeEntropy_eq_neg_entropy_sub_trace_mul_log hG,
    vonNeumannEntropy_eq_neg_trace_mul_log (blockPinch_isHermitian hG), ht]
  ring

end
end Fidelity
end
/- END ORIGINAL SOURCE: BlockEntropy.lean -/


/- BEGIN ORIGINAL SOURCE: BlockGaugePinching.lean -/
section

open scoped Matrix
open Matrix

namespace Fidelity

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- Outer block pinching commutes with a block-diagonal change of basis. -/
theorem blockPinch_blockDiagonal_conjugate
    (G : Matrix (n × ι) (n × ι) ℂ) (U : ι → Matrix n n ℂ) :
    blockPinch (Matrix.blockDiagonal U * G * (Matrix.blockDiagonal U)ᴴ) =
      Matrix.blockDiagonal U * blockPinch G * (Matrix.blockDiagonal U)ᴴ := by
  change Matrix.blockDiagonal
      (fun i => matrixBlock (Matrix.blockDiagonal U * G * (Matrix.blockDiagonal U)ᴴ) i i) =
    Matrix.blockDiagonal U * Matrix.blockDiagonal (fun i => matrixBlock G i i) *
      (Matrix.blockDiagonal U)ᴴ
  conv_rhs =>
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
      ← Matrix.blockDiagonal_mul]
  apply congrArg Matrix.blockDiagonal
  funext i
  exact matrixBlock_blockDiagonal_conjugate G U i i

omit [Fintype n] [DecidableEq n] [Fintype ι] in
/-- An internal scalar slice of the outer block diagonal is exactly the
diagonal of that scalar slice. -/
theorem scalarSlice_blockPinch [Fintype n] [DecidableEq n] [Fintype ι] (G : Matrix (n × ι) (n × ι) ℂ) (r : n) :
    scalarSlice (blockPinch G) r = Matrix.diagonal (fun i => scalarSlice G r i i) := by
  ext i j
  by_cases hij : i = j <;>
    simp [scalarSlice, blockPinch, blockOf, Matrix.blockDiagonal_apply,
      hij]

end Fidelity
end
/- END ORIGINAL SOURCE: BlockGaugePinching.lean -/


/- BEGIN ORIGINAL SOURCE: GibbsVariational.lean -/
section
/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/

/-!
# Extracted unnormalized Gibbs variational inequality

These are the initial proved declarations of QICLean's
`Analysis/LiebTraceExponential.lean`, commit
`acda92aa70e69b37507e422bceb5414036859fe6`.
Their statements and proof bodies are unchanged. The later Lieb-concavity
results and their otherwise unused data-processing import are omitted to
reduce the dependency graph. This extraction is prior work, not a new result.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Scaling the second argument of the relative entropy by `c > 0` shifts it by
`-(log c) Re tr X`, since `log (c Y) = (log c) 1 + log Y`. -/
theorem quantumRelativeEntropy_smul_right (X : Matrix n n ℂ) {Y : Matrix n n ℂ}
    (hY : Y.PosDef) {c : ℝ} (hc : 0 < c) :
    quantumRelativeEntropy X (c • Y) =
      quantumRelativeEntropy X Y - Real.log c * (X.trace).re := by
  rw [quantumRelativeEntropy_eq_trace_mul_log_sub, quantumRelativeEntropy_eq_trace_mul_log_sub,
    CFC.log_smul' Y hc hY.isStrictlyPositive, Algebra.algebraMap_eq_smul_one, Matrix.mul_add,
    Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul, Complex.add_re,
    Complex.real_smul, Complex.re_ofReal_mul]
  ring

/-- **Klein's inequality without trace normalization.** For positive definite `X` and `Y`,
`Re tr X - Re tr Y ≤ D(X‖Y)`.

Normalizing `X = a ρ` and `Y = b σ` with `a = tr X` and `b = tr Y`, the relative entropy is
`D(X‖Y) = a D(ρ‖σ) + a log (a / b) ≥ a log (a / b) ≥ a - b`, by Klein's inequality for
the density matrices `ρ` and `σ` and the scalar bound `log x ≤ x - 1`. -/
theorem re_trace_sub_re_trace_le_quantumRelativeEntropy {X Y : Matrix n n ℂ}
    (hX : X.PosDef) (hY : Y.PosDef) :
    (X.trace).re - (Y.trace).re ≤ quantumRelativeEntropy X Y := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [quantumRelativeEntropy, Matrix.trace]
  set a := (X.trace).re with ha_def
  set b := (Y.trace).re with hb_def
  have hXtr := Complex.pos_iff.mp hX.trace_pos
  have hYtr := Complex.pos_iff.mp hY.trace_pos
  have ha : 0 < a := hXtr.1
  have hb : 0 < b := hYtr.1
  have hXa : X.trace = (a : ℂ) := Complex.ext (by simp [a]) (by simp [hXtr.2])
  have hYb : Y.trace = (b : ℂ) := Complex.ext (by simp [b]) (by simp [hYtr.2])
  set ρ := a⁻¹ • X with hρ
  set σ := b⁻¹ • Y with hσ
  have hρ_pd : ρ.PosDef := hX.smul (inv_pos.mpr ha)
  have hσ_pd : σ.PosDef := hY.smul (inv_pos.mpr hb)
  have hρ_tr : ρ.trace = 1 := by
    rw [hρ, Matrix.trace_smul, hXa, Complex.real_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ ha.ne', Complex.ofReal_one]
  have hσ_tr : σ.trace = 1 := by
    rw [hσ, Matrix.trace_smul, hYb, Complex.real_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hb.ne', Complex.ofReal_one]
  have hklein : 0 ≤ quantumRelativeEntropy ρ σ :=
    quantumRelativeEntropy_nonneg hρ_pd.posSemidef hρ_tr hσ_pd.posSemidef hσ_tr
      (Matrix.isUnit_iff_isUnit_det _ |>.mp hσ_pd.isUnit)
  -- `X = a ρ` and `(a / b) Y = a σ`.
  have hXρ : X = a • ρ := by rw [hρ, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have hYσ : (a / b) • Y = a • σ := by rw [hσ, smul_smul, div_eq_mul_inv]
  have hY_eq : Y = (b / a) • ((a / b) • Y) := by
    rw [smul_smul, show b / a * (a / b) = 1 by field_simp, one_smul]
  have hscale : quantumRelativeEntropy X ((a / b) • Y) = a * quantumRelativeEntropy ρ σ := by
    rw [hYσ, hXρ, Matrix.quantumRelativeEntropy_smul_posDef hρ_pd hσ_pd ha]
  have hD : quantumRelativeEntropy X Y =
      a * quantumRelativeEntropy ρ σ - Real.log (b / a) * a := by
    conv_lhs => rw [hY_eq]
    rw [quantumRelativeEntropy_smul_right X (hY.smul (div_pos ha hb)) (div_pos hb ha), hscale]
  have hlog : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hlog' : Real.log (b / a) * a ≤ b - a := by
    have := mul_le_mul_of_nonneg_right hlog ha.le
    rwa [sub_mul, div_mul_cancel₀ _ ha.ne', one_mul] at this
  rw [hD]
  nlinarith [mul_nonneg ha.le hklein]

/-- The exponential of a Hermitian matrix is positive definite. -/
theorem Matrix.IsHermitian.posDef_exp {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (NormedSpace.exp M).PosDef := by
  rw [← CFC.real_exp_eq_normedSpace_exp hM.isSelfAdjoint]
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    ((cfc_isStrictlyPositive_iff Real.exp M Real.continuous_exp.continuousOn
      hM.isSelfAdjoint).mpr fun x _ => Real.exp_pos x)

/-- For Hermitian `H`, `D(X‖exp (H + log A)) = D(X‖A) - Re tr X H`, because
`log exp (H + log A) = H + log A`. -/
theorem quantumRelativeEntropy_exp_add_log (X A : Matrix n n ℂ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) :
    quantumRelativeEntropy X (NormedSpace.exp (H + CFC.log A)) =
      quantumRelativeEntropy X A - (X * H).trace.re := by
  rw [quantumRelativeEntropy_eq_trace_mul_log_sub, quantumRelativeEntropy_eq_trace_mul_log_sub,
    CFC.log_exp _ (hH.isSelfAdjoint.add IsSelfAdjoint.log), Matrix.mul_add, Matrix.trace_add,
    Complex.add_re]
  ring

/-- **Variational inequality for the trace exponential** (Tropp 2012, Lemma; Lieb 1973).
For Hermitian `H` and positive definite `X`,
`Re tr X H - D(X‖A) + Re tr X ≤ Re tr exp (H + log A)`.

With `Y = exp (H + log A)`, the left side minus the right side equals
`Re tr X - Re tr Y - D(X‖Y)`, which is nonpositive by the unnormalized Klein inequality. -/
theorem re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_le {X : Matrix n n ℂ}
    (hX : X.PosDef) (A : Matrix n n ℂ) {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (X * H).trace.re - quantumRelativeEntropy X A + (X.trace).re ≤
      (NormedSpace.exp (H + CFC.log A)).trace.re := by
  have h := re_trace_sub_re_trace_le_quantumRelativeEntropy hX
    (hH.add (IsSelfAdjoint.log (a := A)).isHermitian).posDef_exp
  rw [quantumRelativeEntropy_exp_add_log X A hH] at h
  linarith


#print axioms re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_le
end
/- END ORIGINAL SOURCE: GibbsVariational.lean -/


/- BEGIN ORIGINAL SOURCE: ScalarExponential.lean -/
section

/-!
# Entrywise comparison for finite matrix exponentials

These theorems concern the actual exponential defined by its convergent power
series. They are auxiliary established inequalities, not a formal verification
of the proposed three-state entropy theorem.
-/

open scoped BigOperators

namespace Fidelity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise domination by a real matrix propagates to every natural power. -/
theorem norm_pow_entry_le (A : Matrix ι ι ℂ) (B : Matrix ι ι ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ B i j) (k : ℕ) :
    ∀ i j, ‖(A ^ k) i j‖ ≤ (B ^ k) i j := by
  induction k with
  | zero =>
    intro i j
    by_cases hij : i = j <;> simp [hij]
  | succ k ih =>
    intro i j
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    calc
      ‖∑ l, (A ^ k) i l * A l j‖ ≤ ∑ l, ‖(A ^ k) i l * A l j‖ :=
        norm_sum_le _ _
      _ = ∑ l, ‖(A ^ k) i l‖ * ‖A l j‖ := by simp only [norm_mul]
      _ ≤ ∑ l, (B ^ k) i l * B l j := by
        apply Finset.sum_le_sum
        intro l _
        exact mul_le_mul (ih i l) (h l j) (norm_nonneg _)
          ((norm_nonneg _).trans (ih i l))

/-- Entrywise domination propagates to the actual convergent matrix exponential. -/
theorem norm_exp_entry_le (A : Matrix ι ι ℂ) (B : Matrix ι ι ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ B i j) (i j : ι) :
    ‖(NormedSpace.exp A) i j‖ ≤ (NormedSpace.exp B) i j := by
  let : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  have hA := Pi.hasSum.mp (Pi.hasSum.mp
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A) i) j
  have hB := Pi.hasSum.mp (Pi.hasSum.mp
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) B) i) j
  apply hA.norm_le_of_bounded hB
  intro k
  have hc : 0 ≤ ((Nat.factorial k : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg (Nat.factorial k))
  simp only [Matrix.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hc, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_entry_le A B h k i j) hc

-- Match the local operator-norm instances with the canonical matrix ring,
-- as in mathlib's matrix-exponential wrappers; kernel checking is unchanged.
set_option backward.isDefEq.respectTransparency false in
/-- A real scalar shift of a matrix exponent factors out as a positive scalar. -/
theorem exp_add_real_smul_one {𝕂 : Type*} [RCLike 𝕂]
    (A : Matrix ι ι 𝕂) (c : ℝ) :
    NormedSpace.exp (A + c • (1 : Matrix ι ι 𝕂)) =
      Real.exp c • NormedSpace.exp A := by
  let : NormedRing (Matrix ι ι 𝕂) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix ι ι 𝕂) := Matrix.linftyOpNormedAlgebra
  rw [← Algebra.algebraMap_eq_smul_one,
    Matrix.exp_add_of_commute _ _ (Algebra.commutes c A).symm,
    ← NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix ι ι 𝕂) c,
    Real.exp_eq_exp_ℝ,
    Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one]

/-- Off-diagonal domination suffices when the diagonals agree and are real. -/
theorem norm_exp_entry_le_of_offdiag (A : Matrix ι ι ℂ) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, A i i = (B i i : ℂ))
    (hoff : ∀ i j, i ≠ j → ‖A i j‖ ≤ B i j) (i j : ι) :
    ‖(NormedSpace.exp A) i j‖ ≤ (NormedSpace.exp B) i j := by
  classical
  let c : ℝ := ∑ k, |B k k|
  have hc : ∀ k, 0 ≤ B k k + c := by
    intro k
    have hk : |B k k| ≤ c :=
      Finset.single_le_sum (fun l _ => abs_nonneg (B l l)) (Finset.mem_univ k)
    have hh : -B k k ≤ c := (neg_le_abs (B k k)).trans hk
    have hh' : 0 ≤ c + B k k := neg_le_iff_add_nonneg.mp hh
    simpa only [add_comm] using hh'
  have hshift : ∀ k l,
      ‖(A + c • (1 : Matrix ι ι ℂ)) k l‖ ≤
        (B + c • (1 : Matrix ι ι ℝ)) k l := by
    intro k l
    by_cases hkl : k = l
    · subst l
      calc
        ‖(A + c • (1 : Matrix ι ι ℂ)) k k‖ = ‖((B k k + c : ℝ) : ℂ)‖ := by
          congr 1
          simp [hdiag, Complex.real_smul]
        _ = B k k + c := by
          rw [Complex.norm_real, Real.norm_of_nonneg (hc k)]
        _ ≤ (B + c • (1 : Matrix ι ι ℝ)) k k := by simp
    · simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hkl]
        using hoff k l hkl
  have h := norm_exp_entry_le (A + c • (1 : Matrix ι ι ℂ))
    (B + c • (1 : Matrix ι ι ℝ)) hshift i j
  rw [exp_add_real_smul_one, exp_add_real_smul_one] at h
  simp only [Matrix.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos c), smul_eq_mul] at h
  exact (mul_le_mul_iff_right₀ (Real.exp_pos c)).mp h

/-- Trace-exponential domination for arbitrary real diagonal and dominated off-diagonal entries. -/
theorem re_trace_exp_le_of_offdiag (A : Matrix ι ι ℂ) (B : Matrix ι ι ℝ)
    (hdiag : ∀ i, A i i = (B i i : ℂ))
    (hoff : ∀ i j, i ≠ j → ‖A i j‖ ≤ B i j) :
    (NormedSpace.exp A).trace.re ≤ (NormedSpace.exp B).trace := by
  simp only [Matrix.trace, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (Complex.re_le_norm _).trans (norm_exp_entry_le_of_offdiag A B hdiag hoff i i)

#print axioms norm_pow_entry_le
#print axioms norm_exp_entry_le
#print axioms norm_exp_entry_le_of_offdiag
#print axioms re_trace_exp_le_of_offdiag

end

end Fidelity

end
/- END ORIGINAL SOURCE: ScalarExponential.lean -/


/- BEGIN ORIGINAL SOURCE: ScalarPhase.lean -/
section

/-! Elementary scalar-phase matrix identities for the three-state entropy attempt.
These are auxiliary identities, not the entropy inequality itself. -/

open scoped BigOperators
open ComplexConjugate

namespace Fidelity

noncomputable section

/-- A unit-modulus phase, choosing one at zero. -/
def scalarPhase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

theorem norm_scalarPhase (z : ℂ) : ‖scalarPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [scalarPhase, hz]
  · simp [scalarPhase, hz, Complex.norm_real,
      norm_ne_zero_iff.mpr hz]

theorem scalarPhase_conj (z : ℂ) : scalarPhase (conj z) = conj (scalarPhase z) := by
  by_cases hz : z = 0
  · simp [scalarPhase, hz]
  · simp [scalarPhase, hz]

theorem mul_conj_scalarPhase (z : ℂ) : z * conj (scalarPhase z) = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [scalarPhase, hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    simp only [scalarPhase, ite_eq_right hz, map_div₀, Complex.conj_ofReal, ← mul_div_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    rw [pow_two, mul_div_cancel_right₀ _ hn]

/-- The selected scalar phase viewed as an element of the multiplicative unit circle. -/
def phaseCircle (z : ℂ) : Circle :=
  ⟨scalarPhase z, mem_sphere_zero_iff_norm.mpr (norm_scalarPhase z)⟩

@[simp] theorem coe_phaseCircle (z : ℂ) : (phaseCircle z : ℂ) = scalarPhase z := rfl

theorem phase_score_le (z : ℂ) (u : Circle) :
    (z * conj (u : ℂ)).re ≤ ‖z‖ := by
  calc
    (z * conj (u : ℂ)).re ≤ ‖z * conj (u : ℂ)‖ := Complex.re_le_norm _
    _ = ‖z‖ := by simp [Circle.norm_coe]

theorem phase_score_max (z : ℂ) :
    (z * conj (phaseCircle z : ℂ)).re = ‖z‖ := by
  rw [coe_phaseCircle, mul_conj_scalarPhase]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lift a real matrix by the phases of a complex matrix, fixing its diagonal. -/
def phaseLift (A : Matrix ι ι ℂ) (K : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  fun i j => if i = j then (K i i : ℂ) else (K i j : ℂ) * scalarPhase (A i j)

omit [Fintype ι] in
theorem phaseLift_diag [Fintype ι] (A : Matrix ι ι ℂ) (K : Matrix ι ι ℝ) (i : ι) :
    phaseLift A K i i = (K i i : ℂ) := by simp [phaseLift]

omit [Fintype ι] in
theorem phaseLift_isHermitian [Fintype ι] {A : Matrix ι ι ℂ} {K : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hK : K.IsSymm) : (phaseLift A K).IsHermitian := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.conjTranspose_apply, phaseLift]
  · have hji : j ≠ i := Ne.symm hij
    have hAij : conj (A j i) = A i j := congrFun (congrFun hA i) j
    have hKij : K j i = K i j := congrFun (congrFun hK i) j
    simp [Matrix.conjTranspose_apply, phaseLift, hij, hji, hKij,
      ← scalarPhase_conj, hAij]

omit [Fintype ι] in
theorem norm_phaseLift_offdiag [Fintype ι] (A : Matrix ι ι ℂ) (K : Matrix ι ι ℝ)
    (i j : ι) (hij : i ≠ j) (hK : 0 ≤ K i j) :
    ‖phaseLift A K i j‖ = K i j := by
  simp [phaseLift, hij, norm_scalarPhase, Complex.norm_real,
    Real.norm_of_nonneg hK]

theorem mul_phaseLift_swap {A : Matrix ι ι ℂ} {K : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hK : K.IsSymm)
    (hdiag : ∀ i, A i i = (‖A i i‖ : ℂ)) (i j : ι) :
    A i j * phaseLift A K j i = (K i j * ‖A i j‖ : ℝ) := by
  by_cases hij : i = j
  · subst j
    rw [phaseLift_diag, Complex.ofReal_mul]
    exact (congrArg (fun z : ℂ => z * (K i i : ℂ)) (hdiag i)).trans (mul_comm _ _)
  · have hji : j ≠ i := Ne.symm hij
    have hAij : A j i = conj (A i j) := by
      have h := congrFun (congrFun hA j) i
      exact h.symm
    have hKij : K j i = K i j := congrFun (congrFun hK i) j
    rw [phaseLift, ite_eq_right hji, hKij, hAij, scalarPhase_conj]
    calc
      A i j * ((K i j : ℂ) * conj (scalarPhase (A i j))) =
          (K i j : ℂ) * (A i j * conj (scalarPhase (A i j))) := by ring
      _ = (K i j : ℂ) * (‖A i j‖ : ℂ) := by rw [mul_conj_scalarPhase]
      _ = ((K i j * ‖A i j‖ : ℝ) : ℂ) := by norm_cast

theorem re_trace_mul_phaseLift {A : Matrix ι ι ℂ} {K : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hK : K.IsSymm)
    (hdiag : ∀ i, A i i = (‖A i i‖ : ℂ)) :
    (A * phaseLift A K).trace.re = ∑ i, ∑ j, K i j * ‖A i j‖ := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_phaseLift_swap hA hK hdiag]
  rfl

#print axioms phaseLift_isHermitian
#print axioms re_trace_mul_phaseLift

end

end Fidelity

end
/- END ORIGINAL SOURCE: ScalarPhase.lean -/


/- BEGIN ORIGINAL SOURCE: TriangleAlignment.lean -/
section

/-! An elementary group lemma used in the proposed three-state entropy proof.
This module alone does not formalize the entropy theorem.
-/

namespace ThreeStateFidelity

variable {G : Type*} [Group G]

/-- With at least one nonpositive edge on a triangle, all strictly positive
edges can be aligned simultaneously by vertex labels in any group. -/
theorem triangle_positive_alignment (a b c : ℝ) (u01 u02 u12 : G)
    (h : a ≤ 0 ∨ b ≤ 0 ∨ c ≤ 0) :
    ∃ v0 v1 v2 : G,
      (0 < a → v0 * v1⁻¹ = u01) ∧
      (0 < b → v0 * v2⁻¹ = u02) ∧
      (0 < c → v1 * v2⁻¹ = u12) := by
  rcases h with ha | hb | hc
  · refine ⟨1, u12 * u02⁻¹, u02⁻¹, ?_, ?_, ?_⟩
    · intro ha'; exact (not_lt_of_ge ha ha').elim
    · intro _; simp
    · intro _; simp [mul_assoc]
  · refine ⟨1, u01⁻¹, u12⁻¹ * u01⁻¹, ?_, ?_, ?_⟩
    · intro _; simp
    · intro hb'; exact (not_lt_of_ge hb hb').elim
    · intro _; simp []
  · refine ⟨1, u01⁻¹, u02⁻¹, ?_, ?_, ?_⟩
    · intro _; simp
    · intro _; simp
    · intro hc'; exact (not_lt_of_ge hc hc').elim

/-- If each edge score has a specified maximizer, then a triangle with at
least one nonpositive coefficient admits vertex labels whose signed total
score dominates the weighted sum of the individual maxima. -/
theorem triangle_signed_score_domination
    (a b c : ℝ) (s01 s02 s12 : G → ℝ) (m01 m02 m12 : ℝ)
    (u01 u02 u12 : G)
    (h01 : ∀ u, s01 u ≤ m01) (h02 : ∀ u, s02 u ≤ m02)
    (h12 : ∀ u, s12 u ≤ m12)
    (hu01 : s01 u01 = m01) (hu02 : s02 u02 = m02)
    (hu12 : s12 u12 = m12)
    (h : a ≤ 0 ∨ b ≤ 0 ∨ c ≤ 0) :
    ∃ v0 v1 v2 : G,
      a * m01 + b * m02 + c * m12 ≤
        a * s01 (v0 * v1⁻¹) + b * s02 (v0 * v2⁻¹) +
          c * s12 (v1 * v2⁻¹) := by
  obtain ⟨v0, v1, v2, ha, hb, hc⟩ :=
    triangle_positive_alignment a b c u01 u02 u12 h
  refine ⟨v0, v1, v2, ?_⟩
  have hA : a * m01 ≤ a * s01 (v0 * v1⁻¹) := by
    by_cases hp : 0 < a
    · rw [ha hp, hu01]
    · exact mul_le_mul_of_nonpos_left (h01 _) (le_of_not_gt hp)
  have hB : b * m02 ≤ b * s02 (v0 * v2⁻¹) := by
    by_cases hp : 0 < b
    · rw [hb hp, hu02]
    · exact mul_le_mul_of_nonpos_left (h02 _) (le_of_not_gt hp)
  have hC : c * m12 ≤ c * s12 (v1 * v2⁻¹) := by
    by_cases hp : 0 < c
    · rw [hc hp, hu12]
    · exact mul_le_mul_of_nonpos_left (h12 _) (le_of_not_gt hp)
  exact add_le_add (add_le_add hA hB) hC

#print axioms triangle_positive_alignment
#print axioms triangle_signed_score_domination

end ThreeStateFidelity
end
/- END ORIGINAL SOURCE: TriangleAlignment.lean -/


/- BEGIN ORIGINAL SOURCE: ScalarWitness.lean -/
section

/-! A dimension-three matrix exponential witness for the entropy argument.
This file develops the actual matrix witness, not an assumed entropy bound. -/

open scoped BigOperators Matrix
open ComplexConjugate

namespace Fidelity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Real matrices embedded into complex matrices. -/
def complexMatrix (K : Matrix ι ι ℝ) : Matrix ι ι ℂ := K.map Complex.ofReal

omit [Fintype ι] [DecidableEq ι] in
theorem complexMatrix_isHermitian [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℝ} (hK : K.IsSymm) :
    (complexMatrix K).IsHermitian := by
  ext i j
  have h : K j i = K i j := congrFun (congrFun hK i) j
  simp [complexMatrix, Matrix.conjTranspose_apply, h]

theorem exp_complexMatrix (K : Matrix ι ι ℝ) :
    NormedSpace.exp (complexMatrix K) = complexMatrix (NormedSpace.exp K) := by
  let : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℚ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  have hf : Continuous (Complex.ofRealHom.mapMatrix : Matrix ι ι ℝ → Matrix ι ι ℂ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_apply i))
  exact (NormedSpace.map_exp Complex.ofRealHom.mapMatrix hf K).symm

theorem re_trace_exp_complexMatrix (K : Matrix ι ι ℝ) :
    (NormedSpace.exp (complexMatrix K)).trace.re = (NormedSpace.exp K).trace := by
  rw [exp_complexMatrix]
  simp [complexMatrix, Matrix.trace, Matrix.diag_apply, Complex.re_sum]

/-- When all off-diagonal coefficients are nonnegative, entrywise phases attain
the desired trace objective and satisfy the exponential bound. -/
theorem exists_exp_witness_nonneg {A : Matrix ι ι ℂ} {K : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hK : K.IsSymm)
    (hdiag : ∀ i, A i i = (‖A i i‖ : ℂ))
    (hpos : ∀ i j, i ≠ j → 0 ≤ K i j) :
    ∃ H : Matrix ι ι ℂ, H.IsHermitian ∧
      (∑ i, ∑ j, K i j * ‖A i j‖) ≤ (A * H).trace.re ∧
      (NormedSpace.exp H).trace.re ≤
        (NormedSpace.exp (complexMatrix K)).trace.re := by
  refine ⟨phaseLift A K, phaseLift_isHermitian hA hK, ?_, ?_⟩
  · exact (re_trace_mul_phaseLift hA hK hdiag).ge
  · rw [re_trace_exp_complexMatrix]
    apply re_trace_exp_le_of_offdiag
    · exact phaseLift_diag A K
    · intro i j hij
      exact (norm_phaseLift_offdiag A K i j hij (hpos i j hij)).le

/-- Diagonal scalar phases as a unit of the matrix ring. -/
def phaseDiagonalUnit (v : ι → Circle) : (Matrix ι ι ℂ)ˣ where
  val := Matrix.diagonal (fun i => (v i : ℂ))
  inv := Matrix.diagonal (fun i => ((v i)⁻¹ : Circle))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Circle.coe_inv, Circle.coe_ne_zero]
    · simp [hij]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Circle.coe_inv, Circle.coe_ne_zero]
    · simp [hij]

theorem phaseDiagonalUnit_inv_eq_conjTranspose (v : ι → Circle) :
    (↑(phaseDiagonalUnit v)⁻¹ : Matrix ι ι ℂ) =
      (phaseDiagonalUnit v : Matrix ι ι ℂ)ᴴ := by
  have hinv : ∀ i, (v i : ℂ)⁻¹ = conj (v i : ℂ) :=
    fun i => Circle.coe_inv_eq_conj (v i)
  ext i j
  by_cases hij : i = j
  · subst j
    simp [phaseDiagonalUnit, Matrix.conjTranspose_apply, hinv]
  · simp [phaseDiagonalUnit, Matrix.conjTranspose_apply, hij, Ne.symm hij]

/-- Conjugation by diagonal phases. -/
def phaseGauge (K : Matrix ι ι ℝ) (v : ι → Circle) : Matrix ι ι ℂ :=
  (phaseDiagonalUnit v : Matrix ι ι ℂ) * complexMatrix K *
    (↑(phaseDiagonalUnit v)⁻¹ : Matrix ι ι ℂ)

theorem phaseGauge_apply (K : Matrix ι ι ℝ) (v : ι → Circle) (i j : ι) :
    phaseGauge K v i j = (v i : ℂ) * (K i j : ℂ) * conj (v j : ℂ) := by
  have hinv : (v j : ℂ)⁻¹ = conj (v j : ℂ) := Circle.coe_inv_eq_conj (v j)
  simp [phaseGauge, phaseDiagonalUnit, complexMatrix, Matrix.diagonal_mul,
    Matrix.mul_diagonal, hinv]

theorem phaseGauge_diag (K : Matrix ι ι ℝ) (v : ι → Circle) (i : ι) :
    phaseGauge K v i i = (K i i : ℂ) := by
  rw [phaseGauge_apply]
  calc
    (v i : ℂ) * (K i i : ℂ) * conj (v i : ℂ) =
        (K i i : ℂ) * ((v i : ℂ) * conj (v i : ℂ)) := by ring
    _ = (K i i : ℂ) := by simp [Complex.mul_conj]

theorem phaseGauge_isHermitian {K : Matrix ι ι ℝ} (hK : K.IsSymm) (v : ι → Circle) :
    (phaseGauge K v).IsHermitian := by
  rw [phaseGauge, phaseDiagonalUnit_inv_eq_conjTranspose]
  exact Matrix.isHermitian_mul_mul_conjTranspose _ (complexMatrix_isHermitian hK)

theorem trace_exp_phaseGauge (K : Matrix ι ι ℝ) (v : ι → Circle) :
    (NormedSpace.exp (phaseGauge K v)).trace =
      (NormedSpace.exp (complexMatrix K)).trace := by
  rw [phaseGauge, Matrix.exp_units_conj, Matrix.trace_mul_cycle,
    Units.inv_mul, Matrix.one_mul]

#print axioms exists_exp_witness_nonneg
#print axioms trace_exp_phaseGauge

end

end Fidelity

end
/- END ORIGINAL SOURCE: ScalarWitness.lean -/


/- BEGIN ORIGINAL SOURCE: ScalarTraceThree.lean -/
section

/-! Explicit trace formulas for three-by-three Hermitian matrices. -/

open scoped BigOperators
open ComplexConjugate

namespace Fidelity

noncomputable section

theorem re_trace_mul_three {A H : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) :
    (A * H).trace.re =
      (A 0 0 * H 0 0).re + (A 1 1 * H 1 1).re + (A 2 2 * H 2 2).re +
        2 * ((A 0 1 * conj (H 0 1)).re +
          (A 0 2 * conj (H 0 2)).re + (A 1 2 * conj (H 1 2)).re) := by
  have ha10 : A 1 0 = conj (A 0 1) := (congrFun (congrFun hA 1) 0).symm
  have ha20 : A 2 0 = conj (A 0 2) := (congrFun (congrFun hA 2) 0).symm
  have ha21 : A 2 1 = conj (A 1 2) := (congrFun (congrFun hA 2) 1).symm
  have hh10 : H 1 0 = conj (H 0 1) := (congrFun (congrFun hH 1) 0).symm
  have hh20 : H 2 0 = conj (H 0 2) := (congrFun (congrFun hH 2) 0).symm
  have hh21 : H 2 1 = conj (H 1 2) := (congrFun (congrFun hH 2) 1).symm
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_three,
    ha10, ha20, ha21, hh10, hh20, hh21, Complex.add_re,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem weighted_norm_sum_three {A : Matrix (Fin 3) (Fin 3) ℂ}
    {K : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian) (hK : K.IsSymm) :
    (∑ i, ∑ j, K i j * ‖A i j‖) =
      K 0 0 * ‖A 0 0‖ + K 1 1 * ‖A 1 1‖ + K 2 2 * ‖A 2 2‖ +
        2 * (K 0 1 * ‖A 0 1‖ + K 0 2 * ‖A 0 2‖ + K 1 2 * ‖A 1 2‖) := by
  have ha10 : A 1 0 = conj (A 0 1) := (congrFun (congrFun hA 1) 0).symm
  have ha20 : A 2 0 = conj (A 0 2) := (congrFun (congrFun hA 2) 0).symm
  have ha21 : A 2 1 = conj (A 1 2) := (congrFun (congrFun hA 2) 1).symm
  have hk10 : K 1 0 = K 0 1 := congrFun (congrFun hK 0) 1
  have hk20 : K 2 0 = K 0 2 := congrFun (congrFun hK 0) 2
  have hk21 : K 2 1 = K 1 2 := congrFun (congrFun hK 1) 2
  simp only [Fin.sum_univ_three, ha10, ha20, ha21, hk10, hk20, hk21,
    RCLike.norm_conj]
  ring

theorem re_mul_real_of_eq_norm (z : ℂ) (k : ℝ) (hz : z = (‖z‖ : ℂ)) :
    (z * (k : ℂ)).re = k * ‖z‖ := by
  have hr : z.re = ‖z‖ := congrArg Complex.re hz
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, hr, mul_comm]

#print axioms re_trace_mul_three
#print axioms weighted_norm_sum_three

end

end Fidelity

end
/- END ORIGINAL SOURCE: ScalarTraceThree.lean -/


/- BEGIN ORIGINAL SOURCE: ScalarWitnessThree.lean -/
section

/-! The actual three-by-three phase witness, combining the entrywise exponential
bound with the triangle alignment lemma. This is an intermediate theorem in the
attempt to formalize the entropy bound, not the entropy bound itself. -/

open scoped BigOperators
open ComplexConjugate

namespace Fidelity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem phaseGauge_score (z : ℂ) (K : Matrix ι ι ℝ)
    (v : ι → Circle) (i j : ι) :
    (z * conj (phaseGauge K v i j)).re =
      K i j * (z * conj ((v i * (v j)⁻¹ : Circle) : ℂ)).re := by
  have hinv : (v j : ℂ)⁻¹ = conj (v j : ℂ) := Circle.coe_inv_eq_conj (v j)
  simp only [phaseGauge_apply, Circle.coe_mul, Circle.coe_inv, hinv,
    map_mul, Complex.conj_ofReal, Complex.conj_conj, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem re_trace_mul_phaseGauge_three {A : Matrix (Fin 3) (Fin 3) ℂ}
    {K : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian) (hK : K.IsSymm)
    (hdiag : ∀ i, A i i = (‖A i i‖ : ℂ)) (v : Fin 3 → Circle) :
    (A * phaseGauge K v).trace.re =
      K 0 0 * ‖A 0 0‖ + K 1 1 * ‖A 1 1‖ + K 2 2 * ‖A 2 2‖ +
      2 * (K 0 1 * (A 0 1 * conj ((v 0 * (v 1)⁻¹ : Circle) : ℂ)).re +
        K 0 2 * (A 0 2 * conj ((v 0 * (v 2)⁻¹ : Circle) : ℂ)).re +
        K 1 2 * (A 1 2 * conj ((v 1 * (v 2)⁻¹ : Circle) : ℂ)).re) := by
  rw [re_trace_mul_three hA (phaseGauge_isHermitian hK v)]
  simp only [phaseGauge_diag, phaseGauge_score,
    re_mul_real_of_eq_norm (A 0 0) (K 0 0) (hdiag 0),
    re_mul_real_of_eq_norm (A 1 1) (K 1 1) (hdiag 1),
    re_mul_real_of_eq_norm (A 2 2) (K 2 2) (hdiag 2)]

/-- A nonpositive edge leaves a forest of positive edges, which can all be
aligned by diagonal scalar phases. -/
theorem exists_exp_witness_forest {A : Matrix (Fin 3) (Fin 3) ℂ}
    {K : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian) (hK : K.IsSymm)
    (hdiag : ∀ i, A i i = (‖A i i‖ : ℂ))
    (hn : K 0 1 ≤ 0 ∨ K 0 2 ≤ 0 ∨ K 1 2 ≤ 0) :
    ∃ H : Matrix (Fin 3) (Fin 3) ℂ, H.IsHermitian ∧
      (∑ i, ∑ j, K i j * ‖A i j‖) ≤ (A * H).trace.re ∧
      (NormedSpace.exp H).trace.re ≤
        (NormedSpace.exp (complexMatrix K)).trace.re := by
  obtain ⟨v0, v1, v2, hv⟩ :=
    ThreeStateFidelity.triangle_signed_score_domination
      (K 0 1) (K 0 2) (K 1 2)
      (fun u : Circle => (A 0 1 * conj (u : ℂ)).re)
      (fun u : Circle => (A 0 2 * conj (u : ℂ)).re)
      (fun u : Circle => (A 1 2 * conj (u : ℂ)).re)
      ‖A 0 1‖ ‖A 0 2‖ ‖A 1 2‖
      (phaseCircle (A 0 1)) (phaseCircle (A 0 2)) (phaseCircle (A 1 2))
      (phase_score_le (A 0 1)) (phase_score_le (A 0 2)) (phase_score_le (A 1 2))
      (phase_score_max (A 0 1)) (phase_score_max (A 0 2)) (phase_score_max (A 1 2)) hn
  let v : Fin 3 → Circle := ![v0, v1, v2]
  refine ⟨phaseGauge K v, phaseGauge_isHermitian hK v, ?_, ?_⟩
  · rw [weighted_norm_sum_three hA hK, re_trace_mul_phaseGauge_three hA hK hdiag]
    have hm := mul_le_mul_of_nonneg_left hv (show (0 : ℝ) ≤ 2 by norm_num)
    have hh := add_le_add_left hm
      (K 0 0 * ‖A 0 0‖ + K 1 1 * ‖A 1 1‖ + K 2 2 * ‖A 2 2‖)
    simpa [v] using hh
  · exact le_of_eq (congrArg Complex.re (trace_exp_phaseGauge K v))

/-- For any real symmetric three-by-three test matrix there is an actual
Hermitian phase witness with the required trace objective and exponential bound. -/
theorem exists_exp_witness_three {A : Matrix (Fin 3) (Fin 3) ℂ}
    {K : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian) (hK : K.IsSymm)
    (hdiag : ∀ i, A i i = (‖A i i‖ : ℂ)) :
    ∃ H : Matrix (Fin 3) (Fin 3) ℂ, H.IsHermitian ∧
      (∑ i, ∑ j, K i j * ‖A i j‖) ≤ (A * H).trace.re ∧
      (NormedSpace.exp H).trace.re ≤
        (NormedSpace.exp (complexMatrix K)).trace.re := by
  classical
  by_cases hp : 0 ≤ K 0 1 ∧ 0 ≤ K 0 2 ∧ 0 ≤ K 1 2
  · apply exists_exp_witness_nonneg hA hK hdiag
    have hk10 : K 1 0 = K 0 1 := congrFun (congrFun hK 0) 1
    have hk20 : K 2 0 = K 0 2 := congrFun (congrFun hK 0) 2
    have hk21 : K 2 1 = K 1 2 := congrFun (congrFun hK 1) 2
    rcases hp with ⟨hp01, hp02, hp12⟩
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hp01
    · exact hp02
    · exact hk10.symm ▸ hp01
    · exact (hij rfl).elim
    · exact hp12
    · exact hk20.symm ▸ hp02
    · exact hk21.symm ▸ hp12
    · exact (hij rfl).elim
  · apply exists_exp_witness_forest hA hK hdiag
    by_cases h01 : 0 ≤ K 0 1
    · by_cases h02 : 0 ≤ K 0 2
      · right; right
        exact le_of_lt (lt_of_not_ge (fun h12 => hp ⟨h01, h02, h12⟩))
      · right; left
        exact le_of_lt (lt_of_not_ge h02)
    · left
      exact le_of_lt (lt_of_not_ge h01)

#print axioms exists_exp_witness_three

end

end Fidelity

end
/- END ORIGINAL SOURCE: ScalarWitnessThree.lean -/


/- BEGIN ORIGINAL SOURCE: ScalarEntropyBridge.lean -/
section

/-! Bridge to spectral matrix entropy. -/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Matrix

namespace Fidelity

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The unnormalized entropy variational inequality, for actual matrix entropy. -/
theorem entropy_le_exp_trace_sub {A H : Matrix n n ℂ}
    (hA : A.PosDef) (hH : H.IsHermitian) :
    vonNeumannEntropy A hA.isHermitian ≤
      (NormedSpace.exp H).trace.re - A.trace.re - (A * H).trace.re := by
  have h := re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_le hA
    (1 : Matrix n n ℂ) hH
  have hrel : quantumRelativeEntropy A (1 : Matrix n n ℂ) =
      -vonNeumannEntropy A hA.isHermitian := by
    rw [quantumRelativeEntropy_eq_neg_entropy_sub_trace_mul_log hA.isHermitian]
    simp
  rw [hrel, CFC.log_one, add_zero] at h
  linarith

omit [Fintype n] [DecidableEq n] in
/-- Entrywise absolute values of a Hermitian matrix are symmetric. -/
theorem entryAbs_transpose [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (entryAbs A)ᵀ = entryAbs A := by
  ext i j
  change (‖A j i‖ : ℂ) = (‖A i j‖ : ℂ)
  rw [← hA.apply i j, norm_star]

/-- The logarithm of the real symmetric absolute-entry matrix is real symmetric. -/
theorem exists_real_symmetric_log_entryAbs {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    ∃ K : Matrix n n ℝ, K.IsSymm ∧ complexMatrix K = CFC.log (entryAbs A) := by
  let L := CFC.log (entryAbs A)
  have hLH : L.IsHermitian := IsSelfAdjoint.log.isHermitian
  have hLT : Lᵀ = L := by
    dsimp only [L]
    rw [← (entryAbs_isHermitian hA).log_transpose, entryAbs_transpose hA]
  let K : Matrix n n ℝ := fun i j => (L i j).re
  refine ⟨K, ?_, ?_⟩
  · ext i j
    exact congrArg Complex.re (congrFun (congrFun hLT i) j)
  · ext i j
    have hs : star (L i j) = L i j :=
      (hLH.apply j i).trans (congrFun (congrFun hLT i) j)
    apply Complex.ext
    · rfl
    · have hi := congrArg Complex.im hs
      simp only [Complex.star_def, Complex.conj_im] at hi
      change 0 = (L i j).im
      linarith

omit [DecidableEq n] in
theorem re_trace_entryAbs_mul_complexMatrix [DecidableEq n] (A : Matrix n n ℂ)
    {K : Matrix n n ℝ} (hK : K.IsSymm) :
    (entryAbs A * complexMatrix K).trace.re =
      ∑ i, ∑ j, K i j * ‖A i j‖ := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum,
    entryAbs, complexMatrix, Matrix.map_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij : K j i = K i j := congrFun (congrFun hK i) j
  rw [hij, mul_comm]

theorem entryAbs_trace {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (entryAbs A).trace = A.trace := by
  apply Finset.sum_congr rfl
  intro i _
  exact entryAbs_diag hA i

/-- The actual entropy inequality for the entrywise absolute value of a
positive definite three-by-three complex matrix. This is the known scalar
ingredient, not a claim of a new research result. -/
theorem entropy_entryAbs_three_posDef {A : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : A.PosDef) :
    vonNeumannEntropy A hA.isHermitian ≤
      vonNeumannEntropy (entryAbs A) (entryAbs_isHermitian hA.isHermitian) := by
  have hB := entryAbs_posDef_three hA
  obtain ⟨K, hK, hlog⟩ := exists_real_symmetric_log_entryAbs hA.isHermitian
  obtain ⟨H, hH, hobj, hpart⟩ := exists_exp_witness_three hA.isHermitian hK
    (fun i => (entryAbs_diag hA.posSemidef i).symm)
  have hobjective :
      -vonNeumannEntropy (entryAbs A) (entryAbs_isHermitian hA.isHermitian) ≤
        (A * H).trace.re := by
    rw [vonNeumannEntropy_eq_neg_trace_mul_log, neg_neg, ← hlog,
      re_trace_entryAbs_mul_complexMatrix _ hK]
    exact hobj
  have hpartition : (NormedSpace.exp (complexMatrix K)).trace.re = A.trace.re := by
    rw [hlog, CFC.exp_log _ hB.isStrictlyPositive, entryAbs_trace hA.posSemidef]
  rw [hpartition] at hpart
  have hgibbs := entropy_le_exp_trace_sub hA hH
  linarith

#print axioms entropy_entryAbs_three_posDef

end
end Fidelity
end
/- END ORIGINAL SOURCE: ScalarEntropyBridge.lean -/


/- BEGIN ORIGINAL SOURCE: DiagonalEntropy.lean -/
section

/-! Identities relating diagonal pinching to quantum relative
entropy. -/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Matrix

namespace Fidelity

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

def diagPinch (A : Matrix n n ℂ) : Matrix n n ℂ := Matrix.diagonal (Matrix.diag A)

omit [Fintype n] in
theorem diagPinch_isHermitian [Fintype n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (diagPinch A).IsHermitian := by
  exact Matrix.isHermitian_diagonal_of_self_adjoint _
    (funext fun i => hA.apply i i)

omit [Fintype n] in
theorem diagPinch_eq_real [Fintype n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    diagPinch A = Matrix.diagonal (fun i => ((A i i).re : ℂ)) := by
  unfold diagPinch
  apply congrArg Matrix.diagonal
  funext i
  exact (hA.coe_re_apply_self i).symm

theorem log_diagPinch {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    CFC.log (diagPinch A) =
      Matrix.diagonal (fun i => (Real.log (A i i).re : ℂ)) := by
  rw [diagPinch_eq_real hA, CFC.log]
  exact Matrix.cfc_diagonal _ _ (Set.finite_range _ |>.continuousOn _)

theorem trace_mul_log_diagPinch {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A * CFC.log (diagPinch A)).trace =
      (diagPinch A * CFC.log (diagPinch A)).trace := by
  rw [log_diagPinch hA]
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, diagPinch]

theorem relativeEntropy_diagPinch_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    quantumRelativeEntropy A (diagPinch A) =
      vonNeumannEntropy (diagPinch A) (diagPinch_isHermitian hA) -
        vonNeumannEntropy A hA := by
  rw [quantumRelativeEntropy_eq_neg_entropy_sub_trace_mul_log hA,
    vonNeumannEntropy_eq_neg_trace_mul_log (diagPinch_isHermitian hA),
    trace_mul_log_diagPinch hA]
  ring

omit [Fintype n] in
theorem diagPinch_posDef [Fintype n] {A : Matrix n n ℂ} (hA : A.PosDef) :
    (diagPinch A).PosDef := Matrix.PosDef.diagonal fun _ => hA.diag_pos

theorem diagPinch_entryAbs {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    diagPinch (entryAbs A) = diagPinch A := by
  unfold diagPinch
  apply congrArg Matrix.diagonal
  funext i
  exact entryAbs_diag hA i

omit [Fintype n] in
theorem diagPinch_sum [Fintype n] {r : Type*} [Fintype r] (A : r → Matrix n n ℂ) :
    diagPinch (∑ k, A k) = ∑ k, diagPinch (A k) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [diagPinch, Matrix.diag_apply, Matrix.sum_apply]
  · simp [diagPinch, Matrix.sum_apply, h]

/-- The scalar entropy lemma in precisely the relative-entropy form used
inside the Li--Zhang decomposition. -/
theorem relativeEntropy_entryAbs_three_posDef {A : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : A.PosDef) :
    quantumRelativeEntropy (entryAbs A) (diagPinch (entryAbs A)) ≤
      quantumRelativeEntropy A (diagPinch A) := by
  rw [relativeEntropy_diagPinch_eq (entryAbs_isHermitian hA.isHermitian),
    relativeEntropy_diagPinch_eq hA.isHermitian]
  have hdiag := diagPinch_entryAbs hA.posSemidef
  have he := vonNeumannEntropy_congr hdiag
    (diagPinch_isHermitian (entryAbs_isHermitian hA.isHermitian))
    (diagPinch_isHermitian hA.isHermitian)
  have h := entropy_entryAbs_three_posDef hA
  linarith

#print axioms relativeEntropy_entryAbs_three_posDef

end
end Fidelity
end
/- END ORIGINAL SOURCE: DiagonalEntropy.lean -/


/- BEGIN ORIGINAL SOURCE: FiniteIndexRelativeEntropy.lean -/
section
/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: Sirui Lu
-/

/-!
# Prior foundation: joint convexity on arbitrary finite indices

The following four declarations are extracted from QICLean's
`QICLean/Channel/Schwarz/RelativeEntropyDataProcessing.lean` at commit
`acda92aa70e69b37507e422bceb5414036859fe6` (LionSR/QICLean).
Only the namespace and imports are adjusted, to avoid compiling unrelated
partial-trace and singular-support applications. Their proofs are unchanged.
This adapter is prior work and is not claimed as a research contribution.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix

namespace Fidelity.QICFiniteIndex

open TNLean.RelativeEntropyConvexity

open Matrix

variable {N : Type*} [Fintype N] [DecidableEq N]

omit [DecidableEq N] in
/-- Positive definiteness is preserved and reflected by reindexing with a
bijection to the canonical finite index. -/
theorem posDef_submatrix_equiv_iff (e : N ≃ Fin (Fintype.card N))
    (A : Matrix N N ℂ) :
    (A.submatrix e.symm e.symm).PosDef ↔ A.PosDef := by
  constructor
  · intro h
    have hsub := h.submatrix (e := (e : N → Fin (Fintype.card N))) e.injective
    rwa [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at hsub
  · intro h; exact h.submatrix e.symm.injective

/-- The set of positive definite matrices on an arbitrary finite index, the
faithful domain of the quantum relative entropy. -/
def posDefSetN (N : Type*) [Fintype N] [DecidableEq N] : Set (Matrix N N ℂ) :=
  {A : Matrix N N ℂ | A.PosDef}

/-- **Joint convexity of the quantum relative entropy on an arbitrary finite
index.** The map $(\rho, \sigma) \mapsto D(\rho \,\|\, \sigma)$ is jointly convex
on pairs of positive definite matrices over any finite index. It is transported
from `convexOn_quantumRelativeEntropy` through the componentwise reindexing to the
canonical finite index, which is an affine map preserving the positive definite
product domain and the relative entropy. -/
theorem convexOn_quantumRelativeEntropy_index :
    ConvexOn ℝ (posDefSetN N ×ˢ posDefSetN N)
      (fun p : Matrix N N ℂ × Matrix N N ℂ => quantumRelativeEntropy p.1 p.2) := by
  set D := Fintype.card N
  set e : N ≃ Fin D := Fintype.equivFin N
  set Φ :
      (Matrix N N ℂ × Matrix N N ℂ) →ₗ[ℝ]
        (Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.reindexLinearEquiv ℝ ℂ e e : Matrix N N ℂ →ₗ[ℝ] Matrix (Fin D) (Fin D) ℂ).prodMap
      (Matrix.reindexLinearEquiv ℝ ℂ e e : Matrix N N ℂ →ₗ[ℝ] Matrix (Fin D) (Fin D) ℂ) with hΦ
  have hΦ_apply : ∀ p : Matrix N N ℂ × Matrix N N ℂ,
      Φ p = (p.1.submatrix e.symm e.symm, p.2.submatrix e.symm e.symm) := fun p => rfl
  have hcomp := (convexOn_quantumRelativeEntropy (D := D)).comp_affineMap Φ.toAffineMap
  have hpre : (Φ.toAffineMap) ⁻¹' (posDefSet (D := D) ×ˢ posDefSet (D := D))
      = posDefSetN N ×ˢ posDefSetN N := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, LinearMap.coe_toAffineMap, hΦ_apply, posDefSet,
      posDefSetN, Set.mem_ofPred_eq]
    rw [posDef_submatrix_equiv_iff e, posDef_submatrix_equiv_iff e]
  rw [hpre] at hcomp
  refine hcomp.congr ?_
  intro p hp
  obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
  simp only [Function.comp_apply, LinearMap.coe_toAffineMap, hΦ_apply]
  exact quantumRelativeEntropy_submatrix_equiv (m := N) hp1.isHermitian hp2.isHermitian e

/-- Conjugation by a unitary preserves positive definiteness. -/
theorem posDef_conj_unitary {ρ : Matrix N N ℂ} (hρ : ρ.PosDef)
    (U : unitary (Matrix N N ℂ)) :
    ((U : Matrix N N ℂ) * ρ * star (U : Matrix N N ℂ)).PosDef := by
  have hU : IsUnit (U : Matrix N N ℂ) := ⟨Unitary.toUnits U, rfl⟩
  have hinj : Function.Injective (U : Matrix N N ℂ).vecMul :=
    Matrix.vecMul_injective_iff_isUnit.mpr hU
  have hpd := hρ.mul_mul_conjTranspose_same hinj
  rwa [star_eq_conjTranspose]

end Fidelity.QICFiniteIndex

#print axioms Fidelity.QICFiniteIndex.convexOn_quantumRelativeEntropy_index
end
/- END ORIGINAL SOURCE: FiniteIndexRelativeEntropy.lean -/


/- BEGIN ORIGINAL SOURCE: Twirl.lean -/
section

/-!
# Finite unitary averaging for the three-state fidelity argument

These lemmas concern actual finite complex matrices and the trace-log quantum
relative entropy.  No analytic inequality is postulated as a hypothesis.
The only analytic input is the proved joint convexity and unitary invariance
of relative entropy from QICLean.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker

namespace Fidelity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Joint unitary averaging cannot increase relative entropy. -/
theorem relativeEntropy_unitaryAverage_le {κ : Type*} [Fintype κ]
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (U : κ → unitary (Matrix n n ℂ)) (w : κ → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hwsum : ∑ k, w k = 1) :
    quantumRelativeEntropy
      (∑ k, w k • ((U k : Matrix n n ℂ) * A * star (U k : Matrix n n ℂ)))
      (∑ k, w k • ((U k : Matrix n n ℂ) * B * star (U k : Matrix n n ℂ)))
      ≤ quantumRelativeEntropy A B := by
  let P : κ → Matrix n n ℂ × Matrix n n ℂ := fun k =>
    ((U k : Matrix n n ℂ) * A * star (U k : Matrix n n ℂ),
      (U k : Matrix n n ℂ) * B * star (U k : Matrix n n ℂ))
  have hmem : ∀ k, P k ∈
      Fidelity.QICFiniteIndex.posDefSetN n ×ˢ
        Fidelity.QICFiniteIndex.posDefSetN n := fun k =>
    ⟨Fidelity.QICFiniteIndex.posDef_conj_unitary hA (U k), Fidelity.QICFiniteIndex.posDef_conj_unitary hB (U k)⟩
  have hj := (Fidelity.QICFiniteIndex.convexOn_quantumRelativeEntropy_index
    (N := n)).map_sum_le (t := Finset.univ) (w := w)
    (fun k _ => hw k) hwsum (fun k _ => hmem k)
  have hterm : ∀ k, quantumRelativeEntropy (P k).1 (P k).2 =
      quantumRelativeEntropy A B := fun k =>
    quantumRelativeEntropy_conj_unitary hA.isHermitian hB.isHermitian (U k)
  simp only [hterm, smul_eq_mul, ← Finset.sum_mul, hwsum, one_mul] at hj
  simpa only [P, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd] using hj

/-- The uniform finite unitary average is a relative-entropy contraction. -/
theorem relativeEntropy_uniformUnitaryAverage_le {κ : Type*}
    [Fintype κ] [Nonempty κ]
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (U : κ → unitary (Matrix n n ℂ)) :
    quantumRelativeEntropy
      ((Fintype.card κ : ℝ)⁻¹ •
        ∑ k, (U k : Matrix n n ℂ) * A * star (U k : Matrix n n ℂ))
      ((Fintype.card κ : ℝ)⁻¹ •
        ∑ k, (U k : Matrix n n ℂ) * B * star (U k : Matrix n n ℂ))
      ≤ quantumRelativeEntropy A B := by
  have hc : 0 < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hw : ∑ _k : κ, (Fintype.card κ : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hc.ne'
  simpa only [← Finset.smul_sum] using
    relativeEntropy_unitaryAverage_le hA hB U
      (fun _ => (Fintype.card κ : ℝ)⁻¹) (fun _ => (inv_pos.mpr hc).le) hw

/-- Joint convexity in its homogeneous finite-sum form. -/
theorem relativeEntropy_sum_le_sum {κ : Type*} [Fintype κ] [Nonempty κ]
    (A B : κ → Matrix n n ℂ)
    (hA : ∀ k, (A k).PosDef) (hB : ∀ k, (B k).PosDef) :
    quantumRelativeEntropy (∑ k, A k) (∑ k, B k) ≤
      ∑ k, quantumRelativeEntropy (A k) (B k) := by
  have hc : 0 < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
  let c : ℝ := (Fintype.card κ : ℝ)⁻¹
  have hcp : 0 < c := inv_pos.mpr hc
  have hw : ∑ _k : κ, c = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, c]
    exact mul_inv_cancel₀ hc.ne'
  have hj := (Fidelity.QICFiniteIndex.convexOn_quantumRelativeEntropy_index
    (N := n)).map_sum_le (t := Finset.univ) (w := fun _ : κ => c)
    (p := fun k => (A k, B k)) (fun _ _ => hcp.le) hw
    (fun k _ => ⟨hA k, hB k⟩)
  have hsumA : (∑ k, A k).PosDef := Matrix.posDef_sum Finset.univ_nonempty fun k _ => hA k
  have hsumB : (∑ k, B k).PosDef := Matrix.posDef_sum Finset.univ_nonempty fun k _ => hB k
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
    ← Finset.smul_sum] at hj
  rw [Matrix.quantumRelativeEntropy_smul_posDef hsumA hsumB hcp] at hj
  simp only [smul_eq_mul] at hj
  exact le_of_mul_le_mul_left hj hcp

section InternalPinching

variable {S : Type*} [Fintype S] [DecidableEq S] {d : ℕ} [NeZero d]

/-- Delete entries connecting different values of the internal coordinate. -/
def internalPinch (A : Matrix (S × ZMod d) (S × ZMod d) ℂ) :
    Matrix (S × ZMod d) (S × ZMod d) ℂ :=
  fun x y => if x.2 = y.2 then A x y else 0

/-- Lift an internal clock phase to the full product space. -/
noncomputable def clockLift {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d) (b : ZMod d) :
    unitary (Matrix (S × ZMod d) (S × ZMod d) ℂ) :=
  ⟨(1 : Matrix S S ℂ) ⊗ₖ (Matrix.weylClock (d := d) ζ ^ b.val),
    Matrix.kronecker_mem_unitary (Submonoid.one_mem _)
      (pow_mem (Matrix.weylClock_mem_unitary hζ) b.val)⟩

/-- Clock averaging is exactly internal pinching. -/
theorem internalPinch_eq_clockAverage {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (A : Matrix (S × ZMod d) (S × ZMod d) ℂ) :
    (d : ℝ)⁻¹ • ∑ b : ZMod d,
      (clockLift (S := S) hζ b : Matrix (S × ZMod d) (S × ZMod d) ℂ) * A *
        star (clockLift (S := S) hζ b : Matrix (S × ZMod d) (S × ZMod d) ℂ)
      = internalPinch A := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  ext ⟨i, r⟩ ⟨j, s⟩
  simp only [Matrix.smul_apply, Matrix.sum_apply, clockLift,
    Matrix.star_eq_conjTranspose, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast]
  have hblock (b : ZMod d) :=
    Matrix.kronecker_one_weyl_conj_block (ζ := ζ) (0 : ZMod d) b A i j r s
  simp only [Matrix.weyl, ZMod.val_zero, pow_zero, Matrix.one_mul] at hblock
  simp_rw [hblock]
  have ht := congrArg (fun M : Matrix (ZMod d) (ZMod d) ℂ => M r s)
    (Matrix.sum_weylClock_pow_conj hζ
      (A.submatrix (fun k => (i, k)) (fun k => (j, k))))
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at ht
  rw [ht]
  by_cases hrs : r = s
  · subst s
    simp [internalPinch, Matrix.submatrix_apply, hd]
  · simp [internalPinch, hrs]

/-- Pinching the same internal coordinate in both arguments contracts relative entropy. -/
theorem relativeEntropy_internalPinch_le
    {A B : Matrix (S × ZMod d) (S × ZMod d) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    quantumRelativeEntropy (internalPinch A) (internalPinch B) ≤
      quantumRelativeEntropy A B := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ d :=
    ⟨_, Complex.isPrimitiveRoot_exp d (NeZero.ne d)⟩
  have h := relativeEntropy_uniformUnitaryAverage_le hA hB (clockLift (S := S) hζ)
  rw [ZMod.card, internalPinch_eq_clockAverage hζ A,
    internalPinch_eq_clockAverage hζ B] at h
  exact h

end InternalPinching

#print axioms relativeEntropy_unitaryAverage_le
#print axioms relativeEntropy_sum_le_sum
#print axioms relativeEntropy_internalPinch_le

end Fidelity
end
/- END ORIGINAL SOURCE: Twirl.lean -/


/- BEGIN ORIGINAL SOURCE: SlicePinching.lean -/
section

/-! Coordinate bridge for relative-entropy contraction.
No analytic premise replaces the contraction theorem. -/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Matrix

namespace Fidelity

noncomputable section

variable {n s : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype s] [DecidableEq s]

/-- Pinch the inner coordinate and then identify the result with the direct
sum of its scalar slices. This is the data-processing step actually needed. -/
theorem relativeEntropy_scalarSlices_le
    {A B : Matrix (n × s) (n × s) ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    (∑ r, quantumRelativeEntropy (scalarSlice A r) (scalarSlice B r)) ≤
      quantumRelativeEntropy A B := by
  classical
  let : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
  let e : n ≃ ZMod (Fintype.card n) := Fintype.equivOfCardEq (by rw [ZMod.card])
  let f : (s × ZMod (Fintype.card n)) ≃ (n × s) :=
    (Equiv.prodCongr (Equiv.refl s) e.symm).trans (Equiv.prodComm s n)
  have hAp : (A.submatrix f f).PosDef := hA.submatrix f.injective
  have hBp : (B.submatrix f f).PosDef := hB.submatrix f.injective
  have hpinch (G : Matrix (n × s) (n × s) ℂ) :
      internalPinch (G.submatrix f f) =
        Matrix.blockDiagonal (fun r => scalarSlice G (e.symm r)) := by
    ext ⟨i, r⟩ ⟨j, t⟩
    by_cases h : r = t
    · subst t
      simp [internalPinch, Matrix.blockDiagonal_apply, scalarSlice, f]
    · simp [internalPinch, Matrix.blockDiagonal_apply, scalarSlice, h]
  have hsliceA (r : ZMod (Fintype.card n)) :
      (scalarSlice A (e.symm r)).IsHermitian :=
    hA.isHermitian.submatrix (fun i => (e.symm r, i))
  have hsliceB (r : ZMod (Fintype.card n)) :
      (scalarSlice B (e.symm r)).IsHermitian :=
    hB.isHermitian.submatrix (fun i => (e.symm r, i))
  have h := relativeEntropy_internalPinch_le hAp hBp
  rw [hpinch A, hpinch B, relativeEntropy_blockDiagonal _ _ hsliceA hsliceB] at h
  have hreindex : quantumRelativeEntropy (A.submatrix f f) (B.submatrix f f) =
      quantumRelativeEntropy A B := by
    simpa only [Equiv.symm_symm] using
      (Matrix.quantumRelativeEntropy_submatrix_equiv hA.isHermitian hB.isHermitian f.symm)
  rw [hreindex] at h
  have hsum := Equiv.sum_comp e.symm
    (fun r => quantumRelativeEntropy (scalarSlice A r) (scalarSlice B r))
  rw [hsum] at h
  exact h

#print axioms relativeEntropy_scalarSlices_le

end
end Fidelity
end
/- END ORIGINAL SOURCE: SlicePinching.lean -/


/- BEGIN ORIGINAL SOURCE: BlockCoherence.lean -/
section

/-! Entropy-compression theorem for positive definite matrices.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Matrix

namespace Fidelity

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The central relative-entropy inequality for the three-block trace-norm
compression, for positive definite matrices. -/
theorem relativeEntropy_normCompression3_posDef
    {G : Matrix (n × Fin 3) (n × Fin 3) ℂ} (hG : G.PosDef) :
    quantumRelativeEntropy (normCompression3 G) (diagPinch (normCompression3 G)) ≤
      quantumRelativeEntropy G (blockPinch G) := by
  obtain ⟨U, hpos, hsum⟩ := exists_li_zhang_decomposition_posDef hG
  let D := Matrix.blockDiagonal fun i => (U i : Matrix n n ℂ)
  let G' := D * G * Dᴴ
  let A := scalarSlice G'
  have hG' : G'.PosDef := blockDiagonal_conjugate_posDef hG U
  have hA (r : n) : (A r).PosDef := hpos r
  have hB (r : n) : (entryAbs (A r)).PosDef := entryAbs_posDef_three (hA r)
  have hsum' : normCompression3 G = ∑ r, entryAbs (A r) := hsum
  have hconv := relativeEntropy_sum_le_sum
    (fun r => entryAbs (A r)) (fun r => diagPinch (entryAbs (A r)))
    hB (fun r => diagPinch_posDef (hB r))
  have hfirst :
      quantumRelativeEntropy (normCompression3 G) (diagPinch (normCompression3 G)) ≤
        ∑ r, quantumRelativeEntropy (entryAbs (A r)) (diagPinch (entryAbs (A r))) := by
    simpa only [← diagPinch_sum, ← hsum'] using hconv
  have hscalar :
      (∑ r, quantumRelativeEntropy (entryAbs (A r)) (diagPinch (entryAbs (A r)))) ≤
        ∑ r, quantumRelativeEntropy (A r) (diagPinch (A r)) := by
    exact Finset.sum_le_sum fun r _ => relativeEntropy_entryAbs_three_posDef (hA r)
  have hpinch := relativeEntropy_scalarSlices_le hG' (blockPinch_posDef hG')
  have hslice (r : n) : scalarSlice (blockPinch G') r = diagPinch (A r) :=
    scalarSlice_blockPinch G' r
  simp_rw [hslice] at hpinch
  let DU : Matrix.unitaryGroup (n × Fin 3) ℂ :=
    ⟨D, blockDiagonal_mem_unitary U⟩
  have hinv : quantumRelativeEntropy G' (blockPinch G') =
      quantumRelativeEntropy G (blockPinch G) := by
    change quantumRelativeEntropy (D * G * Dᴴ) (blockPinch (D * G * Dᴴ)) = _
    rw [blockPinch_blockDiagonal_conjugate]
    exact quantumRelativeEntropy_conj_unitary hG.isHermitian
      (blockPinch_isHermitian hG.isHermitian) DU
  rw [hinv] at hpinch
  exact hfirst.trans (hscalar.trans hpinch)

/-- The corresponding entropy-loss comparison, still before the boundary
extension to singular matrices. -/
theorem blockCoherence_normCompression3_posDef
    {G : Matrix (n × Fin 3) (n × Fin 3) ℂ} (hG : G.PosDef) :
    vonNeumannEntropy (diagPinch (normCompression3 G))
        (diagPinch_isHermitian (normCompression3_posDef hG).isHermitian) -
      vonNeumannEntropy (normCompression3 G) (normCompression3_posDef hG).isHermitian ≤
    vonNeumannEntropy (blockPinch G) (blockPinch_isHermitian hG.isHermitian) -
      vonNeumannEntropy G hG.isHermitian := by
  rw [← relativeEntropy_diagPinch_eq, ← relativeEntropy_blockPinch_eq]
  exact relativeEntropy_normCompression3_posDef hG

#print axioms relativeEntropy_normCompression3_posDef
#print axioms blockCoherence_normCompression3_posDef

end
end Fidelity
end
/- END ORIGINAL SOURCE: BlockCoherence.lean -/


/- BEGIN ORIGINAL SOURCE: CompressionRegularization.lean -/
section

open scoped Matrix ComplexOrder
open Matrix

namespace Fidelity

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem normCompression3_diag
    {G : Matrix (n × Fin 3) (n × Fin 3) ℂ} (hG : G.PosSemidef) (i : Fin 3) :
    normCompression3 G i i = (matrixBlock G i i).trace :=
  nuclear_posSemidef_complex (hG.submatrix (fun r => (r, i)))

theorem trace_normCompression3
    {G : Matrix (n × Fin 3) (n × Fin 3) ℂ} (hG : G.PosSemidef) :
    (normCompression3 G).trace = G.trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  simp_rw [normCompression3_diag hG]
  simp only [Matrix.trace, Matrix.diag_apply, matrixBlock, Matrix.submatrix_apply,
    ← Finset.univ_product_univ, Finset.sum_product]
  exact Finset.sum_comm

omit [Fintype n] in
theorem matrixBlock_add_smul_one [Fintype n] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix (n × ι) (n × ι) ℂ) (t : ℝ) (i j : ι) :
    matrixBlock (G + t • (1 : Matrix (n × ι) (n × ι) ℂ)) i j =
      if i = j then matrixBlock G i j + t • (1 : Matrix n n ℂ)
      else matrixBlock G i j := by
  ext r s
  by_cases hij : i = j <;>
    simp [matrixBlock, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Prod.mk.injEq, hij]

/-- The nuclear-norm compression has the expected affine form under
positive identity regularization of a positive block matrix. -/
theorem normCompression3_add_smul_one
    {G : Matrix (n × Fin 3) (n × Fin 3) ℂ} (hG : G.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) :
    normCompression3 (G + t • (1 : Matrix (n × Fin 3) (n × Fin 3) ℂ)) =
      normCompression3 G + ((Fintype.card n : ℝ) * t) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  change (nuclear (matrixBlock (G + t • (1 : Matrix (n × Fin 3) (n × Fin 3) ℂ)) i j) : ℂ) =
    (nuclear (matrixBlock G i j) : ℂ) +
      ((Fintype.card n : ℝ) * t) • (1 : Matrix (Fin 3) (Fin 3) ℂ) i j
  rw [matrixBlock_add_smul_one]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    have hGi : (matrixBlock G i i).PosSemidef := hG.submatrix (fun r => (r, i))
    simpa [Matrix.one_apply, Complex.real_smul] using
      congrArg (fun x : ℝ => (x : ℂ)) (nuclear_add_smul_one hGi t ht)
  · simp [hij]

theorem normCompression3_smul_nonneg
    (G : Matrix (n × Fin 3) (n × Fin 3) ℂ) (t : ℝ) (ht : 0 ≤ t) :
    normCompression3 (t • G) = t • normCompression3 G := by
  ext i j
  change (nuclear (t • matrixBlock G i j) : ℂ) = t • (nuclear (matrixBlock G i j) : ℂ)
  rw [nuclear_smul_nonneg _ t ht]
  simp [Complex.real_smul]

end Fidelity
end
/- END ORIGINAL SOURCE: CompressionRegularization.lean -/


/- BEGIN ORIGINAL SOURCE: EntropyContinuityGeneral.lean -/
section

/-! Unnormalized entropy continuity. Unlike the normalized interval
corollary in QICLean, this uses continuity of the totalized scalar negMulLog
on all of R. No compactness or density normalization is silently assumed.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Matrix Filter Topology

namespace Fidelity

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem continuous_vonNeumannEntropy_family {X : Type*} [TopologicalSpace X]
    {A : X → Matrix n n ℂ} (hA : ∀ x, (A x).IsHermitian)
    (hc : Continuous A) :
    Continuous (fun x => vonNeumannEntropy (A x) (hA x)) := by
  simp_rw [Matrix.vonNeumannEntropy_eq_re_trace_cfc]
  have hfc : Continuous (fun x => cfc Real.negMulLog (A x)) :=
    hc.cfc_of_mem_nhdsSet (s := Set.univ) Real.negMulLog (by simp)
      (fun x => (hA x).isSelfAdjoint) Real.continuous_negMulLog.continuousOn
  exact RCLike.continuous_re.comp (continuous_id.matrix_trace.comp hfc)

omit [Fintype n] in
theorem hermitian_add_real_smul_one [Fintype n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (t : ℝ) : (A + t • (1 : Matrix n n ℂ)).IsHermitian := by
  exact hA.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t))

/-- Entropy is continuous for the unnormalized positive regularization. -/
theorem continuous_entropy_add_smul_one {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Continuous (fun t : ℝ => vonNeumannEntropy (A + t • (1 : Matrix n n ℂ))
      (hermitian_add_real_smul_one hA t)) := by
  exact continuous_vonNeumannEntropy_family _ (continuous_const.add
    (continuous_id.smul continuous_const))

omit [Fintype n] in
theorem posSemidef_add_pos_smul_one [Fintype n] {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {t : ℝ} (ht : 0 < t) : (A + t • (1 : Matrix n n ℂ)).PosDef := by
  have hone : (t • (1 : Matrix n n ℂ)).PosDef := Matrix.PosDef.one.smul ht
  simpa only [add_comm] using hone.add_posSemidef hA

#print axioms continuous_vonNeumannEntropy_family

end Fidelity
end
/- END ORIGINAL SOURCE: EntropyContinuityGeneral.lean -/


/- BEGIN ORIGINAL SOURCE: BlockBoundary.lean -/
section

/-! Extension of the block entropy inequality to positive semidefinite matrices. -/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Matrix Filter Topology

namespace Fidelity

noncomputable section

variable {n ι : Type*} [Fintype n] [DecidableEq n]
  [Fintype ι] [DecidableEq ι]

omit [Fintype n] in
theorem diagPinch_add_smul_one [Fintype n] (A : Matrix n n ℂ) (t : ℝ) :
    diagPinch (A + t • (1 : Matrix n n ℂ)) = diagPinch A + t • 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [diagPinch, Matrix.diag_apply]
  · simp [diagPinch, h]

omit [Fintype n] [Fintype ι] in
theorem blockPinch_add_smul_one [Fintype n] [Fintype ι] (G : Matrix (n × ι) (n × ι) ℂ) (t : ℝ) :
    blockPinch (G + t • (1 : Matrix (n × ι) (n × ι) ℂ)) =
      blockPinch G + t • 1 := by
  ext ⟨r, i⟩ ⟨s, j⟩
  by_cases h : i = j
  · subst j
    simp [blockPinch, blockOf, Matrix.blockDiagonal_apply, Matrix.one_apply]
  · simp [blockPinch, blockOf, Matrix.blockDiagonal_apply, h]

variable [Nonempty n]

/-- Three-block trace-norm compression does not increase the entropy loss
under outer pinching, including singular matrices. -/
theorem blockCoherence_normCompression3
    {G : Matrix (n × Fin 3) (n × Fin 3) ℂ} (hG : G.PosSemidef) :
    vonNeumannEntropy (diagPinch (normCompression3 G))
        (diagPinch_isHermitian (normCompression3_posSemidef hG).isHermitian) -
      vonNeumannEntropy (normCompression3 G) (normCompression3_posSemidef hG).isHermitian ≤
    vonNeumannEntropy (blockPinch G) (blockPinch_isHermitian hG.isHermitian) -
      vonNeumannEntropy G hG.isHermitian := by
  let C := normCompression3 G
  have hC : C.IsHermitian := (normCompression3_posSemidef hG).isHermitian
  have hDC : (diagPinch C).IsHermitian := diagPinch_isHermitian hC
  have hDG : (blockPinch G).IsHermitian := blockPinch_isHermitian hG.isHermitian
  let L : ℝ → ℝ := fun t =>
    vonNeumannEntropy (diagPinch C + ((Fintype.card n : ℝ) * t) • 1)
        (hermitian_add_real_smul_one hDC _) -
      vonNeumannEntropy (C + ((Fintype.card n : ℝ) * t) • 1)
        (hermitian_add_real_smul_one hC _)
  let R : ℝ → ℝ := fun t =>
    vonNeumannEntropy (blockPinch G + t • 1) (hermitian_add_real_smul_one hDG t) -
      vonNeumannEntropy (G + t • 1) (hermitian_add_real_smul_one hG.isHermitian t)
  have hcscale : Continuous (fun t : ℝ => (Fintype.card n : ℝ) * t) :=
    continuous_const.mul continuous_id
  have hcL : Continuous L :=
    ((continuous_entropy_add_smul_one hDC).comp hcscale).sub
      ((continuous_entropy_add_smul_one hC).comp hcscale)
  have hcR : Continuous R :=
    (continuous_entropy_add_smul_one hDG).sub
      (continuous_entropy_add_smul_one hG.isHermitian)
  have hpos (t : ℝ) (ht : 0 < t) : L t ≤ R t := by
    have h := blockCoherence_normCompression3_posDef
      (posSemidef_add_pos_smul_one hG ht)
    simp only [normCompression3_add_smul_one hG ht.le, diagPinch_add_smul_one,
      blockPinch_add_smul_one] at h
    exact h
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ), L t ≤ R t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpos t ht
  have hlim : L 0 ≤ R 0 := le_of_tendsto_of_tendsto
    (hcL.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hcR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hevent
  simpa only [L, R, C, mul_zero, zero_smul, add_zero] using hlim

#print axioms blockCoherence_normCompression3

end
end Fidelity
end
/- END ORIGINAL SOURCE: BlockBoundary.lean -/


/- BEGIN ORIGINAL SOURCE: EnsembleBridge.lean -/
section

/-! Reduction from the block entropy comparison to the three-state inequality.
Definitions use the matrix square root, nuclear norm, and spectral entropy. -/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Matrix

namespace Fidelity

noncomputable section

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

instance matrixRealScalarTower : IsScalarTower ℝ (Matrix n n ℂ) (Matrix n n ℂ) :=
  inferInstance

instance matrixRealSmulCommClass : SMulCommClass ℝ (Matrix n n ℂ) (Matrix n n ℂ) :=
  inferInstance

instance matrixRealFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint :=
  inferInstance


def horizontalStack (R : ι → Matrix n n ℂ) : Matrix n (n × ι) ℂ :=
  fun r si => R si.2 r si.1

omit [DecidableEq n] [Fintype ι] [DecidableEq ι] in
theorem horizontalStack_gram_block [DecidableEq n] [Fintype ι] [DecidableEq ι] (R : ι → Matrix n n ℂ) (i j : ι) :
    matrixBlock ((horizontalStack R)ᴴ * horizontalStack R) i j = (R i)ᴴ * R j := by
  ext r s
  simp [matrixBlock, horizontalStack, Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [DecidableEq n] [DecidableEq ι] in
theorem horizontalStack_covariance [DecidableEq n] [DecidableEq ι] (R : ι → Matrix n n ℂ) :
    horizontalStack R * (horizontalStack R)ᴴ = ∑ i, R i * (R i)ᴴ := by
  ext r s
  simp only [horizontalStack, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [Fintype n] [DecidableEq n] in
theorem real_smul_eq_complex_smul [Fintype n] [DecidableEq n] (c : ℝ) (A : Matrix n n ℂ) :
    c • A = (c : ℂ) • A := by
  ext i j
  exact Complex.real_smul

def weightedRoot (p : ι → ℝ) (ρ : ι → Matrix n n ℂ) (i : ι) : Matrix n n ℂ :=
  Real.sqrt (p i) • CFC.sqrt (ρ i)

omit [Fintype ι] [DecidableEq ι] in
theorem weightedRoot_isHermitian [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (ρ : ι → Matrix n n ℂ) (i : ι) :
    (weightedRoot p ρ i).IsHermitian := by
  apply ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (ρ i))).isHermitian).smul
  exact IsSelfAdjoint.all _

theorem weightedRoot_mul (p : ι → ℝ) (ρ : ι → Matrix n n ℂ) (i j : ι) :
    (weightedRoot p ρ i)ᴴ * weightedRoot p ρ j =
      (Real.sqrt (p i) * Real.sqrt (p j)) • (CFC.sqrt (ρ i) * CFC.sqrt (ρ j)) := by
  rw [(weightedRoot_isHermitian p ρ i).eq]
  simp only [weightedRoot, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm (Real.sqrt (p j)) (Real.sqrt (p i))]

theorem weightedRoot_square (p : ι → ℝ) (ρ : ι → Matrix n n ℂ)
    (hp : ∀ i, 0 ≤ p i) (hρ : ∀ i, (ρ i).PosSemidef) (i : ι) :
    weightedRoot p ρ i * (weightedRoot p ρ i)ᴴ = p i • ρ i := by
  rw [(weightedRoot_isHermitian p ρ i).eq]
  simp only [weightedRoot, smul_mul_assoc, mul_smul_comm, smul_smul,
    Real.mul_self_sqrt (hp i), CFC.sqrt_mul_sqrt_self (ρ i) (hρ i).nonneg]

def ensembleAverage (p : ι → ℝ) (ρ : ι → Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, p i • ρ i

omit [Fintype n] [DecidableEq n] [DecidableEq ι] in
theorem ensembleAverage_posSemidef [Fintype n] [DecidableEq n] [DecidableEq ι] (p : ι → ℝ) (ρ : ι → Matrix n n ℂ)
    (hp : ∀ i, 0 ≤ p i) (hρ : ∀ i, (ρ i).PosSemidef) :
    (ensembleAverage p ρ).PosSemidef :=
  Matrix.posSemidef_sum _ fun i _ => (hρ i).smul (hp i)

def ensembleGram (p : ι → ℝ) (ρ : ι → Matrix n n ℂ) :
    Matrix (n × ι) (n × ι) ℂ :=
  (horizontalStack (weightedRoot p ρ))ᴴ * horizontalStack (weightedRoot p ρ)

omit [DecidableEq ι] in
theorem ensembleGram_posSemidef [DecidableEq ι] (p : ι → ℝ) (ρ : ι → Matrix n n ℂ) :
    (ensembleGram p ρ).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _

theorem ensembleGram_block (p : ι → ℝ) (ρ : ι → Matrix n n ℂ) (i j : ι) :
    matrixBlock (ensembleGram p ρ) i j =
      (Real.sqrt (p i) * Real.sqrt (p j)) • (CFC.sqrt (ρ i) * CFC.sqrt (ρ j)) := by
  rw [ensembleGram, horizontalStack_gram_block, weightedRoot_mul]

theorem ensembleGram_diag_block (p : ι → ℝ) (ρ : ι → Matrix n n ℂ)
    (hp : ∀ i, 0 ≤ p i) (hρ : ∀ i, (ρ i).PosSemidef) (i : ι) :
    matrixBlock (ensembleGram p ρ) i i = p i • ρ i := by
  rw [ensembleGram_block, Real.mul_self_sqrt (hp i),
    CFC.sqrt_mul_sqrt_self (ρ i) (hρ i).nonneg]

theorem entropy_ensembleGram (p : ι → ℝ) (ρ : ι → Matrix n n ℂ)
    (hp : ∀ i, 0 ≤ p i) (hρ : ∀ i, (ρ i).PosSemidef) :
    vonNeumannEntropy (ensembleGram p ρ) (ensembleGram_posSemidef p ρ).isHermitian =
      vonNeumannEntropy (ensembleAverage p ρ)
        (ensembleAverage_posSemidef p ρ hp hρ).isHermitian := by
  let X := horizontalStack (weightedRoot p ρ)
  have hXX : X * Xᴴ = ensembleAverage p ρ := by
    rw [horizontalStack_covariance]
    simp_rw [weightedRoot_square p ρ hp hρ]
    rfl
  have h := vonNeumannEntropy_mul_comm Xᴴ X
    (Matrix.posSemidef_conjTranspose_mul_self X).isHermitian
    (Matrix.posSemidef_self_mul_conjTranspose X).isHermitian
  simpa only [hXX, ensembleGram, X] using h

theorem entropy_real_smul_density {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htrace : A.trace = 1) (p : ℝ) :
    vonNeumannEntropy (p • A) (hA.isHermitian.smul (IsSelfAdjoint.all p)) =
      p * vonNeumannEntropy A hA.isHermitian + Real.negMulLog p := by
  simpa only [← real_smul_eq_complex_smul] using vonNeumannEntropy_smul hA htrace p

theorem entropy_blockPinch_ensembleGram (p : ι → ℝ) (ρ : ι → Matrix n n ℂ)
    (hp : ∀ i, 0 ≤ p i) (hρ : ∀ i, (ρ i).PosSemidef)
    (htrace : ∀ i, (ρ i).trace = 1) :
    vonNeumannEntropy (blockPinch (ensembleGram p ρ))
        (blockPinch_isHermitian (ensembleGram_posSemidef p ρ).isHermitian) =
      (∑ i, Real.negMulLog (p i)) +
        ∑ i, p i * vonNeumannEntropy (ρ i) (hρ i).isHermitian := by
  have hblocks : blockPinch (ensembleGram p ρ) =
      Matrix.blockDiagonal (fun i => p i • ρ i) := by
    apply congrArg Matrix.blockDiagonal
    funext i
    exact ensembleGram_diag_block p ρ hp hρ i
  simp only [hblocks, entropy_blockDiagonal _
    (fun i => (hρ i).isHermitian.smul (IsSelfAdjoint.all (p i)))]
  simp_rw [entropy_real_smul_density (hρ _) (htrace _)]
  rw [Finset.sum_add_distrib, add_comm]

/-- The matrix in the original conjecture, using the unsquared root fidelity. -/
def rootFidelityMatrix (p : Fin 3 → ℝ) (ρ : Fin 3 → Matrix n n ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => (Real.sqrt (p i) * Real.sqrt (p j) *
    nuclear (CFC.sqrt (ρ i) * CFC.sqrt (ρ j)) : ℝ)

theorem normCompression3_ensembleGram (p : Fin 3 → ℝ)
    (ρ : Fin 3 → Matrix n n ℂ) :
    normCompression3 (ensembleGram p ρ) = rootFidelityMatrix p ρ := by
  ext i j
  change (nuclear (matrixBlock (ensembleGram p ρ) i j) : ℂ) = _
  rw [ensembleGram_block, nuclear_smul_nonneg _ _
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  rfl

theorem rootFidelityMatrix_posSemidef (p : Fin 3 → ℝ)
    (ρ : Fin 3 → Matrix n n ℂ) : (rootFidelityMatrix p ρ).PosSemidef := by
  rw [← normCompression3_ensembleGram]
  exact normCompression3_posSemidef (ensembleGram_posSemidef p ρ)

theorem diagPinch_rootFidelityMatrix (p : Fin 3 → ℝ)
    (ρ : Fin 3 → Matrix n n ℂ) (hp : ∀ i, 0 ≤ p i)
    (hρ : ∀ i, (ρ i).PosSemidef) (htrace : ∀ i, (ρ i).trace = 1) :
    diagPinch (rootFidelityMatrix p ρ) = Matrix.diagonal (fun i => (p i : ℂ)) := by
  apply congrArg Matrix.diagonal
  funext i
  change ((Real.sqrt (p i) * Real.sqrt (p i) *
    nuclear (CFC.sqrt (ρ i) * CFC.sqrt (ρ i)) : ℝ) : ℂ) = (p i : ℂ)
  rw [Real.mul_self_sqrt (hp i), CFC.sqrt_mul_sqrt_self (ρ i) (hρ i).nonneg,
    nuclear_posSemidef (hρ i), htrace i]
  simp

theorem rootFidelityMatrix_trace_one (p : Fin 3 → ℝ)
    (ρ : Fin 3 → Matrix n n ℂ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (hρ : ∀ i, (ρ i).PosSemidef)
    (htrace : ∀ i, (ρ i).trace = 1) : (rootFidelityMatrix p ρ).trace = 1 := by
  calc
    (rootFidelityMatrix p ρ).trace =
        (diagPinch (rootFidelityMatrix p ρ)).trace := by
      simp [diagPinch, Matrix.trace, Matrix.diag_apply]
    _ = (Matrix.diagonal (fun i => (p i : ℂ))).trace :=
      congrArg Matrix.trace (diagPinch_rootFidelityMatrix p ρ hp hρ htrace)
    _ = 1 := by
      rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, hsum]
      rfl

/-- The unrestricted three-state root-fidelity entropy bound. -/
theorem holevo_le_entropy_rootFidelityMatrix (p : Fin 3 → ℝ)
    (ρ : Fin 3 → Matrix n n ℂ) (hp : ∀ i, 0 ≤ p i)
    (_hsum : ∑ i, p i = 1) (hρ : ∀ i, (ρ i).PosSemidef)
    (htrace : ∀ i, (ρ i).trace = 1) :
    vonNeumannEntropy (ensembleAverage p ρ)
        (ensembleAverage_posSemidef p ρ hp hρ).isHermitian -
      (∑ i, p i * vonNeumannEntropy (ρ i) (hρ i).isHermitian) ≤
    vonNeumannEntropy (rootFidelityMatrix p ρ)
      (rootFidelityMatrix_posSemidef p ρ).isHermitian := by
  classical
  have : Nonempty n := by
    by_contra hn
    have : IsEmpty n := not_nonempty_iff.mp hn
    have ht := htrace 0
    simp [Matrix.trace] at ht
  have h := blockCoherence_normCompression3 (ensembleGram_posSemidef p ρ)
  simp only [normCompression3_ensembleGram, entropy_ensembleGram p ρ hp hρ,
    entropy_blockPinch_ensembleGram p ρ hp hρ htrace,
    diagPinch_rootFidelityMatrix p ρ hp hρ htrace,
    Matrix.vonNeumannEntropy_diagonal] at h
  linarith

#print axioms holevo_le_entropy_rootFidelityMatrix

end
end Fidelity
end
/- END ORIGINAL SOURCE: EnsembleBridge.lean -/


#check @Fidelity.holevo_le_entropy_rootFidelityMatrix
#print axioms Fidelity.holevo_le_entropy_rootFidelityMatrix
