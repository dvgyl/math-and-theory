module

public import PermutationGramExpansion
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

namespace MathAndTheory.Gyires.PermutationAssembly

open Matrix Equiv
open scoped BigOperators
open MathAndTheory.Gyires.PermutationMatrixBridge

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem permanent_submatrix_equiv (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    (A.submatrix e e).permanent = A.permanent := by
  unfold Matrix.permanent
  calc
    _ = ∑ σ : Equiv.Perm κ, ∏ i : ι, A (e.permCongr σ i) i := by
      apply Finset.sum_congr rfl
      intro σ _
      simpa only [Matrix.submatrix_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply] using
        e.prod_comp (fun i => A (e.permCongr σ i) i)
    _ = _ := e.permCongr.sum_comp (fun σ => ∏ i, A (σ i) i)

omit [Fintype ι] [Fintype κ] in
theorem permMatrix_submatrix_equiv (p : Equiv.Perm ι) (q : Equiv.Perm κ) (e : κ ≃ ι)
    (h : ∀ i, e (q i) = p (e i)) :
    (p.permMatrix ℝ).submatrix e e = q.permMatrix ℝ := by
  ext i j
  simp only [Matrix.submatrix_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, ← h, e.injective.eq_iff]

theorem polynomialMatrix_submatrix_equiv (p : Equiv.Perm ι) (q : Equiv.Perm κ)
    (e : κ ≃ ι) (h : ∀ i, e (q i) = p (e i)) (a b c : ℝ) :
    (polynomialMatrix p a b c).submatrix e e = polynomialMatrix q a b c := by
  have hp := permMatrix_submatrix_equiv p q e h
  have hs : ((p.permMatrix ℝ)^2).submatrix e e = (q.permMatrix ℝ)^2 := by
    simp only [pow_two, ← Matrix.submatrix_mul_equiv _ _ e e e, hp]
  change a • ((1 : Matrix ι ι ℝ).submatrix e e) +
    b • ((p.permMatrix ℝ).submatrix e e) + c • (((p.permMatrix ℝ)^2).submatrix e e) = _
  rw [Matrix.submatrix_one_equiv, hp, hs]
  rfl

theorem strong_gram_submatrix_equiv_iff (A : Matrix ι ι ℝ) (e : κ ≃ ι) (K : ℝ) :
    K * ((A.submatrix e e) * (A.submatrix e e).transpose).permanent ≤
      (A.submatrix e e).permanent^2 ↔
    K * (A*A.transpose).permanent ≤ A.permanent^2 := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
    permanent_submatrix_equiv, permanent_submatrix_equiv]

variable {β : Type*} {γ : β → Type*} [Fintype β] [DecidableEq β]
  [∀ i, Fintype (γ i)] [∀ i, DecidableEq (γ i)]

omit [Fintype β] [∀ i, Fintype (γ i)] in
theorem sigmaPerm_permMatrix (p : ∀ i, Equiv.Perm (γ i)) :
    Equiv.Perm.permMatrix ℝ (Equiv.sigmaCongrRight p) = Matrix.blockDiagonal' (fun i => (p i).permMatrix ℝ) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  by_cases h : i = j
  · subst j
    simp only [Matrix.blockDiagonal'_apply_eq, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.sigmaCongrRight_apply,
      Sigma.mk.inj_iff, heq_eq_eq, true_and]
  · have hn : (⟨i, p i x⟩ : Sigma γ) ≠ ⟨j, y⟩ := by
      intro heq
      exact h (congrArg Sigma.fst heq)
    simp only [Matrix.blockDiagonal'_apply_ne _ _ _ h, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
      Equiv.sigmaCongrRight_apply, hn, ite_false]

theorem sigmaPerm_polynomialMatrix (p : ∀ i, Equiv.Perm (γ i)) (a b c : ℝ) :
    polynomialMatrix (Equiv.sigmaCongrRight p) a b c =
      Matrix.blockDiagonal' (fun i => polynomialMatrix (p i) a b c) := by
  rw [polynomialMatrix, sigmaPerm_permMatrix]
  change _ = Matrix.blockDiagonal' (a • (1 : ∀ i, Matrix (γ i) (γ i) ℝ) +
    b • (fun i => (p i).permMatrix ℝ) + c • (fun i => ((p i).permMatrix ℝ)^2))
  rw [Matrix.blockDiagonal'_add, Matrix.blockDiagonal'_add, Matrix.blockDiagonal'_smul,
    Matrix.blockDiagonal'_smul, Matrix.blockDiagonal'_smul, Matrix.blockDiagonal'_one]
  have hpow : Matrix.blockDiagonal' (fun i => ((p i).permMatrix ℝ)^2) =
      (Matrix.blockDiagonal' (fun i => (p i).permMatrix ℝ))^2 :=
    Matrix.blockDiagonal'_pow (fun i => (p i).permMatrix ℝ) 2
  rw [hpow]

end MathAndTheory.Gyires.PermutationAssembly
