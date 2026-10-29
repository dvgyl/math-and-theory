/-
Copyright (c) 2026 Chris Ozols. Licensed under the Apache License, Version 2.0.

Adapted from `RequestProject/Reduction.lean` at commit
244f48c270d0a4d0801383e15202886b384b2d67 of https://github.com/cozuya/gyires-permanent-4x4.
Modifications: the namespace, the imports, the port to Lean 4.35 and the module system, and the
circulant corollary `MathAndTheory.GyiresCirculant5.conv_permanent_le_gram` at the end of the file.
-/
module

public import MathAndTheory.Mathematics.Gyires.CirculantFive.MatrixBridge
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# The reduction inequality `per(M Mᵀ) + per(N Nᵀ) ≥ 2 per(M Nᵀ)`

For real square matrices `M` and `N` of any size, `2 per(M Nᵀ) ≤ per(M Mᵀ) + per(N Nᵀ)`.
Applied to `M = circ w` and `N = (circ w)ᵀ`, it gives `P5 (conv w) ≤ P5 (gram w)`
(`conv_permanent_le_gram`), so that `gyiresDefect w ≥ strongDefect w`.
-/

@[expose] public section

open Finset Equiv
open scoped BigOperators

namespace MathAndTheory.GyiresCirculant5.PermanentGram

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Monomials `∏ᵢ M i (φ i)` indexed by functions `φ`. -/
def umono (M : Matrix n n ℝ) (φ : n → n) : ℝ := ∏ i, M i (φ i)

/-- The bilinear form realizing `per(M Nᵀ)`. -/
def bform (a b : (n → n) → ℝ) : ℝ := ∑ σ : Perm n, ∑ φ : n → n, a (φ ∘ σ.symm) * b φ

lemma permanent_mul_transpose (M N : Matrix n n ℝ) :
    (M * N.transpose).permanent = bform (umono M) (umono N) := by
  simp only [Matrix.permanent, Matrix.mul_apply, Matrix.transpose_apply, bform, umono]
  refine sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]
  refine Fintype.sum_congr _ _ fun φ => ?_
  rw [prod_mul_distrib]
  congr 1
  exact (Equiv.prod_comp σ (fun i => M i (φ (σ.symm i)))).symm.trans (by simp) |>.symm

lemma bform_comm (M N : Matrix n n ℝ) : bform (umono N) (umono M) = bform (umono M) (umono N) := by
  rw [← permanent_mul_transpose, ← permanent_mul_transpose, ← Matrix.permanent_transpose]
  simp [Matrix.transpose_mul]

lemma bform_self_nonneg (d : (n → n) → ℝ) : 0 ≤ bform d d := by
  have key : (Fintype.card (Perm n) : ℝ) * bform d d =
      ∑ ψ : n → n, (∑ τ : Perm n, d (ψ ∘ τ)) ^ 2 := by
    have inner : ∀ τ ρ : Perm n, ∑ ψ : n → n, d (ψ ∘ τ) * d (ψ ∘ ρ) =
        ∑ φ : n → n, d (φ ∘ (τ⁻¹ * ρ).symm) * d φ := by
      intro τ ρ
      rw [← Equiv.sum_comp (Equiv.arrowCongr ρ (Equiv.refl n)) (fun ψ => d (ψ ∘ τ) * d (ψ ∘ ρ))]
      refine Fintype.sum_congr _ _ fun φ => ?_
      have h1 : (Equiv.arrowCongr ρ (Equiv.refl n)) φ ∘ ρ = φ := by
        ext x; simp [Equiv.arrowCongr_apply]
      have h2 : (Equiv.arrowCongr ρ (Equiv.refl n)) φ ∘ τ = φ ∘ (τ⁻¹ * ρ).symm := by
        ext x
        show φ (ρ.symm (τ x)) = φ ((τ⁻¹ * ρ)⁻¹ x)
        rw [mul_inv_rev, inv_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
      simp only [h1, h2]
    simp only [sq, sum_mul_sum]
    rw [sum_comm]
    simp_rw [sum_comm (s := (univ : Finset (n → n))) (t := (univ : Finset (Perm n))), inner]
    have h3 : ∀ τ : Perm n, ∑ ρ : Perm n, ∑ φ : n → n, d (φ ∘ (τ⁻¹ * ρ).symm) * d φ = bform d d := by
      intro τ
      exact Equiv.sum_comp (Equiv.mulLeft τ⁻¹) (fun σ => ∑ φ : n → n, d (φ ∘ σ.symm) * d φ)
    simp_rw [h3]
    simp
  have hc : (0 : ℝ) < Fintype.card (Perm n) := by exact_mod_cast Fintype.card_pos
  have : 0 ≤ (Fintype.card (Perm n) : ℝ) * bform d d := by
    rw [key]; exact sum_nonneg fun _ _ => sq_nonneg _
  exact (mul_nonneg_iff_of_pos_left hc).mp this

lemma bform_sub (a b c : (n → n) → ℝ) : bform (a - b) c = bform a c - bform b c := by
  simp only [bform, Pi.sub_apply, sub_mul, sum_sub_distrib]

lemma bform_sub' (a b c : (n → n) → ℝ) : bform c (a - b) = bform c a - bform c b := by
  simp only [bform, Pi.sub_apply, mul_sub, sum_sub_distrib]

theorem permanent_gram_add_ge (M N : Matrix n n ℝ) :
    2 * (M * N.transpose).permanent ≤
      (M * M.transpose).permanent + (N * N.transpose).permanent := by
  have h := bform_self_nonneg (umono M - umono N)
  rw [bform_sub, bform_sub', bform_sub', bform_comm M N] at h
  rw [permanent_mul_transpose, permanent_mul_transpose, permanent_mul_transpose]
  linarith

end MathAndTheory.GyiresCirculant5.PermanentGram

namespace MathAndTheory.GyiresCirculant5

/-- The standard Gram comparison specialized to a real circulant. -/
theorem conv_permanent_le_gram (w : Fin 5 → ℝ) :
    P5 (conv w) ≤ P5 (gram w) := by
  have h := PermanentGram.permanent_gram_add_ge (circ w) (circ w).transpose
  simp only [Matrix.transpose_transpose] at h
  rw [circ_mul_self, circ_mul_transpose, transpose_mul_circ] at h
  simp only [permanent_circ] at h
  linarith

end MathAndTheory.GyiresCirculant5
