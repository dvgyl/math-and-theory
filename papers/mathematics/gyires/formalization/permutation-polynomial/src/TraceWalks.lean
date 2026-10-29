module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCycle

open Matrix Finset Equiv
open scoped BigOperators

variable {κ R : Type*} [Fintype κ] [DecidableEq κ] [CommSemiring R]

def pathWeight (M : Matrix κ κ R) {n : ℕ} (f : Fin n → κ) (x y : κ) : R :=
  ∏ i : Fin (n + 1), M (Fin.cons (α := fun _ : Fin (n + 1) => κ) x f i) (Fin.snoc (α := fun _ : Fin (n + 1) => κ) f y i)

omit [Fintype κ] [DecidableEq κ] in
theorem pathWeight_cons (M : Matrix κ κ R) {n : ℕ} (f : Fin n → κ) (x z y : κ) :
    pathWeight M (Fin.cons (α := fun _ : Fin (n + 1) => κ) z f) x y = M x z * pathWeight M f z y := by
  unfold pathWeight
  rw [← Fin.cons_snoc_eq_snoc_cons]
  simp [Fin.prod_univ_succ]

theorem sum_pathWeight (M : Matrix κ κ R) (n : ℕ) (x y : κ) :
    (∑ f : Fin n → κ, pathWeight M f x y) = (M ^ (n + 1)) x y := by
  classical
  induction n generalizing x y with
  | zero => simp [pathWeight, Fin.snoc]
  | succ n ih =>
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => κ))]
    rw [Fintype.sum_prod_type]
    change (∑ z, ∑ f : Fin n → κ,
      pathWeight M (Fin.cons (α := fun _ : Fin (n + 1) => κ) z f) x y) = _
    calc
      _ = ∑ z, M x z * ∑ f : Fin n → κ, pathWeight M f z y := by
        apply Finset.sum_congr rfl
        intro z hz
        simp only [pathWeight_cons, Finset.mul_sum]
      _ = ∑ z, M x z * (M ^ (n + 1)) z y := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [ih]
      _ = (M * M ^ (n + 1)) x y := rfl
      _ = (M ^ (n + 1 + 1)) x y := by rw [← pow_succ']

theorem trace_pow_eq_closed_walks (M : Matrix κ κ R) (n : ℕ) :
    Matrix.trace (M ^ (n + 1)) =
      ∑ s : Fin (n + 1) → κ,
        ∏ i : Fin (n + 1), M (s i) (s (finRotate (n + 1) i)) := by
  classical
  unfold Matrix.trace
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => κ))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  change (M ^ (n + 1)) x x = _
  rw [← sum_pathWeight M n x x]
  apply Finset.sum_congr rfl
  intro f hf
  unfold pathWeight
  rw [Fin.snoc_eq_cons_rotate]
  rfl

end MathAndTheory.Gyires.PermutationCycle
