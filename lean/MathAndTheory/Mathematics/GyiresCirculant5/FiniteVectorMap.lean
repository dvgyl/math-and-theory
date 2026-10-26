module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases

/-!
# Vectors of length 5, 6 and 11

Lemmas for mapping over and comparing explicit vectors `![x₀, …]`, and for proving a
statement for every element of `Fin n`, `n ≤ 11`, one element at a time.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0

namespace MathAndTheory.GyiresCirculant5

theorem map_vec5 {α β : Type*} (f : α → β) (x0 x1 x2 x3 x4 : α) :
    (fun i => f (![x0, x1, x2, x3, x4] i)) = ![f x0, f x1, f x2, f x3, f x4] := by
  funext i
  fin_cases i <;> rfl

theorem vec5_congr {α : Type*} (x0 x1 x2 x3 x4 : α) (y0 y1 y2 y3 y4 : α)
    (h0 : x0 = y0)
    (h1 : x1 = y1)
    (h2 : x2 = y2)
    (h3 : x3 = y3)
    (h4 : x4 = y4) : ![x0, x1, x2, x3, x4] = ![y0, y1, y2, y3, y4] := by
  subst_vars
  rfl

theorem map_vec6 {α β : Type*} (f : α → β) (x0 x1 x2 x3 x4 x5 : α) :
    (fun i => f (![x0, x1, x2, x3, x4, x5] i)) = ![f x0, f x1, f x2, f x3, f x4, f x5] := by
  funext i
  fin_cases i <;> rfl

theorem vec6_congr {α : Type*} (x0 x1 x2 x3 x4 x5 : α) (y0 y1 y2 y3 y4 y5 : α)
    (h0 : x0 = y0)
    (h1 : x1 = y1)
    (h2 : x2 = y2)
    (h3 : x3 = y3)
    (h4 : x4 = y4)
    (h5 : x5 = y5) : ![x0, x1, x2, x3, x4, x5] = ![y0, y1, y2, y3, y4, y5] := by
  subst_vars
  rfl

theorem map_vec11 {α β : Type*} (f : α → β) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : α) :
    (fun i => f (![x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10] i)) = ![f x0, f x1, f x2, f x3, f x4, f x5, f x6, f x7, f x8, f x9, f x10] := by
  funext i
  fin_cases i <;> rfl

theorem vec11_congr {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : α) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 : α)
    (h0 : x0 = y0)
    (h1 : x1 = y1)
    (h2 : x2 = y2)
    (h3 : x3 = y3)
    (h4 : x4 = y4)
    (h5 : x5 = y5)
    (h6 : x6 = y6)
    (h7 : x7 = y7)
    (h8 : x8 = y8)
    (h9 : x9 = y9)
    (h10 : x10 = y10) : ![x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10] = ![y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10] := by
  subst_vars
  rfl

theorem forall_fin1 (P : Fin 1 → Prop) (h0 : P 0) : ∀ i, P i := by
  intro i
  fin_cases i
  exact h0

theorem forall_fin2 (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

theorem forall_fin3 (P : Fin 3 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

theorem forall_fin4 (P : Fin 4 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

theorem forall_fin5 (P : Fin 5 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

theorem forall_fin6 (P : Fin 6 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

theorem forall_fin7 (P : Fin 7 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

theorem forall_fin8 (P : Fin 8 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

theorem forall_fin9 (P : Fin 9 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

theorem forall_fin10 (P : Fin 10 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

theorem forall_fin11 (P : Fin 11 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

end MathAndTheory.GyiresCirculant5
