import IntegerNumerics
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! List-backed integer matrices for the interval certificates of version 1.1.

The certificate data are stored as lists of integer rows or columns. Closed
kernel computations check sequential sums over these lists, and the lemmas
below identify those sums with the `Finset` sums that occur in the matrix
statements used by the convergence proof. Nothing here is specific to a
particular certificate.
-/

open scoped BigOperators

namespace ADMMNearSharpCertificate.IntLists

/-- The sum of the first `n` products of corresponding entries; missing entries
count as zero. -/
def dotN : ℕ → List ℤ → List ℤ → ℤ
  | 0, _, _ => 0
  | _ + 1, [], _ => 0
  | _ + 1, _ :: _, [] => 0
  | n + 1, x :: xs, y :: ys => x * y + dotN n xs ys

/-- The sum of the first `n` entries. -/
def sumN : ℕ → List ℤ → ℤ
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, x :: xs => x + sumN n xs

/-- The sum of the absolute values of the first `n` entries. -/
def absSumN : ℕ → List ℤ → ℤ
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, x :: xs => |x| + absSumN n xs

/-- Entrywise `c₁ p + c₂ v + c₃ x` on the first `n` entries. -/
def lin3N (c₁ c₂ c₃ : ℤ) : ℕ → List ℤ → List ℤ → List ℤ → List ℤ
  | 0, _, _, _ => []
  | n + 1, p, v, x =>
      (c₁ * p.headD 0 + c₂ * v.headD 0 + c₃ * x.headD 0) ::
        lin3N c₁ c₂ c₃ n p.tail v.tail x.tail

/-- Entry `(i, j)` of a list of rows. -/
def lget (L : List (List ℤ)) (i j : ℕ) : ℤ := (L.getD i []).getD j 0

/-- The matrix whose `i`-th row is the `i`-th list. -/
def rowMat (m n : ℕ) (L : List (List ℤ)) : Matrix (Fin m) (Fin n) ℤ :=
  fun i j => lget L i j

/-- The matrix whose `j`-th column is the `j`-th list. -/
def colMat (m n : ℕ) (L : List (List ℤ)) : Matrix (Fin m) (Fin n) ℤ :=
  fun i j => lget L j i

theorem getD_tail (a : List ℤ) (k : ℕ) : a.tail.getD k 0 = a.getD (k + 1) 0 := by
  cases a <;> simp

theorem getD_zero_headD (a : List ℤ) : a.getD 0 0 = a.headD 0 := by
  cases a <;> simp

theorem sum_dotN : ∀ (n : ℕ) (a b : List ℤ),
    ∑ k : Fin n, a.getD k 0 * b.getD k 0 = dotN n a b
  | 0, _, _ => by simp [dotN]
  | n + 1, [], _ => by simp [dotN]
  | n + 1, _ :: _, [] => by simp [dotN]
  | n + 1, x :: xs, y :: ys => by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]
      rw [sum_dotN n xs ys]
      rfl

theorem sum_sumN : ∀ (n : ℕ) (a : List ℤ), ∑ k : Fin n, a.getD k 0 = sumN n a
  | 0, _ => by simp [sumN]
  | n + 1, [] => by simp [sumN]
  | n + 1, x :: xs => by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]
      rw [sum_sumN n xs]
      rfl

theorem sum_absSumN : ∀ (n : ℕ) (a : List ℤ), ∑ k : Fin n, |a.getD k 0| = absSumN n a
  | 0, _ => by simp [absSumN]
  | n + 1, [] => by simp [absSumN]
  | n + 1, x :: xs => by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]
      rw [sum_absSumN n xs]
      rfl

theorem getD_lin3N (c₁ c₂ c₃ : ℤ) : ∀ (n : ℕ) (p v x : List ℤ) (s : ℕ), s < n →
    (lin3N c₁ c₂ c₃ n p v x).getD s 0 =
      c₁ * p.getD s 0 + c₂ * v.getD s 0 + c₃ * x.getD s 0
  | 0, _, _, _, s, h => absurd h (Nat.not_lt_zero s)
  | n + 1, p, v, x, 0, _ => by
      simp only [lin3N, List.getD_cons_zero, getD_zero_headD]
  | n + 1, p, v, x, s + 1, h => by
      simp only [lin3N, List.getD_cons_succ]
      rw [getD_lin3N c₁ c₂ c₃ n p.tail v.tail x.tail s (by omega)]
      simp only [getD_tail]

/-- Gram entries of a matrix stored by columns. -/
theorem gram_entry {k n : ℕ} (L : List (List ℤ)) (i j : Fin n) :
    ((colMat k n L).transpose * colMat k n L) i j =
      dotN k (L.getD i []) (L.getD j []) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, colMat, lget]
  exact sum_dotN k _ _

/-- Diagonal dominance of a matrix stored by rows, from one sequential sum per row. -/
theorem dd_of_absSum {n : ℕ} (L : List (List ℤ)) (i : Fin n)
    (h : absSumN n (L.getD i []) ≤ rowMat n n L i i + |rowMat n n L i i|) :
    ∑ j ∈ Finset.univ.erase i, |rowMat n n L i j| ≤ rowMat n n L i i := by
  have hs := Finset.add_sum_erase Finset.univ (fun j => |rowMat n n L i j|) (Finset.mem_univ i)
  have ht : ∑ j : Fin n, |rowMat n n L i j| = absSumN n (L.getD i []) := by
    simp only [rowMat, lget]
    exact sum_absSumN n _
  linarith

/-- Weighted point differences with weights stored by rows and points by columns. -/
theorem weighted_entry {r N : ℕ} (LL XL : List (List ℤ)) (i : Fin r) (k : Fin N) :
    IntArithmetic.weightedDifferences (rowMat r r LL) (colMat r N XL) i k =
      dotN r (LL.getD i []) (XL.getD k []) -
        (XL.getD k []).getD i 0 * sumN r (LL.getD i []) := by
  simp only [IntArithmetic.weightedDifferences, rowMat, colMat, lget]
  rw [← sum_dotN, ← sum_sumN, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Entries of a sum of symmetrized products, with both factors stored by columns. -/
theorem cross_sum_entry {r N : ℕ} (A W : Matrix (Fin r) (Fin N) ℤ)
    (AL WL : List (List ℤ)) (hA : ∀ s k, A s k = (AL.getD k []).getD s 0)
    (hW : ∀ s k, W s k = (WL.getD k []).getD s 0) (i j : Fin N) :
    (∑ s, IntArithmetic.integerCross (A s) (W s)) i j =
      dotN r (AL.getD i []) (WL.getD j []) + dotN r (WL.getD i []) (AL.getD j []) := by
  simp only [Matrix.sum_apply, IntArithmetic.integerCross, Finset.sum_add_distrib, hA, hW]
  rw [sum_dotN, sum_dotN]

/-- A matrix stored by columns that agrees, column by column, with an entrywise
linear combination of three other matrices stored by columns. -/
theorem colMat_lin3 {r N : ℕ} (c₁ c₂ c₃ : ℤ) (AL PL VL XL : List (List ℤ))
    (h : ∀ k : Fin N, AL.getD k [] = lin3N c₁ c₂ c₃ r (PL.getD k []) (VL.getD k []) (XL.getD k []))
    (s : Fin r) (k : Fin N) :
    c₁ * colMat r N PL s k + c₂ * colMat r N VL s k + c₃ * colMat r N XL s k =
      (AL.getD k []).getD s 0 := by
  simp only [colMat, lget]
  rw [h k, getD_lin3N c₁ c₂ c₃ r _ _ _ s s.isLt]

end ADMMNearSharpCertificate.IntLists
