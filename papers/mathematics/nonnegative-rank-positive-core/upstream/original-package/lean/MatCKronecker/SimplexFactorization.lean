module

public import MatCKronecker.NonnegativeRank
public import Mathlib.Algebra.BigOperators.Option

@[expose] public section

namespace MatCKronecker

open Matrix
open scoped BigOperators

variable {m n q : Type*} [Fintype q]

/-- The simplex columns replacing one strictly positive outer product. -/
noncomputable def simplexLeft (u : m → ℝ) (R : Matrix m q ℝ) (eta : ℝ) :
    Matrix m (Option q) ℝ := fun i a =>
  match a with
  | some k => u i + eta * R i k
  | none => u i - eta * ∑ k, R i k

/-- The matching simplex rows. -/
noncomputable def simplexRight (v : n → ℝ) (T : Matrix q n ℝ) (eps eta : ℝ) :
    Matrix (Option q) n ℝ := fun a j =>
  match a with
  | some k => v j / ((Fintype.card q : ℝ) + 1) + (eps / eta) *
      (T k j - (∑ l, T l j) / ((Fintype.card q : ℝ) + 1))
  | none => v j / ((Fintype.card q : ℝ) + 1) - (eps / eta) *
      ((∑ l, T l j) / ((Fintype.card q : ℝ) + 1))

theorem simplexRight_sum (v : n → ℝ) (T : Matrix q n ℝ) (eps eta : ℝ) (j : n) :
    (∑ a : Option q, simplexRight v T eps eta a j) = v j := by
  classical
  have hc : (Fintype.card q : ℝ) + 1 ≠ 0 := by positivity
  simp only [univ_option, Finset.sum_insertNone, simplexRight]
  simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem simplexRight_sub_none (v : n → ℝ) (T : Matrix q n ℝ)
    (eps eta : ℝ) (k : q) (j : n) :
    simplexRight v T eps eta (some k) j - simplexRight v T eps eta none j =
      (eps / eta) * T k j := by
  simp only [simplexRight]
  ring

def simplexRowDifferences (G : Matrix (Option q) n ℝ) : Matrix q n ℝ :=
  fun k j => G (some k) j - G none j

/-- Algebraic column/row reduction; no positivity or rank premise occurs. -/
theorem simplexLeft_mul (u : m → ℝ) (R : Matrix m q ℝ) (eta : ℝ)
    (G : Matrix (Option q) n ℝ) :
    simplexLeft u R eta * G =
      Matrix.vecMulVec u (fun j => ∑ a : Option q, G a j) +
        eta • (R * simplexRowDifferences G) := by
  classical
  ext i j
  have hs : (∑ k : q, (u i + eta * R i k) * G (some k) j) =
      u i * (∑ k : q, G (some k) j) +
        eta * (∑ k : q, R i k * G (some k) j) := by
    simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hd : (∑ k : q, R i k * (G (some k) j - G none j)) =
      (∑ k : q, R i k * G (some k) j) -
        (∑ k : q, R i k) * G none j := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.vecMulVec_apply, univ_option, Finset.sum_insertNone,
    simplexLeft, simplexRowDifferences]
  rw [hs, hd]
  ring

/-- Exact simplex factorization of a rank-one term plus a factored perturbation. -/
theorem simplex_factorization (u : m → ℝ) (v : n → ℝ)
    (R : Matrix m q ℝ) (T : Matrix q n ℝ) (eps eta : ℝ) (heta : eta ≠ 0) :
    simplexLeft u R eta * simplexRight v T eps eta =
      Matrix.vecMulVec u v + eps • (R * T) := by
  classical
  rw [simplexLeft_mul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, simplexRight_sum, Matrix.mul_apply,
    simplexRowDifferences, simplexRight_sub_none]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  field_simp

/-- A finite absolute sum estimate specialized to the 18-coordinate construction. -/
theorem abs_sum_eighteen_le (hcard : Fintype.card q = 18)
    (f : q → ℝ) (b : ℝ) (hf : ∀ k, |f k| ≤ b) :
    |∑ k, f k| ≤ 18 * b := by
  classical
  calc
    |∑ k, f k| ≤ ∑ k, |f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : q, b := Finset.sum_le_sum fun k _ => hf k
    _ = 18 * b := by simp [hcard]

/-- Entrywise positivity of the actual 19-column correction used in the witness. -/
theorem simplexLeft_nonneg_eighteen (hcard : Fintype.card q = 18)
    (u : m → ℝ) (R : Matrix m q ℝ)
    (hu : ∀ i, (1 : ℝ) / 36 ≤ u i)
    (hR : ∀ i k, |R i k| ≤ 17) :
    EntryNonneg (simplexLeft u R ((1 : ℝ) / 15120)) := by
  intro i a
  cases a with
  | some k =>
    have hl := (abs_le.mp (hR i k)).1
    simp only [simplexLeft]
    nlinarith [hu i]
  | none =>
    have hs := abs_sum_eighteen_le hcard (R i) 17 (hR i)
    have hh := (abs_le.mp hs).2
    simp only [simplexLeft]
    nlinarith [hu i]

/-- Entrywise positivity of the actual matching 19-row correction. -/
theorem simplexRight_nonneg_eighteen (hcard : Fintype.card q = 18)
    (v : n → ℝ) (T : Matrix q n ℝ)
    (hv : ∀ j, (1 : ℝ) / 10 ≤ v j)
    (hT : ∀ k j, |T k j| ≤ 1) :
    EntryNonneg (simplexRight v T ((1 : ℝ) / 11491200) ((1 : ℝ) / 15120)) := by
  intro a j
  have hs := abs_sum_eighteen_le hcard (fun k => T k j) 1 (fun k => hT k j)
  have hslo := (abs_le.mp hs).1
  have hshi := (abs_le.mp hs).2
  cases a with
  | some k =>
    have htlo := (abs_le.mp (hT k j)).1
    simp only [simplexRight]
    norm_num [hcard]
    nlinarith [hv j]
  | none =>
    simp only [simplexRight]
    norm_num [hcard]
    nlinarith [hv j]

end MatCKronecker
