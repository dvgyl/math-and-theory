module

public import PositiveCore.Absorption

@[expose] public section

namespace PositiveCore

open Matrix MatCKronecker
open scoped BigOperators

variable {m n p q : Type*} [Fintype p] [Fintype q] [DecidableEq q]

/-- Unused paired directions of the two factors absorb a factored perturbation
without adding factorization terms.  The two cross terms vanish separately. -/
theorem nullspace_absorption_identity
    (U : Matrix m p ℝ) (V : Matrix p n ℝ)
    (X : Matrix m q ℝ) (Y : Matrix q n ℝ)
    (W : Matrix q p ℝ) (Z : Matrix p q ℝ)
    (hUZ : U * Z = 0) (hWV : W * V = 0) (hWZ : W * Z = 1) :
    (U + X * W) * (V + Z * Y) = U * V + X * Y := by
  simp only [Matrix.add_mul, Matrix.mul_add]
  rw [← Matrix.mul_assoc U Z Y, hUZ, Matrix.zero_mul,
    Matrix.mul_assoc X W V, hWV, Matrix.mul_zero,
    Matrix.mul_assoc X W (Z * Y), ← Matrix.mul_assoc W Z Y,
    hWZ, Matrix.one_mul]
  simp

/-- The algebraic nullspace criterion produces an actual factorization of the
same width whenever the perturbed factors remain entrywise nonnegative. -/
theorem nullspace_absorption
    (U : Matrix m p ℝ) (V : Matrix p n ℝ)
    (X : Matrix m q ℝ) (Y : Matrix q n ℝ)
    (W : Matrix q p ℝ) (Z : Matrix p q ℝ)
    (hUZ : U * Z = 0) (hWV : W * V = 0) (hWZ : W * Z = 1)
    (hleft : EntryNonneg (U + X * W))
    (hright : EntryNonneg (V + Z * Y)) :
    HasNMF (U * V + X * Y) (Fintype.card p) :=
  hasNMF_of_factorization _ _ hleft hright
    (nullspace_absorption_identity U V X Y W Z hUZ hWV hWZ)

/-- Independent balancing of the two sides permits a signed perturbation
parameter without changing the frame or the latent dimension. -/
theorem nullspace_scaled_absorption_identity
    (U : Matrix m p ℝ) (V : Matrix p n ℝ)
    (X : Matrix m q ℝ) (Y : Matrix q n ℝ)
    (W : Matrix q p ℝ) (Z : Matrix p q ℝ)
    (hUZ : U * Z = 0) (hWV : W * V = 0) (hWZ : W * Z = 1)
    (eps eta : ℝ) (heta : eta ≠ 0) :
    (U + eta • (X * W)) * (V + (eps / eta) • (Z * Y)) =
      U * V + eps • (X * Y) := by
  have hc : eta * (eps / eta) = eps := by field_simp
  have hc' : (eps / eta) * eta = eps := div_mul_cancel₀ eps heta
  simpa only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, hc'] using
    nullspace_absorption_identity U V (eta • X) ((eps / eta) • Y)
      W Z hUZ hWV hWZ

/-- An elementary entrywise product estimate with no norm convention hidden in
the statement.  Empty intermediate types are included. -/
theorem abs_mul_entry_le
    (A : Matrix m q ℝ) (B : Matrix q n ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hA : ∀ i k, |A i k| ≤ a) (hB : ∀ k j, |B k j| ≤ b)
    (i : m) (j : n) :
    |(A * B) i j| ≤ (Fintype.card q : ℝ) * a * b := by
  classical
  rw [Matrix.mul_apply]
  calc
    |∑ k, A i k * B k j| ≤ ∑ k, |A i k * B k j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : q, a * b := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) ha
    _ = (Fintype.card q : ℝ) * a * b := by simp [mul_assoc]

/-- Explicit budgets ensure the nonnegativity of the perturbed factors. -/
theorem nullspace_absorption_bounded
    (U : Matrix m p ℝ) (V : Matrix p n ℝ)
    (X : Matrix m q ℝ) (Y : Matrix q n ℝ)
    (W : Matrix q p ℝ) (Z : Matrix p q ℝ)
    (hUZ : U * Z = 0) (hWV : W * V = 0) (hWZ : W * Z = 1)
    (alpha beta x y w z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) (hz : 0 ≤ z)
    (hU : ∀ i k, alpha ≤ U i k) (hV : ∀ k j, beta ≤ V k j)
    (hX : ∀ i k, |X i k| ≤ x) (hY : ∀ k j, |Y k j| ≤ y)
    (hW : ∀ k j, |W k j| ≤ w) (hZ : ∀ i k, |Z i k| ≤ z)
    (hleft : (Fintype.card q : ℝ) * x * w ≤ alpha)
    (hright : (Fintype.card q : ℝ) * z * y ≤ beta) :
    HasNMF (U * V + X * Y) (Fintype.card p) := by
  apply nullspace_absorption U V X Y W Z hUZ hWV hWZ
  · intro i j
    have hh := (abs_le.mp (abs_mul_entry_le X W x w hx hw hX hW i j)).1
    simp only [Matrix.add_apply]
    linarith [hU i j]
  · intro i j
    have hh := (abs_le.mp (abs_mul_entry_le Z Y z y hz hy hZ hY i j)).1
    simp only [Matrix.add_apply]
    linarith [hV i j]

/-- The corresponding actual nonnegative-rank bound. -/
theorem nullspace_nnrank_le
    (U : Matrix m p ℝ) (V : Matrix p n ℝ)
    (X : Matrix m q ℝ) (Y : Matrix q n ℝ)
    (W : Matrix q p ℝ) (Z : Matrix p q ℝ)
    (hUZ : U * Z = 0) (hWV : W * V = 0) (hWZ : W * Z = 1)
    (hleft : EntryNonneg (U + X * W))
    (hright : EntryNonneg (V + Z * Y)) :
    nnrank (U * V + X * Y) ≤ Fintype.card p :=
  nnrank_le_of_hasNMF (nullspace_absorption U V X Y W Z hUZ hWV hWZ hleft hright)

end PositiveCore
