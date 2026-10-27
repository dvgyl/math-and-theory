module

/- Source attribution: MathAndTheory/Mathematics/GyiresCirculant5/PROVENANCE.md. -/

public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.Basic.Real.Basic

/-!
# Gyires's permanent inequality for circulant matrices of order five

All matrices are real `5 × 5` matrices indexed by `Fin 5`, whose arithmetic is arithmetic
modulo five. `A.permanent` is Mathlib's permanent `∑ σ, ∏ i, A (σ i) i`, `Aᵀ` is the transpose,
and `doublyStochastic ℝ (Fin 5)` is the set of doubly stochastic matrices: nonnegative entries,
every row sum and every column sum equal to `1`. Mathlib's `Matrix.circulant v` is the circulant
matrix with entries `circulant v i j = v (i - j)`; a matrix is *circulant* if it equals
`circulant v` for some `v : Fin 5 → ℝ`, its vector of *weights*. The real number
`(Nat.factorial 5 : ℝ) / 5 ^ 5 = 24/625` is `n!/nⁿ` for `n = 5`, and `J₅`, the matrix with every
entry `1/5`, is `of fun _ _ => 5⁻¹`.

**Source.** B. Gyires (*On permanent inequalities*, Colloq. Math. Soc. János Bolyai 18,
North-Holland, 1978, 471–484) conjectured that every doubly stochastic `n × n` matrix `A`
satisfies
`4 per(A)² / (per(A Aᵀ) + per(Aᵀ A) + 2 per(A²)) ≥ n!/nⁿ`,
with equality only at the matrix `Jₙ` all of whose entries are `1/n`. This is Conjecture 20 in
G.-S. Cheon and I. M. Wanless, *An update on Minc's survey of open problems involving
permanents*, Linear Algebra Appl. 403 (2005), 314–342, where the transpose is a conjugate
transpose; for real matrices the two agree. The conjecture is open in general. The theorems
below prove it for every doubly stochastic circulant matrix of order five, a four-parameter
family, together with a stronger inequality for all nonnegative circulants of order five.

* `gyires_ratio`, `gyires_ratio_eq_iff`, `gyires_denominator_pos`: the conjectured inequality,
  its equality case and the positivity of the denominator, for doubly stochastic circulants.
* `gyires_homogeneous`, `gyires_homogeneous_eq_iff`: the same inequality, multiplied out, for
  every circulant with nonnegative entries (no normalization); equality holds exactly for the
  constant matrices.
* `strong_inequality`, `strong_inequality_eq_iff`: the stronger inequality
  `(5!/5⁵) per(A Aᵀ) ≤ per(A)²` for circulants with nonnegative entries, with equality exactly
  for the constant matrices. Since `A Aᵀ = Aᵀ A` and `per(A²) ≤ per(A Aᵀ)` for every real
  circulant `A`, it implies the homogeneous form.
* `strong_margin`, `strong_margin_attained`, `strong_margin_sharp`: a quantitative form. If the
  weights are nonnegative and `σ` sorts them, `v (σ 0) ≤ v (σ 1) ≤ ⋯ ≤ v (σ 4)`, then
  `625 per(A)² - 24 per(A Aᵀ) ≥ 484 ∑ⱼ (v (σ (j+1)) - v (σ j))¹⁰`; equality holds for some
  weights with nonzero gaps, and `484` is the largest constant for which the inequality holds.

Context: the research area is inequalities for permanents of doubly stochastic matrices, the
setting of van der Waerden's permanent conjecture (proved independently by Gyires, by Egorychev
and by Falikman in 1980–1981) and of the open problems collected in Minc's surveys of
permanents. Gyires's conjecture is elementary for `n = 2`; the inequality for `n = 3` was proved
by D. K. Chang (Linear Multilinear Algebra 26 (1990), 207–213), and a computer-assisted proof
for `n = 4`, formalized in Lean with its finite certificate checked by `native_decide` and not
peer reviewed, was given by C. Ozols in 2026 (https://github.com/cozuya/gyires-permanent-4x4). The order-five case is open;
the results here cover its circulant matrices, which are the convex combinations of the five
powers of the cyclic permutation matrix.
-/

public section

namespace MathAndTheory.GyiresCirculant5

open Matrix

/-- **Gyires's inequality for doubly stochastic circulants of order five.** If `A` is a doubly
stochastic circulant `5 × 5` matrix, then
`4 per(A)² / (per(A Aᵀ) + per(Aᵀ A) + 2 per(A²)) ≥ 5!/5⁵ = 24/625`. -/
theorem gyires_ratio (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin 5))
    (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    (Nat.factorial 5 : ℝ) / 5 ^ 5 ≤
      4 * A.permanent ^ 2 /
        ((A * Aᵀ).permanent + (Aᵀ * A).permanent + 2 * (A * A).permanent) := by
  sorry

/-- **The equality case.** For a doubly stochastic circulant `A` of order five, the ratio of
`gyires_ratio` equals `5!/5⁵` if and only if `A = J₅`, the matrix with every entry `1/5`. -/
theorem gyires_ratio_eq_iff (A : Matrix (Fin 5) (Fin 5) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin 5)) (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    4 * A.permanent ^ 2 /
        ((A * Aᵀ).permanent + (Aᵀ * A).permanent + 2 * (A * A).permanent) =
      (Nat.factorial 5 : ℝ) / 5 ^ 5 ↔
      A = of fun _ _ => (5 : ℝ)⁻¹ := by
  sorry

/-- The denominator `per(A Aᵀ) + per(Aᵀ A) + 2 per(A²)` of Gyires's ratio is positive for every
doubly stochastic circulant `A` of order five, so the quotient in `gyires_ratio` is never a
division by zero (which Lean defines to be `0`). -/
theorem gyires_denominator_pos (A : Matrix (Fin 5) (Fin 5) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin 5)) (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    0 < (A * Aᵀ).permanent + (Aᵀ * A).permanent + 2 * (A * A).permanent := by
  sorry

/-- **The homogeneous form.** Every circulant `5 × 5` matrix `A` with nonnegative entries
satisfies `(5!/5⁵) (per(A Aᵀ) + per(Aᵀ A) + 2 per(A²)) ≤ 4 per(A)²`. No normalization of the
row sums is assumed. -/
theorem gyires_homogeneous (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    (Nat.factorial 5 : ℝ) / 5 ^ 5 *
        ((A * Aᵀ).permanent + (Aᵀ * A).permanent + 2 * (A * A).permanent) ≤
      4 * A.permanent ^ 2 := by
  sorry

/-- Equality holds in `gyires_homogeneous` if and only if `A` is a constant matrix, that is, all
five circulant weights are equal (this includes `A = 0`). -/
theorem gyires_homogeneous_eq_iff (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    (Nat.factorial 5 : ℝ) / 5 ^ 5 *
        ((A * Aᵀ).permanent + (Aᵀ * A).permanent + 2 * (A * A).permanent) =
      4 * A.permanent ^ 2 ↔
      ∃ c : ℝ, A = of fun _ _ => c := by
  sorry

/-- **The strong inequality.** Every circulant `5 × 5` matrix `A` with nonnegative entries
satisfies `(5!/5⁵) per(A Aᵀ) ≤ per(A)²`, that is, `24 per(A Aᵀ) ≤ 625 per(A)²`. -/
theorem strong_inequality (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    (Nat.factorial 5 : ℝ) / 5 ^ 5 * (A * Aᵀ).permanent ≤ A.permanent ^ 2 := by
  sorry

/-- Equality holds in `strong_inequality` if and only if `A` is a constant matrix. -/
theorem strong_inequality_eq_iff (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hcirc : ∃ v : Fin 5 → ℝ, A = circulant v) :
    (Nat.factorial 5 : ℝ) / 5 ^ 5 * (A * Aᵀ).permanent = A.permanent ^ 2 ↔
      ∃ c : ℝ, A = of fun _ _ => c := by
  sorry

/-- **The margin in sorted-gap coordinates.** Let `v` be a nonnegative weight vector and `σ` a
permutation that sorts it, `v (σ 0) ≤ ⋯ ≤ v (σ 4)`. Then the defect of the strong inequality for
`A = circulant v` is at least `484` times the sum of the tenth powers of the four gaps
`v (σ (j+1)) - v (σ j)` between consecutive sorted weights. -/
theorem strong_margin (v : Fin 5 → ℝ) (hv : ∀ i, 0 ≤ v i) (σ : Equiv.Perm (Fin 5))
    (hσ : Monotone (v ∘ σ)) :
    484 * ∑ j : Fin 4, (v (σ j.succ) - v (σ j.castSucc)) ^ 10 ≤
      625 * (circulant v).permanent ^ 2 - 24 * (circulant v * (circulant v)ᵀ).permanent := by
  sorry

/-- **The margin is attained.** There are a nonnegative weight vector `v` and a permutation `σ`
that sorts it for which the tenth powers of the gaps add up to `1` and the defect
`625 per(A)² - 24 per(A Aᵀ)` of `A = circulant v` equals `484`; for instance
`v = (1, 1, 0, 0, 0)`. -/
theorem strong_margin_attained :
    ∃ v : Fin 5 → ℝ, (∀ i, 0 ≤ v i) ∧ ∃ σ : Equiv.Perm (Fin 5), Monotone (v ∘ σ) ∧
      ∑ j : Fin 4, (v (σ j.succ) - v (σ j.castSucc)) ^ 10 = 1 ∧
      625 * (circulant v).permanent ^ 2 - 24 * (circulant v * (circulant v)ᵀ).permanent = 484 := by
  sorry

/-- **The constant `484` is sharp.** If a constant `K` satisfies the inequality of
`strong_margin` for every nonnegative weight vector and every permutation that sorts it, then
`K ≤ 484`. -/
theorem strong_margin_sharp (K : ℝ)
    (hK : ∀ v : Fin 5 → ℝ, (∀ i, 0 ≤ v i) → ∀ σ : Equiv.Perm (Fin 5), Monotone (v ∘ σ) →
      K * ∑ j : Fin 4, (v (σ j.succ) - v (σ j.castSucc)) ^ 10 ≤
        625 * (circulant v).permanent ^ 2 - 24 * (circulant v * (circulant v)ᵀ).permanent) :
    K ≤ 484 := by
  sorry

end MathAndTheory.GyiresCirculant5

/-!
The following statements cover doubly stochastic matrices of any order with at most two
distinct row vectors and two distinct column vectors. Unequal class sizes, zero entries,
and orders zero and one are included.
-/

namespace MathAndTheory.GyiresFourBlock

noncomputable def rowVectorCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℕ := by
  classical
  exact (Finset.univ.image (fun i => fun j => A i j)).card

noncomputable def columnVectorCount {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℕ := by
  classical
  exact (Finset.univ.image (fun j => fun i => A i j)).card

theorem contractions {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hrow : rowVectorCount A ≤ 2) (hcol : columnVectorCount A ≤ 2) :
    (A * A.transpose).permanent ≤ A.permanent ∧
      (A.transpose * A).permanent ≤ A.permanent ∧ (A * A).permanent ≤ A.permanent := by
  sorry

theorem margin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hrow : rowVectorCount A ≤ 2) (hcol : columnVectorCount A ≤ 2) :
    4 * A.permanent * (A.permanent - (Nat.factorial n : ℝ) / (n : ℝ)^n) ≤
      4 * A.permanent^2 - (Nat.factorial n : ℝ) / (n : ℝ)^n *
        ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) ∧
    0 ≤ 4 * A.permanent * (A.permanent - (Nat.factorial n : ℝ) / (n : ℝ)^n) := by
  sorry

theorem gyires {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hrow : rowVectorCount A ≤ 2) (hcol : columnVectorCount A ≤ 2) :
    (Nat.factorial n : ℝ) / (n : ℝ)^n *
      ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) ≤
        4 * A.permanent^2 := by
  sorry

theorem gyires_eq_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hrow : rowVectorCount A ≤ 2) (hcol : columnVectorCount A ≤ 2) :
    (Nat.factorial n : ℝ) / (n : ℝ)^n *
      ((A * A.transpose).permanent + (A.transpose * A).permanent + 2 * (A * A).permanent) =
        4 * A.permanent^2 ↔ A = fun _ _ => 1 / (n : ℝ) := by
  sorry

end MathAndTheory.GyiresFourBlock

namespace MathAndTheory.GyiresExceptional

def HasExceptionalVector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∃ e, ∀ i j k, j ≠ e → k ≠ e → A i j = A i k) ∨
    (∃ e, ∀ i j k, j ≠ e → k ≠ e → A j i = A k i)

theorem strong {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (he : HasExceptionalVector A)
    (hn : 2 ≤ n) :
    ((Nat.factorial n : ℝ) / (n : ℝ)^n) * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      ((Nat.factorial n : ℝ) / (n : ℝ)^n) * (A.transpose*A).permanent ≤ A.permanent^2 := by
  sorry

theorem gram_eq_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (he : HasExceptionalVector A)
    (hn : 2 ≤ n) :
    (((Nat.factorial n : ℝ) / (n : ℝ)^n) * (A*A.transpose).permanent = A.permanent^2 ↔
      A = fun _ _ => 1 / (n : ℝ)) ∧
    (((Nat.factorial n : ℝ) / (n : ℝ)^n) * (A.transpose*A).permanent = A.permanent^2 ↔
      A = fun _ _ => 1 / (n : ℝ)) := by
  sorry

theorem gyires {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (he : HasExceptionalVector A)
    (hn : 2 ≤ n) :
    ((Nat.factorial n : ℝ) / (n : ℝ)^n) *
      ((A*A.transpose).permanent + (A.transpose*A).permanent + 2*(A*A).permanent) ≤
        4*A.permanent^2 := by
  sorry

theorem gyires_eq_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (he : HasExceptionalVector A)
    (hn : 2 ≤ n) :
    ((Nat.factorial n : ℝ) / (n : ℝ)^n) *
      ((A*A.transpose).permanent + (A.transpose*A).permanent + 2*(A*A).permanent) =
        4*A.permanent^2 ↔ A = fun _ _ => 1 / (n : ℝ) := by
  sorry

end MathAndTheory.GyiresExceptional
