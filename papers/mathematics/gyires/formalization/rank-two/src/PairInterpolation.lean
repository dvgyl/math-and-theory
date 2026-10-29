module

public import MathAndTheory.Mathematics.Gyires.BernoulliMaximizer
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.Gyires.RankTwo

open Bernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complete law of the sum of the Bernoulli variables. -/
def law (p : ι → ℝ) : Fin (Fintype.card ι + 1) → ℝ :=
  fun k => probability p k

lemma continuous_law : Continuous (law (ι := ι)) := by
  apply continuous_pi
  intro k
  simp only [law, probability_eq_expectation]
  exact continuous_expectation _

lemma law_pair_formula (p : ι → ℝ) {i j : ι} (hij : i ≠ j)
    (x y : ℝ) (k : Fin (Fintype.card ι + 1)) :
    law (setPair p i j x y) k = law (setPair p i j 0 0) k +
      (law (setPair p i j 1 0) k - law (setPair p i j 0 0) k) * (x + y) +
      (law (setPair p i j 1 1) k - 2 * law (setPair p i j 1 0) k +
        law (setPair p i j 0 0) k) * x * y := by
  simp only [law, probability_eq_expectation]
  exact expectation_pair_formula _ p hij x y

lemma law_pair_interpolation (p : ι → ℝ) {i j : ι} (hij : i ≠ j)
    (x y r t α β : ℝ) (hxy : x + y = p i + p j)
    (hrt : r + t = p i + p j) (hsum : α + β = 1)
    (hprod : α * (x * y) + β * (r * t) = p i * p j) :
    law p = α • law (setPair p i j x y) + β • law (setPair p i j r t) := by
  ext k
  have hp := law_pair_formula p hij (p i) (p j) k
  rw [setPair_self] at hp
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hp, law_pair_formula p hij x y k, law_pair_formula p hij r t k, hxy, hrt]
  calc
    _ = (α + β) * (law (setPair p i j 0 0) k +
          (law (setPair p i j 1 0) k - law (setPair p i j 0 0) k) * (p i + p j)) +
        (law (setPair p i j 1 1) k - 2 * law (setPair p i j 1 0) k +
          law (setPair p i j 0 0) k) * (α * (x * y) + β * (r * t)) := by
      rw [hsum, hprod]
      ring
    _ = _ := by ring

/-- An unequal interior pair is a strict mixture of an equal pair and a boundary pair. -/
lemma exists_strict_pair_interpolation {a b : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hab : a ≠ b) :
    ∃ x y m α β : ℝ,
      (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1) ∧ (0 ≤ m ∧ m ≤ 1) ∧
      x + y = a + b ∧ m + m = a + b ∧
      0 < α ∧ 0 < β ∧ α + β = 1 ∧
      α * (x * y) + β * (m * m) = a * b ∧
      a ^ 2 + b ^ 2 < x ^ 2 + y ^ 2 := by
  obtain ⟨x, y, hx, hy, hxy, hspread⟩ := exists_pair_spread ha hb
  let m := (a + b) / 2
  have hm : 0 ≤ m ∧ m ≤ 1 := by dsimp [m]; constructor <;> linarith
  have hmsum : m + m = a + b := by dsimp [m]; ring
  have hlow : x * y < a * b := by
    have hsq : (x + y) ^ 2 = (a + b) ^ 2 := congrArg (fun z : ℝ => z ^ 2) hxy
    nlinarith
  have hhigh : a * b < m * m := by
    dsimp [m]
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hab)]
  have hden : 0 < m * m - x * y := by linarith
  let α := (m * m - a * b) / (m * m - x * y)
  let β := (a * b - x * y) / (m * m - x * y)
  have hα : 0 < α := div_pos (sub_pos.mpr hhigh) hden
  have hβ : 0 < β := div_pos (sub_pos.mpr hlow) hden
  refine ⟨x, y, m, α, β, hx, hy, hm, hxy, hmsum, hα, hβ, ?_, ?_, hspread⟩
  · dsimp [α, β]
    rw [← add_div]
    have hnum : (m*m-a*b)+(a*b-x*y) = m*m-x*y := by ring
    rw [hnum, div_self (ne_of_gt hden)]
  · dsimp [α, β]
    calc
      _ = ((m*m-a*b)*(x*y)+(a*b-x*y)*(m*m))/(m*m-x*y) := by ring
      _ = a*b := (div_eq_iff (ne_of_gt hden)).mpr (by ring)

end MathAndTheory.Gyires.RankTwo
