module

public import MatCKronecker.SimplexFactorization

@[expose] public section

namespace MatCKronecker

open Matrix
open scoped BigOperators

variable {m n q : Type*} [Fintype q]

/-- The elementary absolute-sum bound, including an empty index type. -/
theorem simplex_abs_sum_le_card_mul (f : q → ℝ) (b : ℝ)
    (hf : ∀ k, |f k| ≤ b) :
    |∑ k, f k| ≤ (Fintype.card q : ℝ) * b := by
  classical
  calc
    |∑ k, f k| ≤ ∑ k, |f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : q, b := Finset.sum_le_sum fun k _ => hf k
    _ = (Fintype.card q : ℝ) * b := by simp

/-- Uniform entrywise nonnegativity of the simplex columns for every positive
number of perturbation coordinates. -/
theorem simplexLeft_nonneg_uniform (hq : 0 < Fintype.card q)
    (u : m → ℝ) (R : Matrix m q ℝ)
    (hu : ∀ i, (1 : ℝ) / 36 ≤ u i)
    (hR : ∀ i k, |R i k| ≤ 17) :
    EntryNonneg (simplexLeft u R ((1 : ℝ) / (840 * (Fintype.card q : ℝ)))) := by
  classical
  let Q : ℝ := Fintype.card q
  let eta : ℝ := 1 / (840 * Q)
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast hq
  have hQone : 1 ≤ Q := by
    dsimp [Q]
    exact_mod_cast (Nat.succ_le_of_lt hq)
  have hQne : Q ≠ 0 := ne_of_gt hQ
  have heta : 0 ≤ eta := by dsimp [eta]; positivity
  have hvalue : eta * (17 * Q) = 17 / 840 := by
    dsimp [eta]
    field_simp
  intro i a
  cases a with
  | some k =>
    have hl := (abs_le.mp (hR i k)).1
    have hl' : -(17 * Q) ≤ R i k := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hl' heta
    change 0 ≤ u i + eta * R i k
    nlinarith [hu i]
  | none =>
    have hs := simplex_abs_sum_le_card_mul (R i) 17 (hR i)
    have hh := (abs_le.mp hs).2
    change (∑ k, R i k) ≤ Q * 17 at hh
    have hp := mul_le_mul_of_nonneg_left hh heta
    change 0 ≤ u i - eta * ∑ k, R i k
    nlinarith [hu i]

/-- Uniform entrywise nonnegativity of the matching simplex rows. The scale
ratio is exactly `1 / (40 * (card q + 1))`. -/
theorem simplexRight_nonneg_uniform (hq : 0 < Fintype.card q)
    (v : n → ℝ) (T : Matrix q n ℝ)
    (hv : ∀ j, (1 : ℝ) / 10 ≤ v j)
    (hT : ∀ k j, |T k j| ≤ 1) :
    EntryNonneg (simplexRight v T
      ((1 : ℝ) / (33600 * (Fintype.card q : ℝ) * ((Fintype.card q : ℝ) + 1)))
      ((1 : ℝ) / (840 * (Fintype.card q : ℝ)))) := by
  classical
  let Q : ℝ := Fintype.card q
  let eta : ℝ := 1 / (840 * Q)
  let eps : ℝ := 1 / (33600 * Q * (Q + 1))
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast hq
  have hQne : Q ≠ 0 := ne_of_gt hQ
  have hQone : 0 < Q + 1 := by positivity
  have hQone_ne : Q + 1 ≠ 0 := ne_of_gt hQone
  have hratio : eps / eta = 1 / (40 * (Q + 1)) := by
    dsimp [eps, eta]
    field_simp
    norm_num
  intro a j
  have hs := simplex_abs_sum_le_card_mul (fun k => T k j) 1 (fun k => hT k j)
  have hshi := (abs_le.mp hs).2
  have hsumdiv : (∑ k, T k j) / (Q + 1) ≤ 1 := by
    apply (div_le_iff₀ hQone).2
    change (∑ k, T k j) ≤ Q * 1 at hshi
    nlinarith
  cases a with
  | some k =>
    have htlo := (abs_le.mp (hT k j)).1
    change 0 ≤ v j / (Q + 1) + (eps / eta) *
      (T k j - (∑ l, T l j) / (Q + 1))
    rw [hratio]
    have hid : v j / (Q + 1) + (1 / (40 * (Q + 1))) *
        (T k j - (∑ l, T l j) / (Q + 1)) =
        (40 * v j + T k j - (∑ l, T l j) / (Q + 1)) / (40 * (Q + 1)) := by
      field_simp
      ring
    rw [hid]
    apply div_nonneg
    · nlinarith [hv j]
    · positivity
  | none =>
    change 0 ≤ v j / (Q + 1) - (eps / eta) *
      ((∑ l, T l j) / (Q + 1))
    rw [hratio]
    have hid : v j / (Q + 1) - (1 / (40 * (Q + 1))) *
        ((∑ l, T l j) / (Q + 1)) =
        (40 * v j - (∑ l, T l j) / (Q + 1)) / (40 * (Q + 1)) := by
      field_simp
    rw [hid]
    apply div_nonneg
    · nlinarith [hv j]
    · positivity

end MatCKronecker
