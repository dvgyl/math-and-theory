module

public import MatCKronecker.SimplexUniform
public import MatCKronecker.BasicFactorizations

@[expose] public section

namespace PositiveCore

open Matrix MatCKronecker
open scoped BigOperators

variable {m n q : Type*} [Fintype q]

/-- The exact inequalities for nonnegative simplex columns.  These inequalities
allow zeros outside the support of the positive core and require no global
strict positivity. -/
theorem simplexLeft_nonneg_iff (u : m → ℝ) (R : Matrix m q ℝ) (eta : ℝ) :
    EntryNonneg (simplexLeft u R eta) ↔
      (∀ i k, -u i ≤ eta * R i k) ∧
      (∀ i, eta * (∑ k, R i k) ≤ u i) := by
  constructor
  · intro h
    constructor
    · intro i k
      have hk := h i (some k)
      simp only [simplexLeft] at hk
      linarith
    · intro i
      have hi := h i none
      simp only [simplexLeft] at hi
      linarith
  · rintro ⟨hcols, hlast⟩ i a
    cases a with
    | some k =>
      simp only [simplexLeft]
      linarith [hcols i k]
    | none =>
      simp only [simplexLeft]
      linarith [hlast i]

/-- The exact inequalities for nonnegative simplex rows.  They impose no
unnecessary sign constraint on the perturbation parameter. -/
theorem simplexRight_nonneg_iff (v : n → ℝ) (T : Matrix q n ℝ)
    (eps eta : ℝ) :
    EntryNonneg (simplexRight v T eps eta) ↔
      (∀ j, (eps / eta) * (∑ k, T k j) ≤ v j) ∧
      (∀ k j, (eps / eta) *
        ((∑ l, T l j) - ((Fintype.card q : ℝ) + 1) * T k j) ≤ v j) := by
  classical
  let Q : ℝ := Fintype.card q
  have hc : 0 < Q + 1 := by dsimp [Q]; positivity
  have hcne : Q + 1 ≠ 0 := ne_of_gt hc
  have hnone (j : n) :
      (Q + 1) * simplexRight v T eps eta none j =
        v j - (eps / eta) * (∑ k, T k j) := by
    simp only [simplexRight]
    change (Q + 1) * (v j / (Q + 1) - (eps / eta) *
      ((∑ k, T k j) / (Q + 1))) = _
    generalize eps / eta = rho
    field_simp <;> ring
  have hsome (k : q) (j : n) :
      (Q + 1) * simplexRight v T eps eta (some k) j =
        v j - (eps / eta) * ((∑ l, T l j) - (Q + 1) * T k j) := by
    simp only [simplexRight]
    change (Q + 1) * (v j / (Q + 1) + (eps / eta) *
      (T k j - (∑ l, T l j) / (Q + 1))) = _
    generalize eps / eta = rho
    field_simp <;> ring
  constructor
  · intro h
    constructor
    · intro j
      have hh := mul_nonneg hc.le (h none j)
      rw [hnone] at hh
      linarith
    · intro k j
      have hh := mul_nonneg hc.le (h (some k) j)
      rw [hsome] at hh
      change (eps / eta) * ((∑ l, T l j) - (Q + 1) * T k j) ≤ v j
      linarith
  · rintro ⟨hn, hs⟩ a j
    apply (nonneg_of_mul_nonneg_right ?_ hc)
    cases a with
    | none =>
      rw [hnone]
      linarith [hn j]
    | some k =>
      rw [hsome]
      have hh := hs k j
      change (eps / eta) * ((∑ l, T l j) - (Q + 1) * T k j) ≤ v j at hh
      linarith

/-- A support-sensitive absorption criterion.  Every hypothesis is an explicit
coordinate inequality and the conclusion is an actual real nonnegative
factorization, not a surrogate notion of rank. -/
theorem absorption_of_coordinates
    (u : m → ℝ) (v : n → ℝ) (R : Matrix m q ℝ) (T : Matrix q n ℝ)
    (eps eta : ℝ) (heta : eta ≠ 0)
    (hLsome : ∀ i k, -u i ≤ eta * R i k)
    (hLnone : ∀ i, eta * (∑ k, R i k) ≤ u i)
    (hRnone : ∀ j, (eps / eta) * (∑ k, T k j) ≤ v j)
    (hRsome : ∀ k j, (eps / eta) *
      ((∑ l, T l j) - ((Fintype.card q : ℝ) + 1) * T k j) ≤ v j) :
    HasNMF (vecMulVec u v + eps • (R * T)) (Fintype.card q + 1) := by
  have hL := (simplexLeft_nonneg_iff u R eta).mpr ⟨hLsome, hLnone⟩
  have hR := (simplexRight_nonneg_iff v T eps eta).mpr ⟨hRnone, hRsome⟩
  simpa using hasNMF_of_factorization _ _ hL hR
    (simplex_factorization u v R T eps eta heta)

/-- Uniform nonnegativity of the left factor with arbitrary baseline and scale. -/
theorem simplexLeft_nonneg_bounded (hq : 0 < Fintype.card q)
    (u : m → ℝ) (R : Matrix m q ℝ) (alpha a eta : ℝ)
    (ha : 0 ≤ a) (heta : 0 ≤ eta)
    (hu : ∀ i, alpha ≤ u i) (hR : ∀ i k, |R i k| ≤ a)
    (hbudget : eta * (Fintype.card q : ℝ) * a ≤ alpha) :
    EntryNonneg (simplexLeft u R eta) := by
  have hQ : (1 : ℝ) ≤ Fintype.card q := by
    exact_mod_cast (Nat.succ_le_of_lt hq)
  apply (simplexLeft_nonneg_iff u R eta).mpr
  constructor
  · intro i k
    have hlow := (abs_le.mp (hR i k)).1
    have hmul := mul_le_mul_of_nonneg_left hlow heta
    have hqa : a ≤ (Fintype.card q : ℝ) * a := by nlinarith
    have hmul' := mul_le_mul_of_nonneg_left hqa heta
    nlinarith [hu i]
  · intro i
    have hs := (abs_le.mp (simplex_abs_sum_le_card_mul (R i) a (hR i))).2
    have hm := mul_le_mul_of_nonneg_left hs heta
    nlinarith [hu i]

/-- Uniform nonnegativity of the right factor.  The signed perturbation is
controlled through its absolute value, so the result is two-sided. -/
theorem simplexRight_nonneg_bounded
    (v : n → ℝ) (T : Matrix q n ℝ) (beta b eps eta : ℝ)
    (hb : 0 ≤ b) (hv : ∀ j, beta ≤ v j)
    (hT : ∀ k j, |T k j| ≤ b)
    (hbudget : |eps / eta| * (2 * (Fintype.card q : ℝ) + 1) * b ≤ beta) :
    EntryNonneg (simplexRight v T eps eta) := by
  classical
  let Q : ℝ := Fintype.card q
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hc : 0 ≤ Q + 1 := by positivity
  have hsum (j : n) : |∑ k, T k j| ≤ Q * b :=
    simplex_abs_sum_le_card_mul (fun k => T k j) b (fun k => hT k j)
  apply (simplexRight_nonneg_iff v T eps eta).mpr
  constructor
  · intro j
    have he : 0 ≤ |eps / eta| := abs_nonneg _
    calc
      (eps / eta) * (∑ k, T k j) ≤ |(eps / eta) * (∑ k, T k j)| := le_abs_self _
      _ = |eps / eta| * |∑ k, T k j| := abs_mul _ _
      _ ≤ |eps / eta| * (Q * b) := mul_le_mul_of_nonneg_left (hsum j) he
      _ ≤ |eps / eta| * ((2 * Q + 1) * b) := by
        apply mul_le_mul_of_nonneg_left _ he
        nlinarith
      _ ≤ beta := by simpa only [Q, mul_assoc] using hbudget
      _ ≤ v j := hv j
  · intro k j
    have hbnd : |(∑ l, T l j) - (Q + 1) * T k j| ≤ (2 * Q + 1) * b := by
      calc
        |(∑ l, T l j) - (Q + 1) * T k j| ≤
            |∑ l, T l j| + |(Q + 1) * T k j| := abs_sub _ _
        _ = |∑ l, T l j| + (Q + 1) * |T k j| := by
          rw [abs_mul, abs_of_nonneg hc]
        _ ≤ Q * b + (Q + 1) * b :=
          add_le_add (hsum j) (mul_le_mul_of_nonneg_left (hT k j) hc)
        _ = (2 * Q + 1) * b := by ring
    change (eps / eta) * ((∑ l, T l j) - (Q + 1) * T k j) ≤ v j
    calc
      (eps / eta) * ((∑ l, T l j) - (Q + 1) * T k j) ≤
          |(eps / eta) * ((∑ l, T l j) - (Q + 1) * T k j)| := le_abs_self _
      _ = |eps / eta| * |(∑ l, T l j) - (Q + 1) * T k j| := abs_mul _ _
      _ ≤ |eps / eta| * ((2 * Q + 1) * b) :=
        mul_le_mul_of_nonneg_left hbnd (abs_nonneg _)
      _ ≤ beta := by simpa only [Q, mul_assoc] using hbudget
      _ ≤ v j := hv j

/-- Quantitative simplex absorption, with arbitrary positive baselines and
arbitrary signed low-rank factors. -/
theorem absorption_bounded (hq : 0 < Fintype.card q)
    (u : m → ℝ) (v : n → ℝ) (R : Matrix m q ℝ) (T : Matrix q n ℝ)
    (alpha beta a b eps eta : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (heta : 0 < eta)
    (hu : ∀ i, alpha ≤ u i) (hv : ∀ j, beta ≤ v j)
    (hR : ∀ i k, |R i k| ≤ a) (hT : ∀ k j, |T k j| ≤ b)
    (hleft : eta * (Fintype.card q : ℝ) * a ≤ alpha)
    (hright : |eps / eta| * (2 * (Fintype.card q : ℝ) + 1) * b ≤ beta) :
    HasNMF (vecMulVec u v + eps • (R * T)) (Fintype.card q + 1) := by
  have hL := simplexLeft_nonneg_bounded hq u R alpha a eta ha heta.le hu hR hleft
  have hR' := simplexRight_nonneg_bounded v T beta b eps eta hb hv hT hright
  simpa using hasNMF_of_factorization _ _ hL hR'
    (simplex_factorization u v R T eps eta (ne_of_gt heta))

/-- Replacing one positive rank-one term increases the nonnegative factorization
width by at most the real factor width of the perturbation. -/
theorem positive_core_absorption (s : ℕ) (P : Matrix m n ℝ)
    (hP : HasNMF P s) (hq : 0 < Fintype.card q)
    (u : m → ℝ) (v : n → ℝ) (R : Matrix m q ℝ) (T : Matrix q n ℝ)
    (alpha beta a b eps eta : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (heta : 0 < eta)
    (hu : ∀ i, alpha ≤ u i) (hv : ∀ j, beta ≤ v j)
    (hR : ∀ i k, |R i k| ≤ a) (hT : ∀ k j, |T k j| ≤ b)
    (hleft : eta * (Fintype.card q : ℝ) * a ≤ alpha)
    (hright : |eps / eta| * (2 * (Fintype.card q : ℝ) + 1) * b ≤ beta) :
    HasNMF (P + vecMulVec u v + eps • (R * T)) (s + Fintype.card q + 1) := by
  have h := hP.add (absorption_bounded hq u v R T alpha beta a b eps eta
    ha hb heta hu hv hR hT hleft hright)
  simpa only [add_assoc] using h

end PositiveCore
