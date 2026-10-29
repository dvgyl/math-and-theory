module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Sym.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! The rank is defined by actual constant-coefficient recurrences on a tail.
The main statement uses the literal positive integer sequence and every
termwise power. The square-count correction and natural-number arithmetic
are unchanged. The companion statements give the literal fixed-rank family
and infinitely many different power-rank profiles at every rank at least three.
Generating-function and polynomial-growth corollaries are outside this statement. -/

@[expose] public section

noncomputable section
open Polynomial
open scoped BigOperators

namespace PowerRank

abbrev Seq := ℕ → ℂ

/-- Fixed numeral proofs keep the definitions identical across modules. -/
instance instAtLeastTwo2 : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩
instance instAtLeastTwo3 : Nat.AtLeastTwo 3 := ⟨Nat.le_add_right 2 1⟩
instance instAtLeastTwo6 : Nat.AtLeastTwo 6 := ⟨Nat.le_add_right 2 4⟩
instance instAtLeastTwo7 : Nat.AtLeastTwo 7 := ⟨Nat.le_add_right 2 5⟩
instance instAtLeastTwo9 : Nat.AtLeastTwo 9 := ⟨Nat.le_add_right 2 7⟩

def shift : Module.End ℂ Seq where
  toFun u n := u (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def polyAction (q : ℂ[X]) : Module.End ℂ Seq := aeval shift q

def EventuallyAnnihilates (q : ℂ[X]) (u : Seq) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, polyAction q u n = 0

def AdmissibleAnnihilator (q : ℂ[X]) (u : Seq) : Prop :=
  q.Monic ∧ q.coeff 0 ≠ 0 ∧ EventuallyAnnihilates q u

def MinimalCharacteristic (χ : ℂ[X]) (u : Seq) : Prop :=
  AdmissibleAnnihilator χ u ∧ ∀ q, AdmissibleAnnihilator q u → χ ∣ q

def recurrenceRank (u : Seq) : ℕ :=
  sInf {r : ℕ | ∃ q : ℂ[X], AdmissibleAnnihilator q u ∧ q.natDegree = r}

def mainSequence (n : ℕ) : ℂ :=
  1 + 2 ^ n + 3 ^ n * (1 - 2 ^ n) ^ 2 + (n : ℂ) * 9 ^ n * (1 + 2 ^ n) ^ 3

def mainInteger (n : ℕ) : ℤ :=
  1 + 2 ^ n + 3 ^ n * (1 - 2 ^ n) ^ 2 + (n : ℤ) * 9 ^ n * (1 + 2 ^ n) ^ 3

def mainPowerSequence (M : ℕ) : Seq := fun n => mainSequence n ^ M

abbrev PowerIndex (M : ℕ) := Σ j : Fin (2 * M + 1), Fin (M + j.val + 1)

def powerBase (M : ℕ) (i : PowerIndex M) : ℂ := (2 : ℂ) ^ i.2.val * (3 : ℂ) ^ i.1.val

def expectedMultiplicity (M j k : ℕ) : ℕ :=
  1 + j / 2 - if j % 2 = 1 ∧ (((M + j : ℕ) : ℚ) - 2 * k) ^ 2 = (M + j : ℕ) then 1 else 0

def powerCharacteristic (M : ℕ) : ℂ[X] :=
  ∏ i : PowerIndex M,
    (X - C (powerBase M i)) ^ expectedMultiplicity M i.1.val i.2.val

def paritySquareSet (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (3 * M + 1)).filter
    (fun q => M < q ^ 2 ∧ q ^ 2 < 3 * M ∧ (q ^ 2 - M) % 2 = 1)

def squareCorrection (M : ℕ) : ℕ := (paritySquareSet M).card

def rankCubicValue (M : ℕ) : ℝ :=
  ((M : ℝ) + 1) * (2 * M + 1) * (7 * M + 6) / 6

def EventuallyQuasipolynomial (f : ℕ → ℝ) : Prop :=
  ∃ (l : ℕ) (hl : 0 < l), ∃ P : Fin l → ℝ[X], ∃ N : ℕ,
    ∀ M ≥ N, f M = (P ⟨M % l, Nat.mod_lt M hl⟩).eval (M : ℝ)

/-- The literal sequence, exact minimal characteristic polynomials, and power ranks. -/
theorem main_result :
    (∀ n, 0 < mainInteger n ∧ mainSequence n = (mainInteger n : ℂ)) ∧
    recurrenceRank mainSequence = 13 ∧
    (∀ M, MinimalCharacteristic (powerCharacteristic M) (mainPowerSequence M)) ∧
    (∀ M, recurrenceRank (mainPowerSequence M) =
      (M + 1) * (2 * M + 1) * (7 * M + 6) / 6 - 2 * squareCorrection M) ∧
    (∀ M ≥ 1, |rankCubicValue M - (recurrenceRank (mainPowerSequence M) : ℝ) -
      (Real.sqrt 3 - 1) * Real.sqrt (M : ℝ)| ≤ 2) ∧
    ¬ EventuallyQuasipolynomial (fun M => (recurrenceRank (mainPowerSequence M) : ℝ)) := by
  sorry

namespace Companion

abbrev Letter (k : ℕ) := Fin 3 ⊕ Fin k

abbrev Composition (k M : ℕ) := {b : Letter k → ℕ // ∑ i, b i = M}

instance compositionFintype (k M : ℕ) : Fintype (Composition k M) :=
  Fintype.ofEquiv (Sym (Letter k) M) (Sym.equivNatSumOfFintype (Letter k) M)

/-- A fixed proof for the literal indices in `Fin 3`. -/
instance instNeZeroThree : NeZero (3 : ℕ) := @Nat.instNeZeroSucc 2

abbrev NormalComposition (k d M : ℕ) := {b : Composition k M // b.1 (Sum.inl 1) < d}

structure OddPrimes (k : ℕ) where
  prime : Fin k → ℕ
  isPrime : ∀ i, Nat.Prime (prime i)
  odd : ∀ i, Odd (prime i)
  injective : Function.Injective prime

def natBase {k : ℕ} (p : OddPrimes k) (d : ℕ) (b : Letter k → ℕ) : ℕ :=
  2^(b (Sum.inl 1)+d*b (Sum.inl 2)) * ∏ i, p.prime i ^ b (Sum.inr i)

def complexBase {k d M : ℕ} (p : OddPrimes k) (b : NormalComposition k d M) : ℂ :=
  natBase p d b.1.1

def naturalSequence {k : ℕ} (p : OddPrimes k) (d n : ℕ) : ℕ :=
  1+2^n+2^(d*n)+∑ i, p.prime i^n

def sequence {k : ℕ} (p : OddPrimes k) (d : ℕ) : Seq :=
  fun n => naturalSequence p d n

def powerSequence {k : ℕ} (p : OddPrimes k) (d M : ℕ) : Seq :=
  fun n => sequence p d n ^ M

def characteristic {k : ℕ} (p : OddPrimes k) (d M : ℕ) : ℂ[X] :=
  ∏ b : NormalComposition k d M, (X-C (complexBase p b))

abbrev Parameter := {d : ℕ // 2 ≤ d}

def rankProfile {k : ℕ} (p : OddPrimes k) (d : Parameter) : ℕ → ℕ :=
  fun M => recurrenceRank (powerSequence p d.1 M)

/-- The actual positive family and its exact all-power rank formula. -/
theorem family_result (r d : ℕ) (hr : 3 ≤ r) (hd : 2 ≤ d) (p : OddPrimes (r-3)) :
    (∀ n, 0 < naturalSequence p d n ∧ sequence p d n = (naturalSequence p d n : ℂ)) ∧
    recurrenceRank (sequence p d) = r ∧
    (∀ M, MinimalCharacteristic (characteristic p d M) (powerSequence p d M)) ∧
    (∀ M, recurrenceRank (powerSequence p d M) = (M+r-1).choose (r-1) -
      if M < d then 0 else (M-d+r-1).choose (r-1)) ∧
    Function.Injective (fun e : {e : ℕ // 2 ≤ e} =>
      fun M => recurrenceRank (powerSequence p e.1 M)) := by
  sorry

/-- Every initial rank at least three has infinitely many power-rank profiles. -/
theorem every_rank_has_infinitely_many_profiles (r : ℕ) (hr : 3 ≤ r) :
    ∃ p : OddPrimes (r-3),
      (∀ d : Parameter, recurrenceRank (sequence p d.1) = r) ∧
      Set.Infinite (Set.range (rankProfile p)) := by
  sorry

end Companion

end PowerRank
