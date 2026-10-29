import CompanionBases
import SequenceSemantics

noncomputable section
open Polynomial
namespace PowerRank.Companion

def naturalSequence {k : ℕ} (p : OddPrimes k) (d n : ℕ) : ℕ :=
  1+2^n+2^(d*n)+∑ i, p.prime i^n

def sequence {k : ℕ} (p : OddPrimes k) (d : ℕ) : Seq :=
  fun n => naturalSequence p d n

def powerSequence {k : ℕ} (p : OddPrimes k) (d M : ℕ) : Seq :=
  fun n => sequence p d n ^ M

theorem naturalSequence_pos {k : ℕ} (p : OddPrimes k) (d n : ℕ) :
    0 < naturalSequence p d n := by
  unfold naturalSequence
  positivity

theorem sequence_literal {k : ℕ} (p : OddPrimes k) (d n : ℕ) :
    sequence p d n = 1+(2 : ℂ)^n+2^(d*n)+∑ i, (p.prime i : ℂ)^n := by
  simp [sequence, naturalSequence]

def letterBase {k : ℕ} (p : OddPrimes k) (d : ℕ) : Letter k → ℕ :=
  Sum.elim ![1,2,2^d] p.prime

theorem naturalSequence_eq_sum {k : ℕ} (p : OddPrimes k) (d n : ℕ) :
    naturalSequence p d n = ∑ i, letterBase p d i ^ n := by
  simp [naturalSequence, letterBase, Fintype.sum_sum_type, Fin.sum_univ_three, ← pow_mul]

theorem letterBase_prod {k : ℕ} (p : OddPrimes k) (d : ℕ) (b : Letter k → ℕ) :
    (∏ i, letterBase p d i ^ b i) = natBase p d b := by
  simp [letterBase, Fintype.prod_sum_type, Fin.prod_univ_three, natBase,
    ← pow_mul, pow_add]

theorem composition_multinomial {R : Type*} [CommSemiring R] (k M : ℕ) (f : Letter k → R) :
    (∑ i, f i)^M = ∑ b : Composition k M,
      (Nat.multinomial Finset.univ b.1 : R) * ∏ i, f i ^ b.1 i := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  exact Finset.sum_subtype _ (fun b => by simp [Finset.mem_piAntidiag]) _

theorem naturalPower_expansion {k : ℕ} (p : OddPrimes k) (d M n : ℕ) :
    naturalSequence p d n ^ M = ∑ b : Composition k M,
      Nat.multinomial Finset.univ b.1 * natBase p d b.1 ^ n := by
  rw [naturalSequence_eq_sum, composition_multinomial]
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  calc
    (∏ i, (letterBase p d i ^ n) ^ b.1 i) = ∏ i, (letterBase p d i ^ b.1 i)^n := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [← pow_mul, Nat.mul_comm]
    _ = (∏ i, letterBase p d i ^ b.1 i)^n := Finset.prod_pow _ _ _
    _ = _ := by rw [letterBase_prod]

def coefficient {k M : ℕ} (d : ℕ) (hd : 0 < d) (b : NormalComposition k d M) : ℕ :=
  ∑ a : {a : Composition k M // normalize d hd a = b}, Nat.multinomial Finset.univ a.1.1

theorem coefficient_pos {k d M : ℕ} (hd : 0 < d) (b : NormalComposition k d M) :
    0 < coefficient d hd b := by
  let a : {a : Composition k M // normalize d hd a = b} := ⟨b.1, normalize_normal hd b⟩
  have hl : Nat.multinomial Finset.univ b.1.1 ≤ coefficient d hd b := by
    unfold coefficient
    exact Finset.single_le_sum (fun i hi => Nat.zero_le
      (Nat.multinomial Finset.univ i.1.1)) (Finset.mem_univ a)
  exact (Nat.multinomial_pos _ _).trans_le hl

theorem naturalPower_normal_expansion {k : ℕ} (p : OddPrimes k) (d : ℕ) (hd : 0 < d) (M n : ℕ) :
    naturalSequence p d n ^ M = ∑ b : NormalComposition k d M,
      coefficient d hd b * natBase p d b.1.1 ^ n := by
  classical
  rw [naturalPower_expansion, ← Fintype.sum_fiberwise (normalize d hd)]
  apply Finset.sum_congr rfl
  intro b hb
  rw [coefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  have hn := natBase_normalize p d a.1.1
  have hval := congrArg (fun c : NormalComposition k d M => c.1.1) a.2
  change normalizeTuple d a.1.1 = b.1.1 at hval
  rw [hval] at hn
  exact hn.symm

def coefficientPolynomial {k d M : ℕ} (hd : 0 < d) (b : NormalComposition k d M) : ℂ[X] :=
  C (coefficient d hd b : ℂ)

theorem coefficientPolynomial_ne_zero {k d M : ℕ} (hd : 0 < d) (b : NormalComposition k d M) :
    coefficientPolynomial hd b ≠ 0 := by
  rw [coefficientPolynomial, Polynomial.C_ne_zero]
  exact_mod_cast (coefficient_pos hd b).ne'

theorem powerSequence_expansion {k : ℕ} (p : OddPrimes k) (d : ℕ) (hd : 0 < d) (M : ℕ) :
    powerSequence p d M = ∑ b : NormalComposition k d M,
      expPoly (complexBase p b) (coefficientPolynomial hd b) := by
  ext n
  simp only [powerSequence, sequence, Finset.sum_apply, expPoly, coefficientPolynomial,
    Polynomial.eval_C, complexBase]
  exact_mod_cast naturalPower_normal_expansion p d hd M n

#print axioms naturalSequence_pos
#print axioms sequence_literal
#print axioms naturalSequence_eq_sum
#print axioms letterBase_prod
#print axioms composition_multinomial
#print axioms naturalPower_expansion
#print axioms coefficient_pos
#print axioms naturalPower_normal_expansion
#print axioms coefficientPolynomial_ne_zero
#print axioms powerSequence_expansion
end PowerRank.Companion
