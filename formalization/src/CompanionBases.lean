module
public import CompanionCompositions
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section
namespace PowerRank.Companion

structure OddPrimes (k : ℕ) where
  prime : Fin k → ℕ
  isPrime : ∀ i, Nat.Prime (prime i)
  odd : ∀ i, Odd (prime i)
  injective : Function.Injective prime

theorem OddPrimes.ne_two {k : ℕ} (p : OddPrimes k) (i : Fin k) : p.prime i ≠ 2 := by
  intro he
  have h := p.odd i
  rw [he] at h
  obtain ⟨a, ha⟩ := h
  omega

def natBase {k : ℕ} (p : OddPrimes k) (d : ℕ) (b : Letter k → ℕ) : ℕ :=
  2^(b (Sum.inl 1)+d*b (Sum.inl 2)) * ∏ i, p.prime i ^ b (Sum.inr i)

theorem natBase_pos {k : ℕ} (p : OddPrimes k) (d : ℕ) (b : Letter k → ℕ) :
    0 < natBase p d b := by
  unfold natBase
  apply Nat.mul_pos (pow_pos (by decide) _)
  exact Finset.prod_pos (fun i hi => pow_pos (p.isPrime i).pos _)

theorem natBase_factorization_two {k : ℕ} (p : OddPrimes k) (d : ℕ) (b : Letter k → ℕ) :
    (natBase p d b).factorization 2 = b (Sum.inl 1)+d*b (Sum.inl 2) := by
  rw [natBase, Nat.factorization_mul (pow_ne_zero _ (by decide))
    (Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (p.isPrime i).ne_zero))]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
    Finsupp.single_eq_same]
  rw [Nat.factorization_prod_apply
    (fun i hi => pow_ne_zero (b (Sum.inr i)) (p.isPrime i).ne_zero)]
  have hzero : ∑ i, (p.prime i ^ b (Sum.inr i)).factorization 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Nat.Prime.factorization_pow (p.isPrime i)]
    exact Finsupp.single_eq_of_ne (p.ne_two i).symm
  rw [hzero, add_zero]

theorem natBase_factorization_prime {k : ℕ} (p : OddPrimes k) (d : ℕ)
    (b : Letter k → ℕ) (i : Fin k) :
    (natBase p d b).factorization (p.prime i) = b (Sum.inr i) := by
  rw [natBase, Nat.factorization_mul (pow_ne_zero _ (by decide))
    (Finset.prod_ne_zero_iff.mpr (fun j hj => pow_ne_zero _ (p.isPrime j).ne_zero))]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow (by decide : Nat.Prime 2)]
  rw [Finsupp.single_eq_of_ne (p.ne_two i), zero_add,
    Nat.factorization_prod_apply (fun j hj => pow_ne_zero (b (Sum.inr j)) (p.isPrime j).ne_zero)]
  rw [Finset.sum_eq_single i]
  · rw [Nat.Prime.factorization_pow (p.isPrime i), Finsupp.single_eq_same]
  · intro j hj hji
    rw [Nat.Prime.factorization_pow (p.isPrime j)]
    exact Finsupp.single_eq_of_ne (fun he => hji (p.injective he.symm))
  · simp

theorem natBase_normalize {k : ℕ} (p : OddPrimes k) (d : ℕ) (b : Letter k → ℕ) :
    natBase p d (normalizeTuple d b) = natBase p d b := by
  have he : b (Sum.inl 1)%d + d*(b (Sum.inl 2)+b (Sum.inl 1)/d) =
      b (Sum.inl 1)+d*b (Sum.inl 2) := by
    have h := Nat.mod_add_div (b (Sum.inl 1)) d
    nlinarith
  simpa [natBase, normalizeTuple] using
    congrArg (fun e : ℕ => 2^e * ∏ i, p.prime i ^ b (Sum.inr i)) he

theorem natBase_normal_injective {k d M : ℕ} (p : OddPrimes k) (hd : 0 < d) :
    Function.Injective (fun b : NormalComposition k d M => natBase p d b.1.1) := by
  intro b c he
  have htwo := congrArg (fun x : ℕ => x.factorization 2) he
  rw [natBase_factorization_two, natBase_factorization_two] at htwo
  have hodd : ∀ i, b.1.1 (Sum.inr i) = c.1.1 (Sum.inr i) := by
    intro i
    have h := congrArg (fun x : ℕ => x.factorization (p.prime i)) he
    simpa only [natBase_factorization_prime] using h
  have hrem := congrArg (fun n : ℕ => n%d) htwo
  have hone : b.1.1 (Sum.inl 1) = c.1.1 (Sum.inl 1) := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt b.2, Nat.mod_eq_of_lt c.2] using hrem
  have htwocoord : b.1.1 (Sum.inl 2) = c.1.1 (Sum.inl 2) := by
    apply Nat.eq_of_mul_eq_mul_left hd
    omega
  have hb := b.1.2
  have hc := c.1.2
  simp only [Fintype.sum_sum_type, Fin.sum_univ_three] at hb hc
  have hsum : (∑ i, b.1.1 (Sum.inr i)) = ∑ i, c.1.1 (Sum.inr i) :=
    Finset.sum_congr rfl (fun i hi => hodd i)
  have hzero : b.1.1 (Sum.inl 0) = c.1.1 (Sum.inl 0) := by omega
  apply Subtype.ext
  apply Subtype.ext
  funext i
  cases i with
  | inl i => fin_cases i <;> assumption
  | inr i => exact hodd i

def complexBase {k d M : ℕ} (p : OddPrimes k) (b : NormalComposition k d M) : ℂ :=
  natBase p d b.1.1

theorem complexBase_ne_zero {k d M : ℕ} (p : OddPrimes k) (b : NormalComposition k d M) :
    complexBase p b ≠ 0 := by
  change (natBase p d b.1.1 : ℂ) ≠ 0
  exact_mod_cast (natBase_pos p d b.1.1).ne'

theorem complexBase_injective {k d M : ℕ} (p : OddPrimes k) (hd : 0 < d) :
    Function.Injective (fun b : NormalComposition k d M => complexBase p b) := by
  intro b c he
  apply natBase_normal_injective p hd
  change (natBase p d b.1.1 : ℂ) = (natBase p d c.1.1 : ℂ) at he
  exact_mod_cast he

#print axioms OddPrimes.ne_two
#print axioms natBase_pos
#print axioms natBase_factorization_two
#print axioms natBase_factorization_prime
#print axioms natBase_normalize
#print axioms natBase_normal_injective
#print axioms complexBase_ne_zero
#print axioms complexBase_injective
end PowerRank.Companion
