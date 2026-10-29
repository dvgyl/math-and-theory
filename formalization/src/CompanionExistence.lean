module
public import CompanionFamily
public import Mathlib.Data.Nat.Prime.Infinite

@[expose] public section

noncomputable section
namespace PowerRank.Companion

def chosenPrime (n : ℕ) : ℕ := Classical.choose (Nat.exists_infinite_primes n)

theorem chosenPrime_spec (n : ℕ) : n ≤ chosenPrime n ∧ Nat.Prime (chosenPrime n) :=
  Classical.choose_spec (Nat.exists_infinite_primes n)

def primeLadder : ℕ → ℕ
  | 0 => chosenPrime 3
  | n+1 => chosenPrime (primeLadder n+1)

theorem primeLadder_strictMono : StrictMono primeLadder := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Nat.lt_succ_self (primeLadder n)).trans_le (chosenPrime_spec (primeLadder n+1)).1

theorem primeLadder_prime (n : ℕ) : Nat.Prime (primeLadder n) := by
  cases n with
  | zero => exact (chosenPrime_spec 3).2
  | succ n => exact (chosenPrime_spec (primeLadder n+1)).2

theorem primeLadder_three_le (n : ℕ) : 3 ≤ primeLadder n :=
  (chosenPrime_spec 3).1.trans (primeLadder_strictMono.monotone (Nat.zero_le n))

def canonicalOddPrimes (k : ℕ) : OddPrimes k where
  prime i := primeLadder i.val
  isPrime i := primeLadder_prime i.val
  odd i := (primeLadder_prime i.val).odd_of_ne_two (by have h := primeLadder_three_le i.val; omega)
  injective := fun i j h => Fin.ext (primeLadder_strictMono.injective h)

theorem oddPrimes_exist (k : ℕ) : Nonempty (OddPrimes k) := ⟨canonicalOddPrimes k⟩

abbrev Parameter := {d : ℕ // 2 ≤ d}

def parameterEquivNat : ℕ ≃ Parameter where
  toFun n := ⟨n+2, by omega⟩
  invFun d := d.1-2
  left_inv n := by simp
  right_inv d := by apply Subtype.ext; have h := d.2; simp; omega

instance parameterInfinite : Infinite Parameter := Infinite.of_injective
  parameterEquivNat parameterEquivNat.injective

def rankProfile {k : ℕ} (p : OddPrimes k) (d : Parameter) : ℕ → ℕ :=
  fun M => recurrenceRank (powerSequence p d.1 M)

theorem rankProfiles_infinite {k : ℕ} (p : OddPrimes k) :
    Set.Infinite (Set.range (rankProfile p)) := by
  apply Set.infinite_range_of_injective
  exact power_rank_functions_injective p

theorem every_rank_has_infinitely_many_profiles (r : ℕ) (hr : 3 ≤ r) :
    ∃ p : OddPrimes (r-3),
      (∀ d : Parameter, recurrenceRank (sequence p d.1) = r) ∧
      Set.Infinite (Set.range (rankProfile p)) := by
  refine ⟨canonicalOddPrimes (r-3), ?_, rankProfiles_infinite _⟩
  intro d
  exact all_r_sequence_rank r d.1 hr d.2 _

#print axioms chosenPrime_spec
#print axioms primeLadder_strictMono
#print axioms primeLadder_prime
#print axioms primeLadder_three_le
#print axioms oddPrimes_exist
#print axioms rankProfiles_infinite
#print axioms every_rank_has_infinitely_many_profiles
end PowerRank.Companion
