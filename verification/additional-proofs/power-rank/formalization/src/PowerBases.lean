import RankEngine
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum

noncomputable section
namespace PowerRank

theorem base_factorization_two (k j : ℕ) : (2 ^ k * 3 ^ j).factorization 2 = k := by
  rw [Nat.factorization_mul (pow_ne_zero k (by decide)) (pow_ne_zero j (by decide)),
    Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
    Nat.Prime.factorization_pow (by decide : Nat.Prime 3)]
  simp

theorem base_factorization_three (k j : ℕ) : (2 ^ k * 3 ^ j).factorization 3 = j := by
  rw [Nat.factorization_mul (pow_ne_zero k (by decide)) (pow_ne_zero j (by decide)),
    Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
    Nat.Prime.factorization_pow (by decide : Nat.Prime 3)]
  simp

/-- Distinct exponent pairs give distinct actual positive complex bases. -/
theorem power_base_injective :
    Function.Injective (fun p : ℕ × ℕ => (2 : ℂ) ^ p.2 * (3 : ℂ) ^ p.1) := by
  intro p q heq
  change (2 : ℂ) ^ p.2 * (3 : ℂ) ^ p.1 = (2 : ℂ) ^ q.2 * (3 : ℂ) ^ q.1 at heq
  have hn : (2 ^ p.2 * 3 ^ p.1 : ℕ) = 2 ^ q.2 * 3 ^ q.1 := by exact_mod_cast heq
  have h2 := congrArg (fun n : ℕ => n.factorization 2) hn
  have h3 := congrArg (fun n : ℕ => n.factorization 3) hn
  rw [base_factorization_two, base_factorization_two] at h2
  rw [base_factorization_three, base_factorization_three] at h3
  exact Prod.ext h3 h2

/-- The precise triangular grid of bases in the displayed characteristic product. -/
abbrev PowerIndex (M : ℕ) := Σ j : Fin (2 * M + 1), Fin (M + j.val + 1)

def powerBase (M : ℕ) (i : PowerIndex M) : ℂ := (2 : ℂ) ^ i.2.val * (3 : ℂ) ^ i.1.val

theorem powerBase_ne_zero (M : ℕ) (i : PowerIndex M) : powerBase M i ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))

theorem powerBase_injective (M : ℕ) : Function.Injective (powerBase M) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ heq
  have h : (j.val, k.val) = (j'.val, k'.val) :=
    power_base_injective (by simpa only [powerBase] using heq)
  have hj : j = j' := Fin.ext (congrArg Prod.fst h)
  subst j'
  have hk : k = k' := Fin.ext (congrArg Prod.snd h)
  subst k'
  rfl

end PowerRank
