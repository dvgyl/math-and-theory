import Mathlib.Algebra.Polynomial.Coeff
import Lean.Elab.Tactic.Omega

/-! Unimodality, unique modes, and the effect of adjoining initial zero coefficients. -/
namespace LeafMode.Modes
open Polynomial

def UnimodalAt (p : Polynomial ℤ) (m : ℕ) : Prop :=
  (∀ i, i < m → p.coeff i ≤ p.coeff (i + 1)) ∧
  (∀ i, m ≤ i → p.coeff (i + 1) ≤ p.coeff i)

def IsMode (p : Polynomial ℤ) (m : ℕ) : Prop :=
  ∀ i, p.coeff i ≤ p.coeff m

def UniqueMode (p : Polynomial ℤ) (m : ℕ) : Prop :=
  ∀ i, i ≠ m → p.coeff i < p.coeff m

def ModesClose (p q : Polynomial ℤ) : Prop :=
  ∃ i j, IsMode p i ∧ IsMode q j ∧ i ≤ j + 1 ∧ j ≤ i + 1

theorem modesClose_comm {p q : Polynomial ℤ} : ModesClose p q ↔ ModesClose q p := by
  constructor <;> rintro ⟨i, j, hi, hj, hij, hji⟩
  · exact ⟨j, i, hj, hi, hji, hij⟩
  · exact ⟨j, i, hj, hi, hji, hij⟩

theorem UniqueMode.isMode {p : Polynomial ℤ} {m : ℕ} (h : UniqueMode p m) :
    IsMode p m := by
  intro i
  by_cases hi : i = m
  · simpa [hi]
  · exact le_of_lt (h i hi)

theorem unique_mode_iff {p : Polynomial ℤ} {m : ℕ} (h : UniqueMode p m) (i : ℕ) :
    IsMode p i ↔ i = m := by
  constructor
  · intro hi
    by_contra hne
    exact (not_le_of_gt (h i hne)) (hi m)
  · rintro rfl
    exact h.isMode

theorem shift_nonneg {p : Polynomial ℤ} (h : ∀ i, 0 ≤ p.coeff i) (n : ℕ) :
    ∀ i, 0 ≤ ((X : Polynomial ℤ) ^ n * p).coeff i := by
  intro i
  rw [coeff_X_pow_mul']
  split_ifs with hi
  · exact h (i - n)
  · exact le_rfl

theorem shift_unimodal {p : Polynomial ℤ} {m : ℕ}
    (h0 : ∀ i, 0 ≤ p.coeff i) (h : UnimodalAt p m) (n : ℕ) :
    UnimodalAt ((X : Polynomial ℤ) ^ n * p) (n + m) := by
  constructor
  · intro i hi
    rw [coeff_X_pow_mul', coeff_X_pow_mul']
    by_cases hn : n ≤ i
    · have hn' : n ≤ i + 1 := by omega
      rw [if_pos hn, if_pos hn']
      have hs : i + 1 - n = (i - n) + 1 := by omega
      rw [hs]
      exact h.1 (i - n) (by omega)
    · rw [if_neg hn]
      split_ifs with hn'
      · exact h0 (i + 1 - n)
      · exact le_rfl
  · intro i hi
    have hn : n ≤ i := by omega
    have hn' : n ≤ i + 1 := by omega
    rw [coeff_X_pow_mul', coeff_X_pow_mul', if_pos hn', if_pos hn]
    have hs : i + 1 - n = (i - n) + 1 := by omega
    rw [hs]
    exact h.2 (i - n) (by omega)

theorem shift_unique {p : Polynomial ℤ} {m : ℕ}
    (hpos : 0 < p.coeff m) (h : UniqueMode p m) (n : ℕ) :
    UniqueMode ((X : Polynomial ℤ) ^ n * p) (n + m) := by
  intro i hi
  have hp : ((X : Polynomial ℤ) ^ n * p).coeff (n + m) = p.coeff m := by
    simpa [Nat.add_comm] using coeff_X_pow_mul p n m
  rw [hp, coeff_X_pow_mul']
  split_ifs with hn
  · exact h (i - n) (by omega)
  · exact hpos

theorem shift_positive {p : Polynomial ℤ} {m : ℕ}
    (hpos : 0 < p.coeff m) (n : ℕ) :
    0 < ((X : Polynomial ℤ) ^ n * p).coeff (n + m) := by
  simpa [Nat.add_comm] using hpos.trans_eq (coeff_X_pow_mul p n m).symm

theorem not_modesClose {p q : Polynomial ℤ} {a b : ℕ}
    (hp : UniqueMode p a) (hq : UniqueMode q b) (hab : a + 1 < b) :
    ¬ ModesClose p q := by
  rintro ⟨i, j, hi, hj, _, hji⟩
  have hai : i = a := (unique_mode_iff hp i).mp hi
  have hbj : j = b := (unique_mode_iff hq j).mp hj
  omega

end LeafMode.Modes
