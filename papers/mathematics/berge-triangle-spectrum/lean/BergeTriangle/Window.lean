import BergeTriangle.Defs
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.LinearCombination

/-!
# Arithmetic of the upper window `(Lₙ, Eₙ]`

The width `Wₙ = Eₙ - Lₙ` equals `⌊n/4⌋`, plus one when `n ≡ 3 (mod 4)`; the paired-product
size `p(n-2p)` is at most `Eₙ`, and `⌊n/4⌋ (n - 2⌊n/4⌋ - 1) = Lₙ`.  Corollary 4 describes the
product sizes `Eₙ - d` with `d < Wₙ` by explicit deficits, and at most
`⌊√(2n)⌋/2 + 1` sizes in the window are product sizes, so at least
`⌊n/4⌋ - ⌊√(2n)⌋/2 - 1` are not.
-/

namespace BergeTriangle

open Finset

instance (n : ℕ) : DecidablePred (IsProductSize n) := fun m =>
  decidable_of_iff (∃ p ∈ range n, 1 ≤ p ∧ 2 * p < n ∧ m = p * (n - 2 * p)) (by
    constructor
    · rintro ⟨p, -, hp⟩
      exact ⟨p, hp⟩
    · rintro ⟨p, hp⟩
      exact ⟨p, mem_range.2 (by omega), hp⟩)

/-- Every product size `p(n-2p)` is at most `Eₙ`. -/
theorem mul_sub_le_E (n p : ℕ) : p * (n - 2 * p) ≤ E n := by
  rw [E, Nat.le_div_iff_mul_le (by norm_num)]
  rcases le_or_gt n (2 * p) with h | h
  · rw [Nat.sub_eq_zero_of_le h]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * p + m := ⟨n - 2 * p, by omega⟩
    rw [show 2 * p + m - 2 * p = m by omega]
    zify
    nlinarith [sq_nonneg ((2 * p : ℤ) - m)]

/-- `Wₙ = ⌊n/4⌋`, plus one when `n ≡ 3 (mod 4)`. -/
theorem W_eq (n : ℕ) : W n = n / 4 + if n % 4 = 3 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  obtain ⟨k, hk⟩ : ∃ k, n = 4 * k + 1 ∨ n = 4 * k + 2 ∨ n = 4 * k + 3 ∨ n = 4 * k + 4 :=
    ⟨(n - 1) / 4, by omega⟩
  unfold W E L
  rcases hk with rfl | rfl | rfl | rfl
  · rw [show (4 * k + 1) ^ 2 = 8 * (2 * k ^ 2 + k) + 1 by ring,
      show (4 * k + 1 - 1) ^ 2 = 8 * (2 * k ^ 2) by rw [Nat.add_sub_cancel]; ring]
    split <;> omega
  · rw [show (4 * k + 2) ^ 2 = 8 * (2 * k ^ 2 + 2 * k) + 4 by ring,
      show (4 * k + 2 - 1) ^ 2 = 8 * (2 * k ^ 2 + k) + 1 by
        rw [show 4 * k + 2 - 1 = 4 * k + 1 by omega]; ring]
    split <;> omega
  · rw [show (4 * k + 3) ^ 2 = 8 * (2 * k ^ 2 + 3 * k + 1) + 1 by ring,
      show (4 * k + 3 - 1) ^ 2 = 8 * (2 * k ^ 2 + 2 * k) + 4 by
        rw [show 4 * k + 3 - 1 = 4 * k + 2 by omega]; ring]
    split <;> omega
  · rw [show (4 * k + 4) ^ 2 = 8 * (2 * k ^ 2 + 4 * k + 2) by ring,
      show (4 * k + 4 - 1) ^ 2 = 8 * (2 * k ^ 2 + 3 * k + 1) + 1 by
        rw [show 4 * k + 4 - 1 = 4 * k + 3 by omega]; ring]
    split <;> omega

/-- The choice `p = ⌊n/4⌋` attains `p(n - 1 - 2p) = Lₙ`. -/
theorem div_four_mul_eq_L {n : ℕ} (hn : 1 ≤ n) : n / 4 * (n - 2 * (n / 4) - 1) = L n := by
  obtain ⟨k, hk⟩ : ∃ k, n = 4 * k + 1 ∨ n = 4 * k + 2 ∨ n = 4 * k + 3 ∨ n = 4 * k + 4 :=
    ⟨(n - 1) / 4, by omega⟩
  unfold L
  rcases hk with rfl | rfl | rfl | rfl
  · rw [show (4 * k + 1) / 4 = k by omega, show 4 * k + 1 - 2 * k - 1 = 2 * k by omega,
      show (4 * k + 1 - 1) ^ 2 = 8 * (k * (2 * k)) by rw [Nat.add_sub_cancel]; ring]
    omega
  · rw [show (4 * k + 2) / 4 = k by omega, show 4 * k + 2 - 2 * k - 1 = 2 * k + 1 by omega,
      show (4 * k + 2 - 1) ^ 2 = 8 * (k * (2 * k + 1)) + 1 by
        rw [show 4 * k + 2 - 1 = 4 * k + 1 by omega]; ring]
    omega
  · rw [show (4 * k + 3) / 4 = k by omega, show 4 * k + 3 - 2 * k - 1 = 2 * k + 2 by omega,
      show (4 * k + 3 - 1) ^ 2 = 8 * (k * (2 * k + 2)) + 4 by
        rw [show 4 * k + 3 - 1 = 4 * k + 2 by omega]; ring]
    omega
  · rw [show (4 * k + 4) / 4 = k + 1 by omega,
      show 4 * k + 4 - 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      show (4 * k + 4 - 1) ^ 2 = 8 * ((k + 1) * (2 * k + 1)) + 1 by
        rw [show 4 * k + 4 - 1 = 4 * k + 3 by omega]; ring]
    omega

/-! ## Integer form of product sizes -/

theorem isProductSize_iff_int {n m : ℕ} (hm : 0 < m) :
    IsProductSize n m ↔ ∃ P : ℤ, (m : ℤ) = P * (n - 2 * P) := by
  constructor
  · rintro ⟨p, -, hpn, rfl⟩
    exact ⟨p, by push_cast [Nat.cast_sub hpn.le]; ring⟩
  · rintro ⟨P, hP⟩
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    have hP1 : 1 ≤ P := by
      by_contra hlt
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ -P by omega) (show (0 : ℤ) ≤ n - 2 * P by omega)]
    have hP2 : 2 * P < n := by
      by_contra hlt
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ P by omega) (show (0 : ℤ) ≤ 2 * P - n by omega)]
    obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ P by omega)
    have h2 : 2 * p ≤ n := by omega
    refine ⟨p, by omega, by omega, ?_⟩
    have e : ((p * (n - 2 * p) : ℕ) : ℤ) = (p : ℤ) * (n - 2 * p) := by
      push_cast [Nat.cast_sub h2]
      ring
    exact_mod_cast hP.trans e.symm

/-! ## The number of product sizes in the window -/

/-- A product size above `Lₙ` comes from a `p` with `(n - 4p)² ≤ 2n`. -/
theorem sq_sub_le_of_lt_L {n p : ℕ} (hpn : 2 * p < n) (hL : L n < p * (n - 2 * p)) :
    ((n : ℤ) - 4 * p) ^ 2 ≤ 2 * n := by
  have h8 : (n - 1) ^ 2 < 8 * L n + 8 := by unfold L; omega
  have h1 : (((n - 1) ^ 2 : ℕ) : ℤ) < 8 * (L n : ℤ) + 8 := by exact_mod_cast h8
  have h2 : (L n : ℤ) < ((p * (n - 2 * p) : ℕ) : ℤ) := by exact_mod_cast hL
  push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub hpn.le] at h1 h2
  nlinarith

/-- At most `⌊√(2n)⌋/2 + 1` sizes in `(Lₙ, Eₙ]` are of the form `p(n-2p)`. -/
theorem card_window_productSizes_le (n : ℕ) :
    #{m ∈ Ioc (L n) (E n) | IsProductSize n m} ≤ Nat.sqrt (2 * n) / 2 + 1 := by
  set s := Nat.sqrt (2 * n) with hs
  have hsub : {m ∈ Ioc (L n) (E n) | IsProductSize n m} ⊆
      (Icc ((n - s + 3) / 4) ((n + s) / 4)).image (fun p => p * (n - 2 * p)) := by
    intro m hm
    rw [mem_filter, mem_Ioc] at hm
    obtain ⟨⟨hLm, -⟩, p, -, hpn, rfl⟩ := hm
    have hsq := sq_sub_le_of_lt_L hpn hLm
    refine mem_image.2 ⟨p, mem_Icc.2 ?_, rfl⟩
    rcases le_total (4 * p) n with h | h
    · have hd : (n - 4 * p) * (n - 4 * p) ≤ 2 * n := by
        have e : (((n - 4 * p) * (n - 4 * p) : ℕ) : ℤ) = ((n : ℤ) - 4 * p) ^ 2 := by
          push_cast [Nat.cast_sub h]
          ring
        exact_mod_cast e.le.trans hsq
      have := Nat.le_sqrt.2 hd
      rw [← hs] at this
      omega
    · have hd : (4 * p - n) * (4 * p - n) ≤ 2 * n := by
        have e : (((4 * p - n) * (4 * p - n) : ℕ) : ℤ) = ((n : ℤ) - 4 * p) ^ 2 := by
          push_cast [Nat.cast_sub h]
          ring
        exact_mod_cast e.le.trans hsq
      have := Nat.le_sqrt.2 hd
      rw [← hs] at this
      omega
  calc #{m ∈ Ioc (L n) (E n) | IsProductSize n m}
      _ ≤ #((Icc ((n - s + 3) / 4) ((n + s) / 4)).image (fun p => p * (n - 2 * p))) :=
        card_le_card hsub
      _ ≤ #(Icc ((n - s + 3) / 4) ((n + s) / 4)) := card_image_le
      _ ≤ s / 2 + 1 := by
        rw [Nat.card_Icc]
        omega

/-- The window `(Lₙ, Eₙ]` has `Wₙ` members. -/
theorem card_window (n : ℕ) : #(Ioc (L n) (E n)) = W n :=
  Nat.card_Ioc _ _

/-- At least `⌊n/4⌋ - ⌊√(2n)⌋/2 - 1` sizes in the window `(Lₙ, Eₙ]` are not of the form
`p(n-2p)`; this is the count `n/4 - O(√n)` of Corollary 4. -/
theorem window_not_productSize_count (n : ℕ) :
    n / 4 ≤ #{m ∈ Ioc (L n) (E n) | ¬ IsProductSize n m} + (Nat.sqrt (2 * n) / 2 + 1) := by
  have h1 := card_filter_add_card_filter_not (s := Ioc (L n) (E n))
    (fun m => IsProductSize n m)
  have h2 := card_window_productSizes_le n
  have h3 : n / 4 ≤ W n := by
    rw [W_eq]
    split <;> omega
  rw [card_window] at h1
  omega

/-! ## Corollary 4: the explicit deficits -/

/-- The deficits `d` for which `Eₙ - d` is a product size, by the residue of `n`. -/
def AllowedDeficit (n d : ℕ) : Prop :=
  (n % 4 = 0 ∧ ∃ j, d = 2 * j ^ 2) ∨ (n % 4 = 2 ∧ ∃ j, d = 2 * j * (j + 1)) ∨
    (n % 2 = 1 ∧ ∃ j, d = j * (j + 1) / 2)

theorem exists_int_iff_even (d : ℕ) :
    (∃ x : ℤ, (d : ℤ) = 2 * x ^ 2) ↔ ∃ j : ℕ, d = 2 * j ^ 2 := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, x ^ 2 = (j : ℤ) ^ 2 := by
      rcases le_total 0 x with h | h
      · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le h
        exact ⟨j, rfl⟩
      · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 h)
        exact ⟨j, by rw [← hj]; ring⟩
    refine ⟨j, ?_⟩
    have : (d : ℤ) = ((2 * j ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [hx, hj]
    exact_mod_cast this
  · rintro ⟨j, rfl⟩
    exact ⟨j, by push_cast; ring⟩

theorem exists_int_iff_two_mul (d : ℕ) :
    (∃ x : ℤ, (d : ℤ) = 2 * x ^ 2 - 2 * x) ↔ ∃ j : ℕ, d = 2 * j * (j + 1) := by
  constructor
  · rintro ⟨x, hx⟩
    rcases le_or_gt 1 x with h | h
    · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x - 1 by omega)
      refine ⟨j, ?_⟩
      have : (d : ℤ) = ((2 * j * (j + 1) : ℕ) : ℤ) := by
        push_cast
        rw [hx, ← hj]
        ring
      exact_mod_cast this
    · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -x by omega)
      refine ⟨j, ?_⟩
      have : (d : ℤ) = ((2 * j * (j + 1) : ℕ) : ℤ) := by
        push_cast
        rw [hx, ← hj]
        ring
      exact_mod_cast this
  · rintro ⟨j, rfl⟩
    exact ⟨j + 1, by push_cast; ring⟩

theorem exists_int_iff_triangular (d : ℕ) :
    (∃ x : ℤ, (d : ℤ) = 2 * x ^ 2 - x) ↔ ∃ j : ℕ, d = j * (j + 1) / 2 := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) * (j + 1) = 2 * d := by
      rcases le_or_gt 1 x with h | h
      · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ 2 * x - 1 by omega)
        exact ⟨j, by rw [hx, ← hj]; ring⟩
      · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -2 * x by omega)
        exact ⟨j, by rw [hx, ← hj]; ring⟩
    refine ⟨j, ?_⟩
    have : j * (j + 1) = 2 * d := by exact_mod_cast hj
    omega
  · rintro ⟨j, rfl⟩
    obtain ⟨y, rfl | rfl⟩ := Nat.even_or_odd' j
    · refine ⟨-y, ?_⟩
      have : 2 * y * (2 * y + 1) / 2 = y * (2 * y + 1) := by
        rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [this]
      push_cast
      ring
    · refine ⟨y + 1, ?_⟩
      have : (2 * y + 1) * (2 * y + 1 + 1) / 2 = (2 * y + 1) * (y + 1) := by
        rw [show (2 * y + 1) * (2 * y + 1 + 1) = 2 * ((2 * y + 1) * (y + 1)) by ring,
          Nat.mul_div_cancel_left _ (by norm_num)]
      rw [this]
      push_cast
      ring

/-- Explicit values of `Eₙ` by the residue of `n` modulo `4`. -/
theorem E_four_mul (t : ℕ) : E (4 * t) = 2 * t ^ 2 := by
  unfold E
  rw [show (4 * t) ^ 2 = 8 * (2 * t ^ 2) by ring]
  omega

theorem E_four_mul_add_one (t : ℕ) : E (4 * t + 1) = 2 * t ^ 2 + t := by
  unfold E
  rw [show (4 * t + 1) ^ 2 = 8 * (2 * t ^ 2 + t) + 1 by ring]
  omega

theorem E_four_mul_add_two (t : ℕ) : E (4 * t + 2) = 2 * t ^ 2 + 2 * t := by
  unfold E
  rw [show (4 * t + 2) ^ 2 = 8 * (2 * t ^ 2 + 2 * t) + 4 by ring]
  omega

theorem E_four_mul_add_three (t : ℕ) : E (4 * t + 3) = 2 * t ^ 2 + 3 * t + 1 := by
  unfold E
  rw [show (4 * t + 3) ^ 2 = 8 * (2 * t ^ 2 + 3 * t + 1) + 1 by ring]
  omega

/-- Corollary 4: for `d < Wₙ`, the size `Eₙ - d` is a product size `p(n-2p)` exactly for the
listed deficits. -/
theorem isProductSize_E_sub_iff {n d : ℕ} (hd : d < W n) :
    IsProductSize n (E n - d) ↔ AllowedDeficit n d := by
  have hdE : d < E n := by unfold W at hd; omega
  rw [isProductSize_iff_int (by omega)]
  push_cast [Nat.cast_sub hdE.le]
  obtain ⟨t, rfl | rfl | rfl | rfl⟩ :
      ∃ t, n = 4 * t ∨ n = 4 * t + 1 ∨ n = 4 * t + 2 ∨ n = 4 * t + 3 := ⟨n / 4, by omega⟩
  · have hE : (E (4 * t) : ℤ) = 2 * t ^ 2 := by exact_mod_cast E_four_mul t
    have : AllowedDeficit (4 * t) d ↔ ∃ j, d = 2 * j ^ 2 := by
      rw [AllowedDeficit]
      constructor
      · rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
        exacts [h, by omega, by omega]
      · intro h
        exact Or.inl ⟨by omega, h⟩
    rw [this, ← exists_int_iff_even]
    constructor
    · rintro ⟨P, hP⟩
      exact ⟨P - t, by push_cast at hP; linear_combination hE - hP⟩
    · rintro ⟨x, hx⟩
      exact ⟨t + x, by push_cast; linear_combination hE - hx⟩
  · have hE : (E (4 * t + 1) : ℤ) = 2 * t ^ 2 + t := by exact_mod_cast E_four_mul_add_one t
    have : AllowedDeficit (4 * t + 1) d ↔ ∃ j, d = j * (j + 1) / 2 := by
      rw [AllowedDeficit]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩)
        exacts [by omega, by omega, h]
      · intro h
        exact Or.inr (Or.inr ⟨by omega, h⟩)
    rw [this, ← exists_int_iff_triangular]
    constructor
    · rintro ⟨P, hP⟩
      exact ⟨P - t, by push_cast at hP; linear_combination hE - hP⟩
    · rintro ⟨x, hx⟩
      exact ⟨t + x, by push_cast; linear_combination hE - hx⟩
  · have hE : (E (4 * t + 2) : ℤ) = 2 * t ^ 2 + 2 * t := by exact_mod_cast E_four_mul_add_two t
    have : AllowedDeficit (4 * t + 2) d ↔ ∃ j, d = 2 * j * (j + 1) := by
      rw [AllowedDeficit]
      constructor
      · rintro (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩)
        exacts [by omega, h, by omega]
      · intro h
        exact Or.inr (Or.inl ⟨by omega, h⟩)
    rw [this, ← exists_int_iff_two_mul]
    constructor
    · rintro ⟨P, hP⟩
      exact ⟨P - t, by push_cast at hP; linear_combination hE - hP⟩
    · rintro ⟨x, hx⟩
      exact ⟨t + x, by push_cast; linear_combination hE - hx⟩
  · have hE : (E (4 * t + 3) : ℤ) = 2 * t ^ 2 + 3 * t + 1 := by
      exact_mod_cast E_four_mul_add_three t
    have : AllowedDeficit (4 * t + 3) d ↔ ∃ j, d = j * (j + 1) / 2 := by
      rw [AllowedDeficit]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩)
        exacts [by omega, by omega, h]
      · intro h
        exact Or.inr (Or.inr ⟨by omega, h⟩)
    rw [this, ← exists_int_iff_triangular]
    constructor
    · rintro ⟨P, hP⟩
      exact ⟨t + 1 - P, by push_cast at hP; linear_combination hE - hP⟩
    · rintro ⟨x, hx⟩
      exact ⟨t + 1 - x, by push_cast; linear_combination hE - hx⟩

end BergeTriangle
