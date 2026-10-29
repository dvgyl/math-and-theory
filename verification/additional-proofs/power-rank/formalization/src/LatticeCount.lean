import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
namespace PowerRank

/-- Count one parity lattice in an open real interval, with the sharp absolute
error at most one. This auxiliary theorem is instantiated for the actual Q below. -/
theorem parity_lattice_count_error (s : Finset ℕ) (a b : ℝ) (r : ℕ)
    (hr : r ≤ 1) (ha : 1 ≤ a) (hab : a < b)
    (hmem : ∀ q : ℕ, q ∈ s ↔ a < q ∧ (q : ℝ) < b ∧ q % 2 = r) :
    |(s.card : ℝ) - (b - a) / 2| ≤ 1 := by
  classical
  let A : ℝ := (a - r) / 2
  let B : ℝ := (b - r) / 2
  let f : ℕ → ℤ := fun q => ((q - r) / 2 : ℕ)
  let g : ℤ → ℕ := fun z => (2 * z + r).toNat
  have hrReal : (r : ℝ) ≤ 1 := by exact_mod_cast hr
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hAB : A < B := by dsimp [A, B]; linarith
  have hfloor : 0 ≤ ⌊A⌋ := Int.floor_nonneg.mpr hA
  have hqexpr (q : ℕ) (hq : q ∈ s) : q = 2 * ((q - r) / 2) + r := by
    obtain ⟨hlo, hhi, hpar⟩ := (hmem q).mp hq
    have hq1 : 1 ≤ q := by exact_mod_cast (show (1 : ℝ) ≤ q by linarith)
    omega
  have hgnat (z : ℤ) (hz : 0 ≤ z) : g z = 2 * z.toNat + r := by
    have hzcast : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
    have hnonneg : 0 ≤ 2 * z + (r : ℤ) := by omega
    have hgcast := Int.toNat_of_nonneg hnonneg
    dsimp [g]
    omega
  have hcard : s.card = (Finset.Ioo ⌊A⌋ ⌈B⌉).card := by
    apply Finset.card_nbij' f g
    · intro q hq
      change q ∈ s at hq
      obtain ⟨hlo, hhi, hpar⟩ := (hmem q).mp hq
      have heq : (q : ℝ) = 2 * (f q : ℝ) + r := by
        dsimp [f]
        exact_mod_cast hqexpr q hq
      change f q ∈ Finset.Ioo ⌊A⌋ ⌈B⌉
      rw [Finset.mem_Ioo]
      exact ⟨Int.floor_lt.mpr (by dsimp [A]; linarith),
        Int.lt_ceil.mpr (by dsimp [B]; linarith)⟩
    · intro z hz
      change z ∈ Finset.Ioo ⌊A⌋ ⌈B⌉ at hz
      obtain ⟨hzlo, hzhi⟩ := Finset.mem_Ioo.mp hz
      have hz0 : 0 ≤ z := by omega
      have heqNat := hgnat z hz0
      have heq : (g z : ℝ) = 2 * (z : ℝ) + r := by
        rw [heqNat]
        have hzcast : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
        exact_mod_cast (show ((2 * z.toNat + r : ℕ) : ℤ) = 2 * z + r by omega)
      have hlo : A < (z : ℝ) := Int.floor_lt.mp hzlo
      have hhi : (z : ℝ) < B := Int.lt_ceil.mp hzhi
      change g z ∈ s
      apply (hmem (g z)).mpr
      refine ⟨?_, ?_, ?_⟩
      · dsimp [A] at hlo
        linarith
      · dsimp [B] at hhi
        linarith
      · rw [heqNat]
        omega
    · intro q hq
      change q ∈ s at hq
      have hv : 2 * f q + (r : ℤ) = (q : ℤ) := by
        dsimp [f]
        exact_mod_cast (hqexpr q hq).symm
      dsimp [g]
      rw [hv]
      simp
    · intro z hz
      change z ∈ Finset.Ioo ⌊A⌋ ⌈B⌉ at hz
      have hz0 : 0 ≤ z := by have := (Finset.mem_Ioo.mp hz).1; omega
      change (((g z - r) / 2 : ℕ) : ℤ) = z
      rw [hgnat z hz0]
      have hd : (2 * z.toNat + r - r) / 2 = z.toNat := by omega
      rw [hd]
      exact Int.toNat_of_nonneg hz0
  have hlt : ⌊A⌋ < ⌈B⌉ := by
    have hf := Int.floor_le A
    have hc := Int.le_ceil B
    exact_mod_cast (show (⌊A⌋ : ℝ) < (⌈B⌉ : ℝ) by linarith)
  have hcardInt : (s.card : ℤ) = ⌈B⌉ - ⌊A⌋ - 1 := by
    rw [hcard]
    exact Int.card_Ioo_of_lt _ _ hlt
  have hcardReal : (s.card : ℝ) = (⌈B⌉ : ℝ) - (⌊A⌋ : ℝ) - 1 := by exact_mod_cast hcardInt
  have hspan : B - A = (b - a) / 2 := by dsimp [A, B]; ring
  rw [hcardReal, ← hspan, abs_le]
  have hf0 := Int.floor_le A
  have hf1 := Int.lt_floor_add_one A
  have hc0 := Int.le_ceil B
  have hc1 := Int.ceil_lt_add_one B
  constructor <;> linarith

end PowerRank
