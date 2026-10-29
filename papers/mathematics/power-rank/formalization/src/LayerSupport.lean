import LayerDegrees

noncomputable section
open Polynomial
namespace PowerRank

theorem layerPolynomial_even_ne_zero (M a k : ℕ) (hj : 2 * a ≤ 2 * M)
    (hk : k ≤ M + 2 * a) : layerPolynomial M (2 * a) k ≠ 0 := by
  intro hz
  have hc := layerPolynomial_even_top M a k hj
  rw [hz, coeff_zero] at hc
  have hb : (0 : ℚ) < (M + 2 * a).choose k := by exact_mod_cast Nat.choose_pos hk
  exact (mul_pos (layerScalar_pos M (2 * a) a (by omega) (by omega) (by omega)) hb).ne' hc.symm

theorem layerPolynomial_nonexceptional_odd_ne_zero (M a k : ℕ)
    (hj : 2 * a + 1 ≤ 2 * M) (hk : k ≤ M + 2 * a + 1)
    (hs : ¬ (((M + 2 * a + 1 : ℕ) : ℚ) - 2 * k) ^ 2 = (M + 2 * a + 1 : ℕ)) :
    layerPolynomial M (2 * a + 1) k ≠ 0 := by
  intro hz
  apply hs
  apply (layerPolynomial_odd_top_eq_zero_iff M a k hj hk).mp
  rw [hz, coeff_zero]

/-- Exported positivity covers the degree-zero case a=1 explicitly. -/
theorem layerPolynomial_exceptional_next_coeff_pos (M a k : ℕ)
    (hj : 2 * a + 1 ≤ 2 * M) (ha : 1 ≤ a) (hk : k ≤ M + 2 * a + 1)
    (hs : (((M + 2 * a + 1 : ℕ) : ℚ) - 2 * k) ^ 2 = (M + 2 * a + 1 : ℕ)) :
    0 < (layerPolynomial M (2 * a + 1) k).coeff (a - 1) := by
  have hvalid := exceptional_odd_lower_layer_valid M a k hj ha hs
  rw [layerPolynomial_coeff, ite_eq_left (by omega),
    show 2 * (2 * a + 1) - 4 * (a - 1) = 6 by omega]
  apply mul_pos (layerScalar_pos M (2 * a + 1) (a - 1) (by omega) (by omega) (by omega))
  apply layerCoefficient_sixth_positive
  · omega
  · simpa [Nat.add_assoc] using hk
  · simpa [Nat.add_assoc] using hs

theorem layerPolynomial_exceptional_odd_ne_zero (M a k : ℕ)
    (hj : 2 * a + 1 ≤ 2 * M) (ha : 1 ≤ a) (hk : k ≤ M + 2 * a + 1)
    (hs : (((M + 2 * a + 1 : ℕ) : ℚ) - 2 * k) ^ 2 = (M + 2 * a + 1 : ℕ)) :
    layerPolynomial M (2 * a + 1) k ≠ 0 := by
  intro hz
  have hc := layerPolynomial_exceptional_next_coeff_pos M a k hj ha hk hs
  rw [hz, coeff_zero] at hc
  exact (lt_irrefl 0) hc

theorem layerPolynomial_odd_zero_iff (M a k : ℕ)
    (hj : 2 * a + 1 ≤ 2 * M) (hk : k ≤ M + 2 * a + 1) :
    layerPolynomial M (2 * a + 1) k = 0 ↔ a = 0 ∧
      (((M + 2 * a + 1 : ℕ) : ℚ) - 2 * k) ^ 2 = (M + 2 * a + 1 : ℕ) := by
  constructor
  · intro hz
    have hs := (layerPolynomial_odd_top_eq_zero_iff M a k hj hk).mp
      (by rw [hz, coeff_zero])
    refine ⟨?_, hs⟩
    by_contra ha
    exact layerPolynomial_exceptional_odd_ne_zero M a k hj (by omega) hk hs hz
  · rintro ⟨rfl, hs⟩
    exact layerPolynomial_first_odd_eq_zero M k (by omega) (by simpa using hk) (by simpa using hs)

end PowerRank
