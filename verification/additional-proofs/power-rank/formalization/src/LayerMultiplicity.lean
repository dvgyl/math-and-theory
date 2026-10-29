import LayerSupport

noncomputable section
namespace PowerRank

/-- Natural-valued characteristic multiplicity; zero polynomials contribute zero. -/
def layerMultiplicity (M j k : ℕ) : ℕ :=
  if layerPolynomial M j k = 0 then 0 else (layerPolynomial M j k).natDegree + 1

def expectedMultiplicity (M j k : ℕ) : ℕ :=
  1 + j / 2 - if j % 2 = 1 ∧ (((M + j : ℕ) : ℚ) - 2 * k) ^ 2 = (M + j : ℕ) then 1 else 0

/-- Every multiplicity, including omitted roots, agrees with the stated formula. -/
theorem layerMultiplicity_eq_expected (M j k : ℕ) (hj : j ≤ 2 * M) (hk : k ≤ M + j) :
    layerMultiplicity M j k = expectedMultiplicity M j k := by
  classical
  rcases Nat.even_or_odd j with heven | hodd
  · obtain ⟨a, ha⟩ := heven
    have hjform : j = 2 * a := by omega
    clear ha
    subst j
    rw [layerMultiplicity, ite_eq_right (layerPolynomial_even_ne_zero M a k hj hk),
      layerPolynomial_even_natDegree M a k hj hk]
    simp [expectedMultiplicity, Nat.add_comm]
  · obtain ⟨a, ha⟩ := hodd
    have hjform : j = 2 * a + 1 := by omega
    clear ha
    subst j
    by_cases hs : (((M + 2 * a + 1 : ℕ) : ℚ) - 2 * k) ^ 2 = (M + 2 * a + 1 : ℕ)
    · by_cases ha0 : a = 0
      · subst a
        have hz := layerPolynomial_first_odd_eq_zero M k (by omega)
          (by simpa using hk) (by simpa using hs)
        norm_num at hs
        simp [layerMultiplicity, hz, expectedMultiplicity, hs]
      · have ha1 : 1 ≤ a := by omega
        rw [layerMultiplicity,
          ite_eq_right (layerPolynomial_exceptional_odd_ne_zero M a k hj ha1 (by omega) hs),
          layerPolynomial_exceptional_odd_natDegree M a k hj ha1 (by omega) hs]
        simp only [expectedMultiplicity]
        have hq : (2 * a + 1) / 2 = a := by omega
        have hm : (2 * a + 1) % 2 = 1 := by omega
        rw [hq, hm, ite_eq_left ⟨rfl, by simpa [Nat.add_assoc] using hs⟩]
        omega
    · rw [layerMultiplicity,
        ite_eq_right (layerPolynomial_nonexceptional_odd_ne_zero M a k hj (by omega) hs),
        layerPolynomial_nonexceptional_odd_natDegree M a k hj (by omega) hs]
      simp only [expectedMultiplicity]
      have hq : (2 * a + 1) / 2 = a := by omega
      rw [hq, ite_eq_right (by intro h; exact hs (by simpa [Nat.add_assoc] using h.2))]
      omega

end PowerRank
