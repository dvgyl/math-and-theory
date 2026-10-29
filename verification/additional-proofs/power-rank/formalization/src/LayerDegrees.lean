import KrawtchoukCoefficients
import Mathlib.Algebra.Polynomial.BigOperators

noncomputable section
open Polynomial
namespace PowerRank

/-- The binomial scalar from choosing the Z term first, then the Y term. -/
def layerScalar (M j c : ℕ) : ℚ :=
  (M.choose c : ℚ) * ((M - c).choose (j - 2 * c) : ℚ)

/-- Explicit coefficient polynomial from the proposed multinomial layer expansion.
Its identification with the literal power expansion is a separate obligation. -/
def layerPolynomial (M j k : ℕ) : ℚ[X] :=
  ∑ c ∈ Finset.Icc (j - M) (j / 2),
    monomial c (layerScalar M j c * layerCoefficient (M + j) (2 * j - 4 * c) k)

theorem layerScalar_pos (M j c : ℕ) (hc : c ≤ M) (hj : 2 * c ≤ j)
    (hupper : j ≤ M + c) : 0 < layerScalar M j c := by
  unfold layerScalar
  have h0 : (0 : ℚ) < M.choose c := by exact_mod_cast Nat.choose_pos hc
  have h1 : (0 : ℚ) < (M - c).choose (j - 2 * c) := by
    exact_mod_cast Nat.choose_pos (show j - 2 * c ≤ M - c by omega)
  exact mul_pos h0 h1

theorem layerPolynomial_coeff (M j k c : ℕ) :
    (layerPolynomial M j k).coeff c =
      if j - M ≤ c ∧ c ≤ j / 2 then
        layerScalar M j c * layerCoefficient (M + j) (2 * j - 4 * c) k else 0 := by
  classical
  simp [layerPolynomial, finsetSum_coeff, coeff_monomial, Finset.mem_Icc]

theorem layerPolynomial_natDegree_le (M j k : ℕ) :
    (layerPolynomial M j k).natDegree ≤ j / 2 := by
  unfold layerPolynomial
  apply natDegree_sum_le_of_forall_le
  intro c hc
  exact (natDegree_monomial_le _).trans (Finset.mem_Icc.mp hc).2

theorem layerPolynomial_even_top (M a k : ℕ) (hj : 2 * a ≤ 2 * M) :
    (layerPolynomial M (2 * a) k).coeff a =
      layerScalar M (2 * a) a * ((M + 2 * a).choose k : ℚ) := by
  rw [layerPolynomial_coeff, ite_eq_left (by omega), show 2 * (2 * a) - 4 * a = 0 by omega,
    layerCoefficient_zero]

/-- Every permitted even layer has the exact full top degree. -/
theorem layerPolynomial_even_natDegree (M a k : ℕ) (hj : 2 * a ≤ 2 * M)
    (hk : k ≤ M + 2 * a) : (layerPolynomial M (2 * a) k).natDegree = a := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · have h := layerPolynomial_natDegree_le M (2 * a) k
    simpa using h
  · rw [layerPolynomial_even_top M a k hj]
    exact (mul_pos (layerScalar_pos M (2 * a) a (by omega) (by omega) (by omega))
      (by exact_mod_cast Nat.choose_pos hk)).ne'

theorem layerPolynomial_odd_top (M a k : ℕ) (hj : 2 * a + 1 ≤ 2 * M) :
    (layerPolynomial M (2 * a + 1) k).coeff a =
      layerScalar M (2 * a + 1) a * layerCoefficient (M + 2 * a + 1) 2 k := by
  rw [layerPolynomial_coeff, ite_eq_left (by omega),
    show 2 * (2 * a + 1) - 4 * a = 2 by omega]
  congr 2

theorem layerPolynomial_odd_top_eq_zero_iff (M a k : ℕ)
    (hj : 2 * a + 1 ≤ 2 * M) (hk : k ≤ M + 2 * a + 1) :
    (layerPolynomial M (2 * a + 1) k).coeff a = 0 ↔
      (((M + 2 * a + 1 : ℕ) : ℚ) - 2 * k) ^ 2 = (M + 2 * a + 1 : ℕ) := by
  rw [layerPolynomial_odd_top M a k hj,
    layerCoefficient_quadratic_formula _ k (by omega)]
  have hs : layerScalar M (2 * a + 1) a ≠ 0 :=
    (layerScalar_pos M (2 * a + 1) a (by omega) (by omega) (by omega)).ne'
  have hb : (((M + 2 * a + 1).choose k : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_pos hk |>.ne'
  have hn0 : (((M + 2 * a + 1 : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast (by omega : M + 2 * a + 1 ≠ 0)
  have hn1 : (((M + 2 * a + 1 : ℕ) : ℚ)) - 1 ≠ 0 := by
    have h : (2 : ℚ) ≤ (M + 2 * a + 1 : ℕ) := by exact_mod_cast (by omega : 2 ≤ M + 2 * a + 1)
    linarith
  simp only [mul_eq_zero, hs, hb, false_or, div_eq_zero_iff, mul_ne_zero hn0 hn1,
    or_false, sub_eq_zero]

/-- A square exception in the first odd layer deletes the entire base. -/
theorem layerPolynomial_first_odd_eq_zero (M k : ℕ) (hM : 1 ≤ M) (hk : k ≤ M + 1)
    (hs : (((M + 1 : ℕ) : ℚ) - 2 * k) ^ 2 = (M + 1 : ℕ)) :
    layerPolynomial M 1 k = 0 := by
  have hdegree : (layerPolynomial M 1 k).natDegree ≤ 0 := by
    simpa using layerPolynomial_natDegree_le M 1 k
  have htop : (layerPolynomial M 1 k).coeff 0 = 0 := by
    exact (layerPolynomial_odd_top_eq_zero_iff M 0 k (by omega) (by simpa using hk)).mpr
      (by simpa using hs)
  rw [eq_C_of_natDegree_le_zero hdegree, htop, C_0]

theorem square_not_two_mod_three (q : ℕ) : q ^ 2 % 3 ≠ 2 := by
  have hlt : q % 3 < 3 := Nat.mod_lt q (by decide)
  have hc : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hc with h | h | h <;> simp [Nat.pow_mod, h]

theorem rational_integer_square_nat_square (N k : ℕ)
    (hs : ((N : ℚ) - 2 * k) ^ 2 = N) : ∃ q : ℕ, q ^ 2 = N := by
  have hi : ((N : ℤ) - 2 * k) ^ 2 = N := by exact_mod_cast hs
  refine ⟨((N : ℤ) - 2 * k).natAbs, ?_⟩
  simpa only [Int.natAbs_pow, Int.natAbs_natCast] using congrArg Int.natAbs hi

/-- The last odd layer cannot be exceptional; this validates the next Z degree. -/
theorem exceptional_odd_lower_layer_valid (M a k : ℕ) (hj : 2 * a + 1 ≤ 2 * M)
    (_ha : 1 ≤ a)
    (hs : (((M + 2 * a + 1 : ℕ) : ℚ) - 2 * k) ^ 2 = (M + 2 * a + 1 : ℕ)) :
    a + 2 ≤ M := by
  obtain ⟨q, hq⟩ := rational_integer_square_nat_square _ k hs
  have hmod := square_not_two_mod_three q
  by_contra hbad
  have hlast : a + 1 = M := by omega
  have hvalue : q ^ 2 = 3 * M - 1 := by omega
  rw [hvalue] at hmod
  have hM : 1 ≤ M := by omega
  omega

/-- Every exceptional later odd layer loses exactly one degree. -/
theorem layerPolynomial_exceptional_odd_natDegree (M a k : ℕ)
    (hj : 2 * a + 1 ≤ 2 * M) (ha : 1 ≤ a) (hk : k ≤ M + 2 * a + 1)
    (hs : (((M + 2 * a + 1 : ℕ) : ℚ) - 2 * k) ^ 2 = (M + 2 * a + 1 : ℕ)) :
    (layerPolynomial M (2 * a + 1) k).natDegree = a - 1 := by
  have hvalid := exceptional_odd_lower_layer_valid M a k hj ha hs
  have htop : (layerPolynomial M (2 * a + 1) k).coeff a = 0 :=
    (layerPolynomial_odd_top_eq_zero_iff M a k hj hk).mpr hs
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro c hc
    by_cases hca : c = a
    · simpa [hca] using htop
    · apply coeff_eq_zero_of_natDegree_lt
      have hbound := layerPolynomial_natDegree_le M (2 * a + 1) k
      have hquot : (2 * a + 1) / 2 = a := by omega
      rw [hquot] at hbound
      omega
  · rw [layerPolynomial_coeff, ite_eq_left (by omega),
      show 2 * (2 * a + 1) - 4 * (a - 1) = 6 by omega]
    apply (mul_pos (layerScalar_pos M (2 * a + 1) (a - 1) (by omega) (by omega) (by omega))
      ?_).ne'
    apply layerCoefficient_sixth_positive
    · omega
    · simpa [Nat.add_assoc] using hk
    · simpa [Nat.add_assoc] using hs

/-- Nonexceptional odd layers retain their full top degree. -/
theorem layerPolynomial_nonexceptional_odd_natDegree (M a k : ℕ)
    (hj : 2 * a + 1 ≤ 2 * M) (hk : k ≤ M + 2 * a + 1)
    (hs : ¬ (((M + 2 * a + 1 : ℕ) : ℚ) - 2 * k) ^ 2 = (M + 2 * a + 1 : ℕ)) :
    (layerPolynomial M (2 * a + 1) k).natDegree = a := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · have h := layerPolynomial_natDegree_le M (2 * a + 1) k
    have hquot : (2 * a + 1) / 2 = a := by omega
    simpa only [hquot] using h
  · exact fun hz => hs ((layerPolynomial_odd_top_eq_zero_iff M a k hj hk).mp hz)

end PowerRank
