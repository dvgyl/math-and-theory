import BivariateExpansion
import LayerDegrees

noncomputable section
namespace PowerRank

theorem biIndex_eq_iff (j c j' c' : ℕ) :
    biIndex j c = biIndex j' c' ↔ j = j' ∧ c = c' := by
  constructor
  · intro h
    have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
    exact ⟨by simpa [biIndex] using h0, by simpa [biIndex] using h1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Exact coefficient extraction from the full two-binomial expansion. -/
theorem trinomialGenerator_pow_coeff {R : Type*} [CommSemiring R]
    (A B D : R) (M j c : ℕ) :
    (trinomialGenerator A B D ^ M).coeff (biIndex j c) =
      if c ≤ M ∧ 2 * c ≤ j ∧ j ≤ M + c then
        A ^ (M + c - j) * B ^ (j - 2 * c) * D ^ c *
          (M.choose c : R) * ((M - c).choose (j - 2 * c) : R) else 0 := by
  classical
  rw [trinomialGenerator_pow]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, biIndex_eq_iff]
  split_ifs with hvalid
  · rw [Finset.sum_eq_single c]
    · rw [Finset.sum_eq_single (j - 2 * c)]
      · rw [ite_eq_left (by omega)]
        rw [show M - c - (j - 2 * c) = M + c - j by omega]
      · intro b hb hne
        apply ite_eq_right
        omega
      · intro hnot
        exfalso
        apply hnot
        simp only [Finset.mem_range]
        omega
    · intro d hd hdc
      apply Finset.sum_eq_zero
      intro b hb
      exact ite_eq_right (by omega)
    · intro hnot
      exfalso
      apply hnot
      simp only [Finset.mem_range]
      omega
  · apply Finset.sum_eq_zero
    intro d hd
    apply Finset.sum_eq_zero
    intro b hb
    apply ite_eq_right
    intro heq
    apply hvalid
    have hdM : d ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
    have hbM : b ≤ M - d := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    omega

open Polynomial

def actualGenerator : MvPolynomial (Fin 2) ℚ[X] :=
  trinomialGenerator (1 + X) ((1 - X) ^ 2) ((1 + X) ^ 3)

/-- The actual generator coefficient before extracting its X coefficient. -/
theorem actualGenerator_pow_coeff (M j c : ℕ)
    (hc : c ≤ M) (hj : 2 * c ≤ j) (hupper : j ≤ M + c) :
    (actualGenerator ^ M).coeff (biIndex j c) =
      C (layerScalar M j c) *
        ((1 + X) ^ (M + j - (2 * j - 4 * c)) * (1 - X) ^ (2 * j - 4 * c)) := by
  rw [actualGenerator, trinomialGenerator_pow_coeff, ite_eq_left ⟨hc, hj, hupper⟩]
  rw [← pow_mul, ← pow_mul]
  have hB : 2 * (j - 2 * c) = 2 * j - 4 * c := by omega
  have hA : M + c - j + 3 * c = M + j - (2 * j - 4 * c) := by omega
  rw [hB]
  have hcast1 : (M.choose c : ℚ[X]) = C (M.choose c : ℚ) :=
    (map_natCast Polynomial.C _).symm
  have hcast2 : ((M - c).choose (j - 2 * c) : ℚ[X]) =
      C ((M - c).choose (j - 2 * c) : ℚ) := (map_natCast Polynomial.C _).symm
  rw [hcast1, hcast2]
  calc
    _ = ((1 + X) ^ (M + c - j) * (1 + X) ^ (3 * c)) *
        (1 - X) ^ (2 * j - 4 * c) *
        (C (M.choose c : ℚ) * C ((M - c).choose (j - 2 * c) : ℚ)) := by ring
    _ = _ := by rw [← pow_add, hA, ← map_mul]; unfold layerScalar; ring

theorem actualGenerator_pow_coeff_X (M j c k : ℕ)
    (hc : c ≤ M) (hj : 2 * c ≤ j) (hupper : j ≤ M + c) :
    ((actualGenerator ^ M).coeff (biIndex j c)).coeff k =
      layerScalar M j c * layerCoefficient (M + j) (2 * j - 4 * c) k := by
  rw [actualGenerator_pow_coeff M j c hc hj hupper, coeff_C_mul]
  rfl

end PowerRank
