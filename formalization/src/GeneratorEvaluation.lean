module
public import GeneratorReconstruction
public import LayerIdentification
public import MainSequence
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

noncomputable section
open Polynomial
namespace PowerRank

def evalAtXYZ (x y z : ℂ) : MvPolynomial (Fin 2) ℚ[X] →+* ℂ :=
  MvPolynomial.eval₂Hom (Polynomial.aeval x).toRingHom ![y, z]

theorem evalAtXYZ_monomial (x y z : ℂ) (j c : ℕ) (P : ℚ[X]) :
    evalAtXYZ x y z (MvPolynomial.monomial (biIndex j c) P) =
      Polynomial.aeval x P * y ^ j * z ^ c := by
  have hm : MvPolynomial.monomial (biIndex j c) P =
      MvPolynomial.C P * MvPolynomial.X 0 ^ j * MvPolynomial.X 1 ^ c := by
    simp only [biIndex, MvPolynomial.C_apply, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial, zero_add, mul_one]
  rw [hm]
  simp [evalAtXYZ]

theorem evalAtXYZ_actualGenerator (x y z : ℂ) :
    evalAtXYZ x y z actualGenerator =
      (1 + x) + y * (1 - x) ^ 2 + z * y ^ 2 * (1 + x) ^ 3 := by
  rw [actualGenerator, trinomialGenerator, map_add, map_add]
  rw [show (0 : Fin 2 →₀ ℕ) = biIndex 0 0 by simp [biIndex]]
  rw [evalAtXYZ_monomial, evalAtXYZ_monomial, evalAtXYZ_monomial]
  simp
  ring

theorem evalAtXYZ_actual_mainSequence (n : ℕ) :
    evalAtXYZ ((2 : ℂ) ^ n) ((3 : ℂ) ^ n) (n : ℂ) actualGenerator = mainSequence n := by
  rw [evalAtXYZ_actualGenerator]
  have h9 : ((3 : ℂ) ^ n) ^ 2 = (9 : ℂ) ^ n := by
    calc
      _ = ((3 : ℂ) ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
      _ = _ := by norm_num
  rw [h9]
  rfl

theorem mainSequence_power_evaluation (M n : ℕ) :
    mainSequence n ^ M =
      evalAtXYZ ((2 : ℂ) ^ n) ((3 : ℂ) ^ n) (n : ℂ) (actualGenerator ^ M) := by
  rw [map_pow, evalAtXYZ_actual_mainSequence]

/-- Every X coefficient is reconstructed through its complete proven degree bound. -/
theorem eval_actualGenerator_coefficient (M j c : ℕ) (x : ℂ) :
    Polynomial.aeval x ((actualGenerator ^ M).coeff (biIndex j c)) =
      ∑ k ∈ Finset.range (M + j + 1),
        ((((actualGenerator ^ M).coeff (biIndex j c)).coeff k : ℚ) : ℂ) * x ^ k := by
  have hd := actualGenerator_coeff_natDegree_le M j c
  have hp := (((actualGenerator ^ M).coeff (biIndex j c))).as_sum_range_C_mul_X_pow'
    (n := M + j + 1) (by omega)
  have h := congrArg (fun P : ℚ[X] => Polynomial.aeval x P) hp
  simpa using h

theorem eval_actualLayerPolynomial (M j k : ℕ) (z : ℂ) :
    Polynomial.aeval z (actualLayerPolynomial M j k) =
      ∑ c ∈ Finset.range (M + 1),
        ((((actualGenerator ^ M).coeff (biIndex j c)).coeff k : ℚ) : ℂ) * z ^ c := by
  simp [actualLayerPolynomial]

def complexLayerPolynomial (M j k : ℕ) : ℂ[X] :=
  (layerPolynomial M j k).map (algebraMap ℚ ℂ)

theorem complexLayerPolynomial_eval (M j k : ℕ) (z : ℂ) :
    (complexLayerPolynomial M j k).eval z = Polynomial.aeval z (layerPolynomial M j k) := by
  rw [complexLayerPolynomial, eval_map, Polynomial.aeval_def]

/-- The full literal sequence power, with all exponential bases grouped correctly. -/
theorem mainSequence_power_expansion (M n : ℕ) :
    mainSequence n ^ M =
      ∑ j ∈ Finset.range (2 * M + 1), ∑ k ∈ Finset.range (M + j + 1),
        expPoly ((2 : ℂ) ^ k * (3 : ℂ) ^ j) (complexLayerPolynomial M j k) n := by
  classical
  rw [mainSequence_power_evaluation, actualGenerator_pow_grid, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_sum, evalAtXYZ_monomial, eval_actualGenerator_coefficient]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hjM : j ≤ 2 * M := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [expPoly, complexLayerPolynomial_eval,
    ← actualLayerPolynomial_eq_layerPolynomial M j k hjM, eval_actualLayerPolynomial]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  have hp : ((2 : ℂ) ^ k * (3 : ℂ) ^ j) ^ n =
      (((2 : ℂ) ^ n) ^ k) * (((3 : ℂ) ^ n) ^ j) := by
    simp only [mul_pow, ← pow_mul, Nat.mul_comm]
  rw [hp]
  ring

end PowerRank
