import PureECQC.Raw
import PureECQC.Entropy
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# A complete pure-state counterexample to the five-dimensional ECQC conjecture

This module connects the explicitly normalized quantum state and six unitary
measurement bases to their actual Born probabilities, Shannon mutual
informations, and the continuous-functional-calculus von Neumann entropy.
`none` denotes the computational basis and `some a` the quadratic basis.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace ECQC5

theorem cc_normSq : Complex.normSq cc = 1 / 5 := by
  rw [cc, Complex.normSq_ofReal]
  nlinarith [c_sq]

theorem shift_eq_double (x : Q) : shift x = double x := rfl

theorem shift_eq_two_mul (x : Q) : shift x = 2 * x := by
  fin_cases x <;> decide

/-- Coefficients of an actual normalized measurement vector. -/
def measurementVec : Option Q → Q → Q → ℂ
  | none, k, x => if x = k then 1 else 0
  | some a, k, x => cc * rawBasis zeta a k x

/-- Inner product between two measurement vectors. -/
def overlap (b b' : Option Q) (i j : Q) : ℂ :=
  ∑ x : Q, star (measurementVec b i x) * measurementVec b' j x

/-- A matrix whose columns are the measurement vectors. -/
def basisMatrix (b : Option Q) : Matrix Q Q ℂ := fun x i => measurementVec b i x

theorem overlap_some (a b i j : Q) :
    overlap (some a) (some b) i j = (cc * cc) * rawOverlap zeta a b i j := by
  unfold overlap rawOverlap
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [measurementVec, star_mul, cc_star]
  ring

theorem overlap_none_some (a i j : Q) :
    overlap none (some a) i j = cc * rawBasis zeta a j i := by
  simp [overlap, measurementVec]

theorem overlap_some_none (a i j : Q) :
    overlap (some a) none i j = star (cc * rawBasis zeta a i j) := by
  simp [overlap, measurementVec]

theorem overlap_same (b : Option Q) (i j : Q) :
    overlap b b i j = if i = j then 1 else 0 := by
  cases b with
  | none =>
      by_cases h : i = j
      · subst j
        simp [overlap, measurementVec]
      · simp [overlap, measurementVec, h, Ne.symm h]
  | some a =>
      rw [overlap_some, rawOverlap_same zeta_fifth zeta_sum zeta_star, cc_mul]
      split <;> norm_num

/-- All six measurement matrices are unitary, so their columns are bases. -/
theorem bases_unitary (b : Option Q) : basisMatrix b ∈ Matrix.unitaryGroup Q ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  change overlap b b i j = (1 : Matrix Q Q ℂ) i j
  rw [overlap_same]
  simp [Matrix.one_apply]

/-- Distinct settings are mutually unbiased in the usual squared-overlap sense. -/
theorem bases_mutually_unbiased (b b' : Option Q) (hne : b ≠ b') (i j : Q) :
    Complex.normSq (overlap b b' i j) = 1 / 5 := by
  cases b with
  | none =>
      cases b' with
      | none => exact (hne rfl).elim
      | some a =>
          rw [overlap_none_some, map_mul, cc_normSq,
            raw_normSq_one zeta_fifth zeta_star]
          ring
  | some a =>
      cases b' with
      | none =>
          rw [overlap_some_none]
          simp only [Complex.star_def, Complex.normSq_conj, map_mul, cc_normSq,
            raw_normSq_one zeta_fifth zeta_star, mul_one]
      | some a' =>
          have ha : a ≠ a' := fun h => hne (congrArg some h)
          rw [overlap_some, map_mul, map_mul, cc_normSq,
            rawOverlap_different zeta_fifth zeta_sum zeta_star a a' i j ha]
          norm_num

/-- The actual bipartite Born amplitude for matching local basis settings. -/
def bornAmplitude (b : Option Q) (i j : Q) : ℂ :=
  ∑ p : QQ, star (measurementVec b i p.1) * star (measurementVec b j p.2) * psi p

/-- The actual Born probability, defined as squared modulus of the amplitude. -/
def bornProb (b : Option Q) (i j : Q) : ℝ := Complex.normSq (bornAmplitude b i j)

theorem bornAmplitude_collapse (b : Option Q) (i j : Q) :
    bornAmplitude b i j =
      cc * ∑ x : Q, star (measurementVec b i x) * star (measurementVec b j (shift x)) := by
  unfold bornAmplitude
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp [psi, mul_ite, Finset.sum_ite_eq', mul_comm, mul_left_comm, mul_assoc]

theorem bornAmplitude_some (a i j : Q) :
    bornAmplitude (some a) i j = cc * (cc * cc) * rawBorn zeta a i j := by
  rw [bornAmplitude_collapse]
  unfold rawBorn
  simp only [measurementVec, star_mul, cc_star, shift_eq_double]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Every basis yields exactly the same permutation-correlated amplitude. -/
theorem bornAmplitude_formula (b : Option Q) (i j : Q) :
    bornAmplitude b i j = if j = shift i then cc else 0 := by
  cases b with
  | none =>
      rw [bornAmplitude_collapse]
      have hs : (∑ x : Q, star (measurementVec none i x) *
          star (measurementVec none j (shift x))) =
          if j = shift i then 1 else 0 := by
        calc
          _ = ∑ x : Q, if x = i then (if j = shift i then (1 : ℂ) else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x = i
            · subst x
              simp [measurementVec, eq_comm]
            · simp [measurementVec, hx]
          _ = _ := by simp
      rw [hs]
      split <;> simp
  | some a =>
      rw [bornAmplitude_some, rawBorn_formula zeta_fifth zeta_sum zeta_star, cc_mul]
      simp only [← shift_eq_double]
      split <;> simp

/-- Exact identification of the genuine Born table with the checked probability table. -/
theorem bornProb_eq_table (b : Option Q) : bornProb b = tableZ := by
  funext i j
  rw [bornProb, bornAmplitude_formula]
  simp only [shift_eq_two_mul, tableZ]
  split <;> simp [cc_normSq]

theorem bornProb_nonneg (b : Option Q) (i j : Q) : 0 ≤ bornProb b i j := by
  rw [bornProb_eq_table]
  exact tableZ_nonneg i j

theorem bornProb_normalized (b : Option Q) : (∑ i, ∑ j, bornProb b i j) = 1 := by
  rw [bornProb_eq_table]
  exact tableZ_normalized

theorem bornProb_classicalMI (b : Option Q) : classicalMI (bornProb b) = Real.log 5 := by
  rw [bornProb_eq_table]
  exact tableZ_classicalMI

/-- The actual measurement score in the ECQC statement. -/
def actualScore (S : Finset (Option Q)) : ℝ := ∑ b ∈ S, classicalMI (bornProb b)

theorem actualScore_eq (S : Finset (Option Q)) (hS : S.card = 5) :
    actualScore S = 5 * Real.log 5 := by
  unfold actualScore
  simp_rw [bornProb_classicalMI]
  simp [hS]

theorem actualScore_strictly_exceeds_quantumMI
    (S : Finset (Option Q)) (hS : S.card = 5) : quantumMI < actualScore S := by
  rw [quantumMI_eq, actualScore_eq S hS]
  have hlog : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  linarith

/-- No permitted subset can satisfy the proposed ECQC inequality. -/
theorem pure_state_ECQC_counterexample :
    (∑ p : QQ, star (psi p) * psi p) = 1 ∧
    rho.PosSemidef ∧ Matrix.trace rho = 1 ∧ rho * rho = rho ∧
    Fintype.card (Option Q) = 6 ∧
    (∀ b : Option Q, basisMatrix b ∈ Matrix.unitaryGroup Q ℂ) ∧
    (∀ b b' : Option Q, b ≠ b' → ∀ i j : Q,
      Complex.normSq (overlap b b' i j) = 1 / 5) ∧
    (∀ b : Option Q, bornProb b = tableZ) ∧
    quantumMI = 2 * Real.log 5 ∧
    (∃ S : Finset (Option Q), S.card = 5) ∧
    (∀ S : Finset (Option Q), S.card = 5 →
      actualScore S = 5 * Real.log 5 ∧ quantumMI < actualScore S) := by
  refine ⟨psi_norm, rho_positive, rho_trace, rho_idempotent, by decide,
    bases_unitary, bases_mutually_unbiased, bornProb_eq_table, quantumMI_eq,
    five_settings_exist, ?_⟩
  intro S hS
  exact ⟨actualScore_eq S hS, actualScore_strictly_exceeds_quantumMI S hS⟩

theorem no_actual_five_setting_budget :
    ¬ ∃ S : Finset (Option Q), S.card = 5 ∧ actualScore S ≤ quantumMI := by
  rintro ⟨S, hS, hb⟩
  exact (not_le_of_gt (actualScore_strictly_exceeds_quantumMI S hS)) hb

/-- The same physical inequality in bits, as used in the original paper. -/
theorem actualScore_bits_violation (S : Finset (Option Q)) (hS : S.card = 5) :
    quantumMI / Real.log 2 = 2 * (Real.log 5 / Real.log 2) ∧
    actualScore S / Real.log 2 = 5 * (Real.log 5 / Real.log 2) ∧
    quantumMI / Real.log 2 < actualScore S / Real.log 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [quantumMI_eq]; ring
  · rw [actualScore_eq S hS]; ring
  · exact div_lt_div_of_pos_right (actualScore_strictly_exceeds_quantumMI S hS)
      (Real.log_pos (by norm_num))

#print axioms ECQC5.bases_unitary
#print axioms ECQC5.bases_mutually_unbiased
#print axioms ECQC5.bornProb_eq_table
#print axioms ECQC5.pure_state_ECQC_counterexample
#print axioms ECQC5.no_actual_five_setting_budget
#print axioms ECQC5.actualScore_bits_violation

end ECQC5
