import ExactSupportGapAlgebra
import RootGapCore

/-!
The exact coefficient-cap support-gap value over all finite-dimensional
normalized real coefficient vectors. This theorem concerns the actual
complete signed-sum minimum and has no probabilistic comparison inputs.
-/

noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.ExactSupportGap
open Breakthrough.GapCore

set_option maxHeartbeats 2000000

def capGapFormula (n : ℕ) (a : ℝ) : ℝ :=
  max (1 / Real.sqrt ((n : ℝ) + 2)) (a - Real.sqrt (1 - (n : ℝ) * a ^ 2))

/-- The bound for every actual gap threshold of a nonnegative vector. The
core and its variance are derived from the vector by `actual_high_gap_data`. -/
theorem signed_gap_le_formula_nonnegative {N n : ℕ} (coeff : Fin N → ℝ)
    (hn : Odd n) {a x : ℝ} (ha : 0 < a) (hna : (n : ℝ) * a ^ 2 ≤ 1)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hvar : ∑ i, coeff i ^ 2 = 1)
    (hgap : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|) :
    x ≤ capGapFormula n a := by
  by_cases hx : x ≤ 1 / Real.sqrt ((n : ℝ) + 2)
  · exact hx.trans (le_max_left _ _)
  · have hxstep : 1 / Real.sqrt ((n : ℝ) + 2) < x := not_le.mp hx
    have hx0 : 0 < x := (by positivity : 0 < 1 / Real.sqrt ((n : ℝ) + 2)).trans hxstep
    have hhalf := cap_lt_twice_of_above_step hn ha.le hna hxstep
    obtain ⟨k, V, ell, hkodd, hkpos, hV, hV1, hell, hVell, hkx, henergy, hvariance⟩ :=
      actual_high_gap_data coeff hx0 ha.le hhalf hc hcap hvar hgap
    have hkn := odd_core_count_le hkodd hn hxstep hkx
    exact (variance_cap_closure hkpos hkn ha.le hx0.le hV hvariance henergy).trans
      (le_max_right _ _)

/-- Arbitrary coefficient signs are handled by an actual Boolean-cube
bijection, with no hypothesis about an abstract symmetric law. -/
theorem signed_gap_le_formula {N n : ℕ} (coeff : Fin N → ℝ)
    (hn : Odd n) {a x : ℝ} (ha : 0 < a) (hna : (n : ℝ) * a ^ 2 ≤ 1)
    (hcap : ∀ i, |coeff i| ≤ a) (hvar : ∑ i, coeff i ^ 2 = 1)
    (hgap : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|) :
    x ≤ capGapFormula n a := by
  apply signed_gap_le_formula_nonnegative (fun i => |coeff i|) hn ha hna
    (fun i => abs_nonneg _) hcap (by simpa only [sq_abs] using hvar)
  intro ω
  have he := rademacherSum_abs_flip coeff (coefficientSignFlip coeff ω)
  rw [coefficientSignFlip_involutive coeff ω] at he
  rw [he]
  exact hgap (coefficientSignFlip coeff ω)

theorem supportGap_le_formula {N n : ℕ} (coeff : Fin N → ℝ)
    (hn : Odd n) {a : ℝ} (ha : 0 < a) (hna : (n : ℝ) * a ^ 2 ≤ 1)
    (hcap : ∀ i, |coeff i| ≤ a) (hvar : ∑ i, coeff i ^ 2 = 1) :
    supportGap coeff ≤ capGapFormula n a :=
  signed_gap_le_formula coeff hn ha hna hcap hvar
    ((le_supportGap_iff coeff (supportGap coeff)).mp le_rfl)

/-- Actual gap values, allowing every finite dimension and arbitrary real
coefficient signs. Zero coefficients are allowed. -/
def admissibleGapValues (a : ℝ) : Set ℝ :=
  {z | ∃ N : ℕ, ∃ coeff : Fin N → ℝ,
    (∀ i, |coeff i| ≤ a) ∧ (∑ i, coeff i ^ 2 = 1) ∧ supportGap coeff = z}

def maximalSupportGap (a : ℝ) : ℝ := sSup (admissibleGapValues a)

/-- The formula is an actual greatest value, not merely a limit of
coefficient vectors or an assumed optimizer. -/
theorem capGapFormula_isGreatest {n : ℕ} (hn : Odd n) {a : ℝ} (ha : 0 < a)
    (hna : (n : ℝ) * a ^ 2 ≤ 1) (hn2a : 1 ≤ ((n : ℝ) + 2) * a ^ 2) :
    IsGreatest (admissibleGapValues a) (capGapFormula n a) := by
  constructor
  · obtain ⟨N, coeff, hc, hvar, hgap⟩ := cap_formula_attained hn ha hna hn2a
    refine ⟨N, coeff, ?_, hvar, hgap⟩
    intro i
    rw [abs_of_nonneg (hc i).1]
    exact (hc i).2
  · rintro z ⟨N, coeff, hcap, hvar, heq⟩
    rw [← heq]
    exact supportGap_le_formula coeff hn ha hna hcap hvar

/-- Exact all-dimensional signed-partition discrepancy under simultaneous
quadratic normalization and coefficient cap, on every odd-index interval. -/
theorem maximalSupportGap_exact {n : ℕ} (hn : Odd n) {a : ℝ} (ha : 0 < a)
    (hna : (n : ℝ) * a ^ 2 ≤ 1) (hn2a : 1 ≤ ((n : ℝ) + 2) * a ^ 2) :
    maximalSupportGap a =
      max (1 / Real.sqrt ((n : ℝ) + 2)) (a - Real.sqrt (1 - (n : ℝ) * a ^ 2)) :=
  (capGapFormula_isGreatest hn ha hna hn2a).csSup_eq

#print axioms signed_gap_le_formula
#print axioms supportGap_le_formula
#print axioms capGapFormula_isGreatest
#print axioms maximalSupportGap_exact

end Breakthrough.ExactSupportGap
