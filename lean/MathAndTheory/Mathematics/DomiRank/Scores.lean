module
public import MathAndTheory.Mathematics.DomiRank.Matrix
public import MathAndTheory.Mathematics.DomiRank.Stability
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MathAndTheory.DomiRank
open Matrix

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def sigmaLeft : ℝ := 251 / 1000
def sigmaRight : ℝ := 63 / 250

def scoreDenominator (s : ℝ) : ℝ :=
  let x := s - 1 / 4
  3 / 16 - 283 * x / 32 - 59 * x ^ 2 / 4 + 52 * x ^ 3 + 92 * x ^ 4 + 24 * x ^ 5

def scoreNumerators (s : ℝ) : Fin 5 → ℝ :=
  let x := s - 1 / 4
  ![3 / 4 - 247 * x / 8 - 19 * x ^ 2 / 2 + 62 * x ^ 3 + 24 * x ^ 4,
    3 / 4 - 259 * x / 8 + 13 * x ^ 2 / 2 + 86 * x ^ 3 + 24 * x ^ 4,
    1 / 4 - 123 * x / 8 + 69 * x ^ 2 / 2 + 86 * x ^ 3 + 24 * x ^ 4,
    3 / 4 - 327 * x / 8 - 99 * x ^ 2 / 2 + 62 * x ^ 3 + 24 * x ^ 4,
    5 * x / 8 + 77 * x ^ 2 / 2 + 86 * x ^ 3 + 24 * x ^ 4]

theorem sigmaLeft_pos : 0 < sigmaLeft := by norm_num [sigmaLeft]
theorem sigmaLeft_lt_sigmaRight : sigmaLeft < sigmaRight := by
  norm_num [sigmaLeft, sigmaRight]

theorem score_polynomials_pos {s : ℝ} (hl : sigmaLeft ≤ s) (hr : s ≤ sigmaRight) :
    0 < scoreDenominator s ∧ ∀ i, 0 < scoreNumerators s i := by
  let x := s - 1 / 4
  have hx : 0 < x := by dsimp [x]; norm_num [sigmaLeft] at hl; linarith
  have hxle : x ≤ (1 : ℝ) / 500 := by dsimp [x]; norm_num [sigmaRight] at hr; linarith
  have hx2 : x ^ 2 ≤ (1 : ℝ) / 250000 := by nlinarith
  have h2 : 0 ≤ x ^ 2 := sq_nonneg x
  have h3 : 0 ≤ x ^ 3 := pow_nonneg hx.le 3
  have h4 : 0 ≤ x ^ 4 := pow_nonneg hx.le 4
  have h5 : 0 ≤ x ^ 5 := pow_nonneg hx.le 5
  constructor
  · change 0 < 3 / 16 - 283 * x / 32 - 59 * x ^ 2 / 4 + 52 * x ^ 3 + 92 * x ^ 4 + 24 * x ^ 5
    nlinarith only [hxle, hx2, h3, h4, h5]
  · intro i
    fin_cases i
    all_goals
      dsimp [scoreNumerators]
      rw [show s - 1 / 4 = x from rfl]
      nlinarith only [hx, hxle, hx2, h2, h3, h4]


/-- The five vertex classes: A, K2, two triangles, the leaf hub, and its leaves. -/
def vertexClass : Fin 14 → Fin 5 :=
  ![0,1,1,2,2,2,2,2,2,3,4,4,4,4]

/-- Exact rational formulas for (I+sA)⁻¹ times the degree vector. -/
def candidateU (s : ℝ) (i : Fin 14) : ℝ :=
  scoreNumerators s (vertexClass i) / scoreDenominator s

/-- A direct polynomial certificate for the resolvent equations. -/
theorem candidateU_resolvent (s : ℝ) (hd : scoreDenominator s ≠ 0) :
    resolvent s *ᵥ candidateU s = degree := by
  rw [degree_eq]
  ext i
  fin_cases i <;>
    norm_num [resolvent, A, adjData, candidateU, vertexClass, scoreNumerators,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Pi.smul_apply]
  all_goals
    field_simp [hd]
    dsimp [scoreDenominator]
    ring

/-- The actual DomiRank score vector with dominance threshold one. -/
def gamma (s : ℝ) : Fin 14 → ℝ :=
  (resolvent s)⁻¹ *ᵥ (s • degree)

/-- The rational formulas agree with the matrix inverse definition. -/
theorem gamma_eq_candidate_of_isUnit (s : ℝ) (hu : IsUnit (resolvent s))
    (hd : scoreDenominator s ≠ 0) : gamma s = s • candidateU s := by
  letI : Invertible (resolvent s) := hu.invertible
  unfold gamma
  apply Matrix.inv_mulVec_eq_vec
  rw [Matrix.mulVec_smul, candidateU_resolvent s hd]

/-- The effective scores used by the source's algorithm. -/
def positiveScores (s : ℝ) (i : Fin 14) : ℝ := max (gamma s i) 0

/-- The normalized DomiRank distribution, using the stated truncation convention. -/
def distribution (s : ℝ) (i : Fin 14) : ℝ :=
  positiveScores s i / ∑ j, positiveScores s j

/-- The exact probabilities at the left endpoint, one value per vertex class. -/
def leftProbability : Fin 5 → ℝ :=
  ![89889445253 / 534258269542, 89703948253 / 534258269542,
    29332448253 / 534258269542, 88634445253 / 534258269542,
    82948253 / 534258269542]

/-- The exact probabilities at the right endpoint, one value per vertex class. -/
def rightProbability : Fin 5 → ℝ :=
  ![168020629 / 988469056, 167303879 / 988469056,
    107123383 / 1976938112, 81549377 / 494234528, 685883 / 1976938112]


/-- Direct exact normalization of the rational formulas at the left endpoint. -/
theorem candidate_distribution_left :
    (fun i => candidateU sigmaLeft i / ∑ j, candidateU sigmaLeft j) =
      fun i => leftProbability (vertexClass i) := by
  funext i
  fin_cases i <;>
    norm_num [candidateU, scoreNumerators, scoreDenominator, sigmaLeft,
      vertexClass, leftProbability, Fin.sum_univ_succ]

/-- Direct exact normalization of the rational formulas at the right endpoint. -/
theorem candidate_distribution_right :
    (fun i => candidateU sigmaRight i / ∑ j, candidateU sigmaRight j) =
      fun i => rightProbability (vertexClass i) := by
  funext i
  fin_cases i <;>
    norm_num [candidateU, scoreNumerators, scoreDenominator, sigmaRight,
      vertexClass, rightProbability, Fin.sum_univ_succ]

/-- On the entire comparison interval, the resolvent formulas are the DomiRank scores. -/
theorem gamma_eq_candidate {s : ℝ} (hl : sigmaLeft ≤ s) (hr : s ≤ sigmaRight) :
    gamma s = s • candidateU s := by
  have hs0 : 0 ≤ s := le_trans sigmaLeft_pos.le hl
  have hs1 : s < (4 : ℝ) / 15 := lt_of_le_of_lt hr (by norm_num [sigmaRight])
  exact gamma_eq_candidate_of_isUnit s (resolvent_isUnit s hs0 hs1)
    (ne_of_gt (score_polynomials_pos hl hr).1)

/-- Every DomiRank score is strictly positive throughout the closed interval. -/
theorem gamma_pos_on_interval {s : ℝ} (hl : sigmaLeft ≤ s) (hr : s ≤ sigmaRight) :
    ∀ i, 0 < gamma s i := by
  rw [gamma_eq_candidate hl hr]
  intro i
  change 0 < s * (scoreNumerators s (vertexClass i) / scoreDenominator s)
  exact mul_pos (lt_of_lt_of_le sigmaLeft_pos hl)
    (div_pos ((score_polynomials_pos hl hr).2 _) (score_polynomials_pos hl hr).1)

/-- The certified scores solve the original steady-state system. -/
theorem gamma_steady_state {s : ℝ} (hl : sigmaLeft ≤ s) (hr : s ≤ sigmaRight) :
    resolvent s *ᵥ gamma s = s • degree := by
  rw [gamma_eq_candidate hl hr, Matrix.mulVec_smul,
    candidateU_resolvent s (ne_of_gt (score_polynomials_pos hl hr).1)]

/-- Truncation has no effect anywhere in the interval. -/
theorem positiveScores_eq_gamma {s : ℝ} (hl : sigmaLeft ≤ s) (hr : s ≤ sigmaRight) :
    positiveScores s = gamma s := by
  funext i
  exact max_eq_left (gamma_pos_on_interval hl hr i).le

/-- Normalization cancels the common factor s in the score vector. -/
theorem distribution_eq_candidate {s : ℝ} (hl : sigmaLeft ≤ s) (hr : s ≤ sigmaRight) :
    distribution s = fun i => candidateU s i / ∑ j, candidateU s j := by
  funext i
  unfold distribution
  rw [positiveScores_eq_gamma hl hr, gamma_eq_candidate hl hr]
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (ne_of_gt (lt_of_lt_of_le sigmaLeft_pos hl))

/-- Exact normalized endpoint values, expanded across all fourteen vertices. -/
theorem distribution_eq_left :
    distribution sigmaLeft = fun i => leftProbability (vertexClass i) := by
  rw [distribution_eq_candidate le_rfl sigmaLeft_lt_sigmaRight.le]
  exact candidate_distribution_left

/-- Exact normalized endpoint values, expanded across all fourteen vertices. -/
theorem distribution_eq_right :
    distribution sigmaRight = fun i => rightProbability (vertexClass i) := by
  rw [distribution_eq_candidate sigmaLeft_lt_sigmaRight.le le_rfl]
  exact candidate_distribution_right

end
end MathAndTheory.DomiRank
