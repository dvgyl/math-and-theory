module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

public section

/-!
# A counterexample to the best-of-n win-rate--KL conjecture

The finite sample space is ordered by reward. `bestOfN` is the exact law
of the largest of n independent draws, expressed through the two cumulative
probabilities. Win rate uses half credit for equal responses; `kl` is the
usual KL divergence with natural logarithms.

The main result `universal_curve_false` is an unconditional disproof of the
universal curve, with a four-response best-of-two witness. Its logarithmic
inequality is proved in Lean over the actual real logarithm, using a finite
rational comparison and the standard analytic log lower bound.

The more general every-budget/small-atom extension in the accompanying
manuscript is not asserted to be formalized by this file.

See AUTHORSHIP.md for the AI-assistance disclosure.
-/

noncomputable section

namespace MathAndTheory.BestOfN

open scoped BigOperators

/-- Reference mass strictly below the response i. -/
@[expose] def before {k : ℕ} (p : Fin k → ℝ) (i : Fin k) : ℝ :=
  ∑ j : Fin k, if j < i then p j else 0

/-- Reference mass at or below the response i. -/
@[expose] def through {k : ℕ} (p : Fin k → ℝ) (i : Fin k) : ℝ :=
  ∑ j : Fin k, if j ≤ i then p j else 0

/-- Exact selected probabilities for independent best-of-n sampling. -/
@[expose] def bestOfN {k : ℕ} (n : ℕ) (p : Fin k → ℝ) (i : Fin k) : ℝ :=
  through p i ^ n - before p i ^ n

/-- Direct enumeration of the independent two-draw experiment. -/
@[expose] def twoDrawMass {k : ℕ} (p : Fin k → ℝ) (i : Fin k) : ℝ :=
  ∑ a : Fin k, ∑ b : Fin k,
    if max a.val b.val = i.val then p a * p b else 0

/-- The half-credit win probability of q against an independent p. -/
@[expose] def winRate {k : ℕ} (q p : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, q i * (before p i + p i / 2)

/-- Kullback--Leibler divergence, selected law first. -/
@[expose] def kl {k : ℕ} (q p : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, q i * Real.log (q i / p i)

/-- The proposed continuous-reference tradeoff curve. -/
@[expose] def ell (w : ℝ) : ℝ := Real.log (w / (1 - w)) + 1 / w - 2

theorem ell_hasDerivAt {w : ℝ} (hw : 0 < w) (hw1 : w < 1) :
    HasDerivAt ell ((2 * w - 1) / (w ^ 2 * (1 - w))) w := by
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hden : 1 - w ≠ 0 := ne_of_gt (sub_pos.mpr hw1)
  have hid := hasDerivAt_id w
  have hsub := (hasDerivAt_const w (1 : ℝ)).sub hid
  have hquot := hid.div hsub hden
  have hlog := hquot.log (div_ne_zero hw0 hden)
  have hinv := (hasDerivAt_const w (1 : ℝ)).div hid hw0
  have h := (hlog.add hinv).sub_const 2
  convert h using 1
  · ext x
    dsimp [ell]
  · dsimp [ell]
    field_simp [hw0, hden]
    ring

/-- Strict monotonicity justifies the inverse-curve formulation on its intended domain. -/
theorem ell_strictMonoOn : StrictMonoOn ell (Set.Ico (1 / 2 : ℝ) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ico (1 / 2 : ℝ) 1) ?_ ?_
  · intro w hw
    exact (ell_hasDerivAt (by linarith [hw.1]) hw.2).continuousAt.continuousWithinAt
  · intro w hw
    rw [interior_Ico] at hw
    rw [(ell_hasDerivAt (by linarith [hw.1]) hw.2).deriv]
    exact div_pos (by linarith [hw.1])
      (mul_pos (sq_pos_of_pos (by linarith [hw.1])) (sub_pos.mpr hw.2))

/-- Four responses in strictly increasing reward order. -/
@[expose] def reference : Fin 4 → ℝ := ![2 / 5, 1 / 5, 1 / 5, 1 / 5]

theorem reference_positive (i : Fin 4) : 0 < reference i := by
  fin_cases i <;> norm_num [reference]

theorem reference_sum : (∑ i : Fin 4, reference i) = 1 := by
  norm_num [reference, Fin.sum_univ_succ]

theorem before_reference : before reference = ![0, 2 / 5, 3 / 5, 4 / 5] := by
  funext i
  fin_cases i <;> norm_num [before, reference, Fin.sum_univ_succ, Fin.lt_def]

theorem through_reference : through reference = ![2 / 5, 3 / 5, 4 / 5, 1] := by
  funext i
  fin_cases i <;> norm_num [through, reference, Fin.sum_univ_succ, Fin.le_def]

theorem selected_probabilities :
    bestOfN 2 reference = ![4 / 25, 5 / 25, 7 / 25, 9 / 25] := by
  funext i
  fin_cases i <;> norm_num [bestOfN, before_reference, through_reference]

/-- The finite reward-max table; its entries are natural-number rewards. -/
@[expose] def maxTable : Fin 4 → Fin 4 → ℕ :=
  ![![0, 1, 2, 3], ![1, 1, 2, 3], ![2, 2, 2, 3], ![3, 3, 3, 3]]

theorem maxTable_correct (a b : Fin 4) : max a.val b.val = maxTable a b := by
  fin_cases a <;> fin_cases b <;> rfl

/-- The CDF law agrees with direct enumeration of all sixteen sample pairs. -/
theorem selected_equals_independent_sampling :
    bestOfN 2 reference = twoDrawMass reference := by
  rw [selected_probabilities]
  funext i
  unfold twoDrawMass
  simp_rw [maxTable_correct]
  fin_cases i <;>
    norm_num [maxTable, reference, Fin.sum_univ_succ]

theorem selected_positive (i : Fin 4) : 0 < bestOfN 2 reference i := by
  rw [selected_probabilities]
  fin_cases i <;> norm_num

theorem selected_sum : (∑ i : Fin 4, bestOfN 2 reference i) = 1 := by
  rw [selected_probabilities]
  norm_num [Fin.sum_univ_succ]

theorem win_rate_exact :
    winRate (bestOfN 2 reference) reference = 163 / 250 := by
  rw [selected_probabilities]
  unfold winRate
  rw [before_reference]
  norm_num [reference, Fin.sum_univ_succ]

theorem win_rate_in_domain :
    (1 / 2 : ℝ) ≤ winRate (bestOfN 2 reference) reference ∧
      winRate (bestOfN 2 reference) reference < 1 := by
  rw [win_rate_exact]
  norm_num

theorem kl_exact :
    kl (bestOfN 2 reference) reference =
      (4 / 25) * Real.log (2 / 5) + (7 / 25) * Real.log (7 / 5) +
      (9 / 25) * Real.log (9 / 5) := by
  rw [selected_probabilities]
  norm_num [kl, reference, Fin.sum_univ_succ]
  <;> ring

theorem ell_exact :
    ell (winRate (bestOfN 2 reference) reference) =
      Real.log (163 / 87) - 76 / 163 := by
  rw [win_rate_exact]
  norm_num [ell]
  <;> ring

/-- A positive rational whose logarithm combines the four required logs. -/
@[expose] def ratio : ℝ :=
  ((163 / 87) ^ 25 * (5 / 2) ^ 4) / ((7 / 5) ^ 7 * (9 / 5) ^ 9)

theorem ratio_positive : 0 < ratio := by
  unfold ratio
  positivity

-- A pure rational certificate; `norm_num` constructs kernel-checked terms.
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 2000 in
theorem ratio_lower_bound : (120 / 119 : ℝ) ^ 1400 < ratio := by
  norm_num [ratio]

theorem log_ratio_lower_bound : (35 / 3 : ℝ) < Real.log ratio := by
  have hlog : (1 / 120 : ℝ) ≤ Real.log (120 / 119 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 120 / 119 by norm_num)
    norm_num at h ⊢
    exact h
  calc
    (35 / 3 : ℝ) = 1400 * (1 / 120 : ℝ) := by norm_num
    _ ≤ 1400 * Real.log (120 / 119 : ℝ) := by linarith
    _ = Real.log ((120 / 119 : ℝ) ^ 1400) := by
      rw [Real.log_pow]
      norm_num
    _ < Real.log ratio := Real.log_lt_log (by positivity) ratio_lower_bound

theorem log_ratio_identity :
    Real.log ratio =
      25 * Real.log (163 / 87) + 4 * Real.log (5 / 2) -
      7 * Real.log (7 / 5) - 9 * Real.log (9 / 5) := by
  unfold ratio
  rw [Real.log_div (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  norm_num
  <;> ring

theorem inverse_log_identity : Real.log (2 / 5 : ℝ) = -Real.log (5 / 2 : ℝ) := by
  have h : (2 / 5 : ℝ) = (5 / 2 : ℝ)⁻¹ := by norm_num
  rw [h, Real.log_inv]

theorem gap_identity :
    ell (winRate (bestOfN 2 reference) reference) -
        kl (bestOfN 2 reference) reference =
      Real.log ratio / 25 - 76 / 163 := by
  rw [ell_exact, kl_exact, inverse_log_identity, log_ratio_identity]
  ring

/-- A strictly positive rational lower bound for the actual transcendental gap. -/
theorem gap_positive :
    (1 / 2445 : ℝ) <
      ell (winRate (bestOfN 2 reference) reference) -
        kl (bestOfN 2 reference) reference := by
  rw [gap_identity]
  have h := log_ratio_lower_bound
  linarith

/-- The finite best-of-two counterexample to the proposed win-rate--KL curve. -/
theorem explicit_counterexample :
    kl (bestOfN 2 reference) reference <
      ell (winRate (bestOfN 2 reference) reference) := by
  have h := gap_positive
  linarith

/-- Nonnegativity of finite KL divergence for positive, normalized distributions. -/
theorem kl_nonneg {k : ℕ} {p q : Fin k → ℝ}
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hpsum : (∑ i : Fin k, p i) = 1) (hqsum : (∑ i : Fin k, q i) = 1) :
    0 ≤ kl q p := by
  have hterm (i : Fin k) : q i - p i ≤ q i * Real.log (q i / p i) := by
    calc
      q i - p i = q i * (1 - (q i / p i)⁻¹) := by
        field_simp [ne_of_gt (hp i), ne_of_gt (hq i)]
        <;> ring
      _ ≤ q i * Real.log (q i / p i) :=
        mul_le_mul_of_nonneg_left
          (Real.one_sub_inv_le_log_of_pos (div_pos (hq i) (hp i))) (le_of_lt (hq i))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simpa only [Finset.sum_sub_distrib, hqsum, hpsum, sub_self, kl] using hsum

/-- Every inverse-curve point in the correct domain lies strictly below the true win rate. -/
theorem inverse_curve_violation {u : ℝ}
    (hu : u ∈ Set.Ico (1 / 2 : ℝ) 1)
    (heq : ell u = kl (bestOfN 2 reference) reference) :
    u < winRate (bestOfN 2 reference) reference := by
  by_contra hn
  have hwle : winRate (bestOfN 2 reference) reference ≤ u := le_of_not_gt hn
  have hmono := ell_strictMonoOn.monotoneOn win_rate_in_domain hu hwle
  rw [heq] at hmono
  exact (not_le_of_gt explicit_counterexample) hmono

/-- An inverse-curve point exists and is strictly below the actual best-of-two win rate. -/
theorem inverse_curve_exists :
    ∃ u : ℝ, u ∈ Set.Ico (1 / 2 : ℝ) 1 ∧
      ell u = kl (bestOfN 2 reference) reference ∧
      u < winRate (bestOfN 2 reference) reference := by
  have hzero : ell (1 / 2 : ℝ) = 0 := by norm_num [ell]
  have hcont : ContinuousOn ell
      (Set.Icc (1 / 2 : ℝ) (winRate (bestOfN 2 reference) reference)) := by
    intro w hw
    exact (ell_hasDerivAt (by linarith [hw.1])
      (lt_of_le_of_lt hw.2 win_rate_in_domain.2)).continuousAt.continuousWithinAt
  have hmem : kl (bestOfN 2 reference) reference ∈
      Set.Icc (ell (1 / 2 : ℝ)) (ell (winRate (bestOfN 2 reference) reference)) := by
    constructor
    · rw [hzero]
      exact kl_nonneg reference_positive selected_positive reference_sum selected_sum
    · exact le_of_lt explicit_counterexample
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc win_rate_in_domain.1 hcont hmem
  have hudom : u ∈ Set.Ico (1 / 2 : ℝ) 1 :=
    ⟨hu.1, lt_of_le_of_lt hu.2 win_rate_in_domain.2⟩
  exact ⟨u, hudom, heq, inverse_curve_violation hudom heq⟩

/-- The exact universal statement in its KL-versus-win-rate formulation. -/
@[expose] def UniversalCurve : Prop :=
  ∀ (k n : ℕ) (p : Fin k → ℝ),
    1 ≤ n → (∀ i, 0 < p i) → (∑ i : Fin k, p i) = 1 →
    ((1 / 2 : ℝ) ≤ winRate (bestOfN n p) p ∧ winRate (bestOfN n p) p < 1) →
    ell (winRate (bestOfN n p) p) ≤ kl (bestOfN n p) p

/-- There is no universally valid bound of the conjectured form. -/
theorem universal_curve_false : ¬ UniversalCurve := by
  intro h
  have hw := h 4 2 reference (by norm_num) reference_positive reference_sum win_rate_in_domain
  exact (not_le_of_gt explicit_counterexample) hw

end MathAndTheory.BestOfN
