module
public import MathAndTheory.Mathematics.DomiRank.Matrix
public import MathAndTheory.Mathematics.DomiRank.Stability
public import MathAndTheory.Mathematics.DomiRank.Spectral
public import MathAndTheory.Mathematics.DomiRank.Scores
public import MathAndTheory.Mathematics.DomiRank.Covariance
public import MathAndTheory.Mathematics.DomiRank.Entropy

/-!
A counterexample to Conjecture 4.9 of Zhang and Zhao,
arXiv:2610.00107v4, on an interval with all scores strictly positive.

The conclusion uses the theoretical probability distribution obtained by
normalizing the actual resolvent solution. The identification with the
positive-part distribution used in the computational lemmas is proved
explicitly on the whole interval, using strict positivity of every score.
-/

@[expose] public section

namespace MathAndTheory.DomiRank
open Matrix

/-- The theoretical normalization from Section 4 of the source. -/
noncomputable def theoreticalDistribution (s : ℝ) (i : Fin 14) : ℝ :=
  gamma s i / ∑ j : Fin 14, gamma s j

/-- Shannon entropy in bits of the theoretical distribution. -/
noncomputable def theoreticalEntropyBits (s : ℝ) : ℝ :=
  (-(∑ i : Fin 14,
    theoreticalDistribution s i * Real.log (theoreticalDistribution s i))) / Real.log 2

theorem gamma_sum_pos_on_interval {s : ℝ}
    (hl : sigmaLeft ≤ s) (hr : s ≤ sigmaRight) :
    0 < ∑ i : Fin 14, gamma s i := by
  exact Finset.sum_pos (fun i _ => gamma_pos_on_interval hl hr i) Finset.univ_nonempty

theorem theoreticalDistribution_pos_on_interval {s : ℝ}
    (hl : sigmaLeft ≤ s) (hr : s ≤ sigmaRight) (i : Fin 14) :
    0 < theoreticalDistribution s i := by
  exact div_pos (gamma_pos_on_interval hl hr i) (gamma_sum_pos_on_interval hl hr)

theorem theoreticalDistribution_sum_on_interval {s : ℝ}
    (hl : sigmaLeft ≤ s) (hr : s ≤ sigmaRight) :
    ∑ i : Fin 14, theoreticalDistribution s i = 1 := by
  simp only [theoreticalDistribution, div_eq_mul_inv, ← Finset.sum_mul]
  simpa only [div_eq_mul_inv] using div_self (gamma_sum_pos_on_interval hl hr).ne'

/-- All scores remain positive throughout the counterexample interval,
so the positive-part normalization is exactly the theoretical one. -/
theorem distribution_eq_theoretical {s : ℝ}
    (hl : sigmaLeft ≤ s) (hr : s ≤ sigmaRight) :
    distribution s = theoreticalDistribution s := by
  have hp : ∀ i : Fin 14, positiveScores s i = gamma s i := by
    intro i
    exact max_eq_left (gamma_pos_on_interval hl hr i).le
  funext i
  simp only [distribution, theoreticalDistribution, hp]

theorem entropyBits_eq_theoretical {s : ℝ}
    (hl : sigmaLeft ≤ s) (hr : s ≤ sigmaRight) :
    entropyBits s = theoreticalEntropyBits s := by
  simp only [entropyBits, entropyNats, theoreticalEntropyBits,
    distribution_eq_theoretical hl hr]

/-- Positive definiteness certifies that every parameter is in the stable
spectral domain of DomiRank, without numerical eigenvalue approximations. -/
theorem resolvent_posDef_on_interval {s : ℝ}
    (hl : sigmaLeft ≤ s) (hr : s ≤ sigmaRight) :
    (resolvent s).PosDef := by
  apply resolvent_posDef s (sigmaLeft_pos.le.trans hl)
  exact hr.trans_lt (by norm_num [sigmaRight])

/-- The spectral condition from the paper holds for every negative
eigenvalue, and hence for its smallest eigenvalue, throughout the interval. -/
theorem spectral_bound_on_interval {s lam : ℝ} {v : Fin 14 → ℝ}
    (hl : sigmaLeft ≤ s) (hr : s ≤ sigmaRight)
    (hlam : lam < 0) (hv : v ≠ 0) (heig : A *ᵥ v = lam • v) :
    s < -1 / lam := by
  exact parameter_lt_neg_inv_eigenvalue
    (resolvent_posDef_on_interval hl hr) hlam hv heig

theorem theoretical_entropy_strict_increase :
    theoreticalEntropyBits sigmaLeft < theoreticalEntropyBits sigmaRight := by
  rw [← entropyBits_eq_theoretical le_rfl sigmaLeft_lt_sigmaRight.le,
    ← entropyBits_eq_theoretical sigmaLeft_lt_sigmaRight.le le_rfl]
  exact entropyBits_strict_increase

/-- The full explicit witness: connectedness, strict structural disassortativity,
strictly ordered positive parameters, stability and positivity on the whole
closed interval, and an entropy increase. -/
theorem fourteen_vertex_counterexample :
    graph.Connected ∧
    degreeLogCovarianceBits < 0 ∧
    0 < sigmaLeft ∧ sigmaLeft < sigmaRight ∧
    (∀ s ∈ Set.Icc sigmaLeft sigmaRight,
      (resolvent s).PosDef ∧ ∀ i : Fin 14, 0 < gamma s i) ∧
    theoreticalEntropyBits sigmaLeft < theoreticalEntropyBits sigmaRight := by
  refine ⟨graph_connected, degreeLogCovarianceBits_neg,
    sigmaLeft_pos, sigmaLeft_lt_sigmaRight, ?_, theoretical_entropy_strict_increase⟩
  intro s hs
  exact ⟨resolvent_posDef_on_interval hs.1 hs.2,
    gamma_pos_on_interval hs.1 hs.2⟩

/-- The interval-monotonicity property asserted for every connected graph
with non-positive degree--log-degree covariance in Conjecture 4.9. This
specialization to our fixed graph already suffices to refute the assertion. -/
def NonincreasingOnPositiveIntervals : Prop :=
  ∀ a b : ℝ, 0 < a → a < b →
    (∀ s ∈ Set.Icc a b,
      (resolvent s).PosDef ∧ ∀ i : Fin 14, 0 < gamma s i) →
    theoreticalEntropyBits b ≤ theoreticalEntropyBits a

/-- A connected, structurally disassortative graph fails the conjectured
monotonicity even on an interval of strictly positive DomiRank scores. -/
theorem refined_conjecture_false_for_graph :
    graph.Connected ∧ degreeLogCovarianceBits ≤ 0 ∧
      ¬ NonincreasingOnPositiveIntervals := by
  refine ⟨graph_connected, degreeLogCovarianceBits_neg.le, ?_⟩
  intro h
  have hle := h sigmaLeft sigmaRight sigmaLeft_pos sigmaLeft_lt_sigmaRight
    (fun s hs => ⟨resolvent_posDef_on_interval hs.1 hs.2,
      gamma_pos_on_interval hs.1 hs.2⟩)
  exact (not_le_of_gt theoretical_entropy_strict_increase) hle

#print axioms fourteen_vertex_counterexample
#print axioms refined_conjecture_false_for_graph

end MathAndTheory.DomiRank
