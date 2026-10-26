module
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathAndTheory.Mathematics.DomiRank.Conclusion
/-!
Conjecture 4.9 of Zhang and Zhao, arXiv:2610.00107v4, predicts decreasing
entropy on positive-score intervals when the degree--log-degree covariance
is nonpositive. The fixed graph below has 14 vertices and 32 edges.
All definitions use the original adjacency, resolvent, and entropy formulas.
-/
@[expose] public section
noncomputable section
namespace DomiRankProblem
open Matrix

set_option maxHeartbeats 2000000

def edgeSeed (i j : Fin 14) : Prop :=
  (i = 1 ∧ j = 2) ∨
  (3 ≤ i ∧ i < j ∧ j ≤ 5) ∨
  (6 ≤ i ∧ i < j ∧ j ≤ 8) ∨
  (i ≤ 2 ∧ 3 ≤ j ∧ j ≤ 9) ∨
  (i = 9 ∧ 10 ≤ j)

def graph : SimpleGraph (Fin 14) := SimpleGraph.fromRel edgeSeed

instance : DecidableRel graph.Adj := by
  classical
  exact fun _ _ => inferInstance

def adjacency : Matrix (Fin 14) (Fin 14) ℝ := graph.adjMatrix ℝ

def degree : Fin 14 → ℝ := adjacency *ᵥ (fun _ => 1)

def covariance : ℝ :=
  (∑ i, (adjacency *ᵥ degree) i * Real.log (degree i)) / (∑ i, degree i) -
  ((∑ i, degree i ^ 2) / (∑ i, degree i) ^ 2) *
    (∑ i, degree i * Real.log (degree i))

def scores (s : ℝ) : Fin 14 → ℝ :=
  (1 + s • adjacency)⁻¹ *ᵥ (s • degree)

def probability (s : ℝ) (i : Fin 14) : ℝ := scores s i / ∑ j, scores s j

def entropy (s : ℝ) : ℝ := -∑ i, probability s i * Real.log (probability s i)

-- Natural logarithms are used. Division by log 2 gives entropy in bits.
theorem counterexample :
    graph.Connected ∧ covariance < 0 ∧
    (∀ s ∈ Set.Icc (251 / 1000 : ℝ) (63 / 250),
      (1 + s • adjacency).PosDef ∧ (∀ i, 0 < scores s i) ∧
      ∀ (lam : ℝ) (v : Fin 14 → ℝ), lam < 0 → v ≠ 0 →
        adjacency *ᵥ v = lam • v → s < -1 / lam) ∧
    entropy (251 / 1000) + (1 / 10000 : ℝ) < entropy (63 / 250) := by
  have hg : graph = MathAndTheory.DomiRank.graph := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [graph, SimpleGraph.fromRel_adj, edgeSeed,
        MathAndTheory.DomiRank.graph, MathAndTheory.DomiRank.adjData]
  have hA : adjacency = MathAndTheory.DomiRank.A := by
    ext i j
    change (if graph.Adj i j then (1 : ℝ) else 0) = MathAndTheory.DomiRank.A i j
    fin_cases i <;> fin_cases j <;>
      norm_num [graph,
        SimpleGraph.fromRel_adj, edgeSeed,
        MathAndTheory.DomiRank.A, MathAndTheory.DomiRank.adjData]
  have hd : degree = MathAndTheory.DomiRank.degree := by
    rw [degree, hA]
    rfl
  have hc : covariance = MathAndTheory.DomiRank.degreeLogCovarianceNats := by
    simp only [covariance, hA, hd, MathAndTheory.DomiRank.degreeLogCovarianceNats]
  have hs (s : ℝ) : scores s = MathAndTheory.DomiRank.gamma s := by
    simp only [scores, hA, hd, MathAndTheory.DomiRank.gamma,
      MathAndTheory.DomiRank.resolvent]
  have he (s : ℝ) (hl : MathAndTheory.DomiRank.sigmaLeft ≤ s)
      (hr : s ≤ MathAndTheory.DomiRank.sigmaRight) :
      entropy s = MathAndTheory.DomiRank.entropyNats s := by
    simp only [entropy, probability, hs, MathAndTheory.DomiRank.entropyNats,
      MathAndTheory.DomiRank.distribution_eq_theoretical hl hr,
      MathAndTheory.DomiRank.theoreticalDistribution]
  refine ⟨hg ▸ MathAndTheory.DomiRank.graph_connected, ?_, ?_, ?_⟩
  · rw [hc]
    exact MathAndTheory.DomiRank.degreeLogCovarianceNats_neg
  · intro s h
    have hl : MathAndTheory.DomiRank.sigmaLeft ≤ s := h.1
    have hr : s ≤ MathAndTheory.DomiRank.sigmaRight := h.2
    rw [hA, hs]
    refine ⟨MathAndTheory.DomiRank.resolvent_posDef_on_interval hl hr,
      MathAndTheory.DomiRank.gamma_pos_on_interval hl hr, ?_⟩
    intro lam v hlam hv heig
    exact MathAndTheory.DomiRank.spectral_bound_on_interval hl hr hlam hv heig
  · change entropy MathAndTheory.DomiRank.sigmaLeft + (1 / 10000 : ℝ) <
      entropy MathAndTheory.DomiRank.sigmaRight
    rw [he _ le_rfl MathAndTheory.DomiRank.sigmaLeft_lt_sigmaRight.le,
      he _ MathAndTheory.DomiRank.sigmaLeft_lt_sigmaRight.le le_rfl]
    exact MathAndTheory.DomiRank.entropyNats_gap

end DomiRankProblem
