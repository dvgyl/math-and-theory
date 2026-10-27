import PermEntropy.MainFactorial

noncomputable section
namespace PermEntropy
namespace FinDist

/-- Every pair has an absolute probability bias at least ε. No transitivity,
independence, or lower bound on the number of labels is assumed. -/
theorem entropy_of_pairwise_bias_all {V : Type*} [Fintype V] [DecidableEq V]
    (p : FinDist (Ranking V)) (ε : ℝ) (hε : 0 < ε)
    (hbias : ∀ u v : V, u ≠ v → ε ≤ |p.precedesProbability u v - 1 / 2|) :
    p.entropy ≤ (1 - ε^4 / 144) * Real.log ((Fintype.card V).factorial : ℝ) := by
  have h := p.entropy_quartic_log_factorial_all (2 * ε) (by positivity)
    (fun u v huv => (p.probability_bias_iff_meanComparison huv ε).mp (hbias u v huv))
  have hc : 1 - (2 * ε)^4 / 2304 = 1 - ε^4 / 144 := by ring
  simpa only [hc] using h

end FinDist
end PermEntropy
