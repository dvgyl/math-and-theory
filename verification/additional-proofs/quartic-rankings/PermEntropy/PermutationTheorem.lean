import PermEntropy.TheoremAll
import PermEntropy.RankingEquiv

/-! # The quartic entropy bound for position-valued permutations

This is the same theorem with a ranking represented by an equivalence from
the labels to their positions. The event in the hypothesis is literally
`e u < e v`; the equivalence with the list model is proved in `RankingEquiv`.
-/

noncomputable section
namespace PermEntropy
namespace FinDist

theorem entropy_of_pairwise_bias_equiv_all {V : Type*} [Fintype V] [DecidableEq V]
    (p : FinDist (V ≃ Fin (Fintype.card V))) (ε : ℝ) (hε : 0 < ε)
    (hbias : ∀ u v : V, u ≠ v →
      ε ≤ |p.expect (fun e => if e u < e v then (1 : ℝ) else 0) - 1 / 2|) :
    p.entropy ≤ (1 - ε^4 / 144) * Real.log ((Fintype.card V).factorial : ℝ) := by
  have hb : ∀ u v : V, u ≠ v →
      ε ≤ |(p.map Ranking.ofEquiv).precedesProbability u v - 1 / 2| := by
    intro u v huv
    simpa only [precedesProbability, map_expect, Ranking.precedes_ofEquiv_iff]
      using hbias u v huv
  have hh := (p.map Ranking.ofEquiv).entropy_of_pairwise_bias_all ε hε hb
  rwa [p.entropy_map_injective Ranking.ofEquiv Ranking.ofEquiv_injective] at hh

end FinDist
end PermEntropy
