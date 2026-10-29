import Mathlib.Tactic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Complex.Basic

namespace KovacecExterior
open Set

/-- The straight-segment exterior from Definition 6 of Kovacec (2026). -/
def RayExterior (G : Set ℂ) : Set ℂ := {p | ∀ M : ℝ, 0 < M →
  ∃ q : ℂ, dist p q = M ∧ Disjoint (segment ℝ p q) G}

lemma segment_cannot_avoid_frontier {C : Set ℂ} (hC : IsClosed C)
    {p q : ℂ} (hp : p ∈ C) (hq : q ∉ C)
    (hd : Disjoint (segment ℝ p q) (frontier C)) : False := by
  have hcover : segment ℝ p q ⊆ interior C ∪ Cᶜ := by
    intro z hz
    by_cases hzc : z ∈ C
    · left
      by_contra hzi
      have hzf : z ∈ frontier C := by
        rw [hC.frontier_eq]
        exact ⟨hzc, hzi⟩
      exact Set.disjoint_left.mp hd hz hzf
    · exact Or.inr hzc
  have hdis : Disjoint (interior C) Cᶜ :=
    Set.disjoint_left.mpr fun z hz hzc => hzc (interior_subset hz)
  rcases IsPreconnected.subset_or_subset isOpen_interior hC.isOpen_compl hdis hcover
      (convex_segment p q).isPreconnected with h | h
  · exact hq (interior_subset (h (right_mem_segment ℝ p q)))
  · exact h (left_mem_segment ℝ p q) hp

lemma not_rayExterior_of_mem {C G : Set ℂ} (hC : IsClosed C)
    (hb : Bornology.IsBounded C) (hf : frontier C ⊆ G)
    {p : ℂ} (hp : p ∈ C) : p ∉ RayExterior G := by
  intro he
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hb
  let M := max R 0 + 1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨q, hd, hg⟩ := he M hM
  have hq : q ∉ C := by
    intro hq
    have hbnd := hR hp hq
    rw [hd] at hbnd
    have : R ≤ max R 0 := le_max_left _ _
    dsimp [M] at hbnd
    linarith
  exact segment_cannot_avoid_frontier hC hp hq (hg.mono_right hf)

lemma rayExterior_subset_compl {C G : Set ℂ} (hC : IsClosed C)
    (hb : Bornology.IsBounded C) (hf : frontier C ⊆ G) : RayExterior G ⊆ Cᶜ := by
  intro p hp hc
  exact not_rayExterior_of_mem hC hb hf hc hp

lemma dist_along_unit (z d : ℂ) (hd : ‖d‖ = 1) (M : ℝ) (hM : 0 ≤ M) :
    dist z (z + M • d) = M := by
  rw [dist_eq_norm]
  have hh : z - (z + M • d) = -(M • d) := by abel
  rw [hh, norm_neg, norm_smul, hd, mul_one, Real.norm_eq_abs, abs_of_nonneg hM]

#print axioms rayExterior_subset_compl
end KovacecExterior
