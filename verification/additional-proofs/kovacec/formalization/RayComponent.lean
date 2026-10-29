import RayExterior

noncomputable section
namespace KovacecComponent
open Set KovacecExterior

/-- A straight ray avoiding a closed set stays in one component of its
frontier complement. -/
lemma ray_mem_component {C : Set ℂ} (hC : IsClosed C) (z d : ℂ)
    (he : ∀ t : ℝ, 0 ≤ t → z + t • d ∉ C)
    (t : ℝ) (ht : 0 ≤ t) :
    z + t • d ∈ connectedComponentIn (frontier C)ᶜ z := by
  have hs : segment ℝ z (z + t • d) ⊆ (frontier C)ᶜ := by
    rintro w ⟨a, b, ha, hb, hab, rfl⟩ hf
    have hh : a • z + b • (z + t • d) = z + (b*t) • d := by
      rw [smul_add, smul_smul, ← add_assoc, ← add_smul, hab, one_smul]
    have hc : a • z + b • (z + t • d) ∈ C := by
      rw [hC.frontier_eq] at hf
      exact hf.1
    rw [hh] at hc
    exact he (b*t) (mul_nonneg hb ht) hc
  exact ((convex_segment z (z+t•d)).isPreconnected.subset_connectedComponentIn
    (left_mem_segment ℝ z (z+t•d)) hs) (right_mem_segment ℝ z (z+t•d))

/-- An escaping unit-speed ray makes the component unbounded. -/
lemma component_unbounded_of_escape {C : Set ℂ} (hC : IsClosed C)
    (z d : ℂ) (hd : ‖d‖ = 1)
    (he : ∀ t : ℝ, 0 ≤ t → z + t • d ∉ C) :
    ¬ Bornology.IsBounded (connectedComponentIn (frontier C)ᶜ z) := by
  intro hb
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hb
  let M := max R 0 + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hz : z ∈ connectedComponentIn (frontier C)ᶜ z := by
    simpa using ray_mem_component hC z d he 0 le_rfl
  have hq := ray_mem_component hC z d he M hM
  have hbnd := hR hz hq
  rw [dist_along_unit z d hd M hM] at hbnd
  have hmax : R ≤ max R 0 := le_max_left _ _
  dsimp [M] at hbnd
  linarith

/-- If every point outside a closed set has a straight escape ray, then the
closure of every bounded component of its frontier complement lies in the set. -/
theorem bounded_component_closure_subset {C : Set ℂ} (hC : IsClosed C)
    (he : ∀ z : ℂ, z ∉ C → ∃ d : ℂ, ‖d‖ = 1 ∧
      ∀ t : ℝ, 0 ≤ t → z + t • d ∉ C)
    (x : ℂ) (hb : Bornology.IsBounded (connectedComponentIn (frontier C)ᶜ x)) :
    closure (connectedComponentIn (frontier C)ᶜ x) ⊆ C := by
  apply closure_minimal _ hC
  intro z hz
  by_contra hzc
  obtain ⟨d, hd, hray⟩ := he z hzc
  have hbz : Bornology.IsBounded (connectedComponentIn (frontier C)ᶜ z) := by
    rwa [← connectedComponentIn_eq hz]
  exact component_unbounded_of_escape hC z d hd hray hbz

/-- A component through an interior point cannot cross the frontier. -/
theorem interior_component_subset {C : Set ℂ} (hC : IsClosed C)
    {z : ℂ} (hz : z ∈ interior C) :
    connectedComponentIn (frontier C)ᶜ z ⊆ interior C := by
  have hzF : z ∈ (frontier C)ᶜ := by
    rw [hC.frontier_eq]
    exact fun h => h.2 hz
  have hzK := mem_connectedComponentIn hzF
  have hcover : connectedComponentIn (frontier C)ᶜ z ⊆ interior C ∪ Cᶜ := by
    intro w hw
    by_cases hwC : w ∈ C
    · left
      by_contra hwI
      have hf : w ∈ frontier C := by
        rw [hC.frontier_eq]
        exact ⟨hwC, hwI⟩
      exact connectedComponentIn_subset _ _ hw hf
    · exact Or.inr hwC
  have hdis : Disjoint (interior C) Cᶜ :=
    Set.disjoint_left.mpr fun w hw hnc => hnc (interior_subset hw)
  rcases IsPreconnected.subset_or_subset isOpen_interior hC.isOpen_compl hdis hcover
      isPreconnected_connectedComponentIn with h | h
  · exact h
  · exact (h hzK (interior_subset hz)).elim

/-- A bounded closed set with nonempty interior has a bounded nonempty
component inside its frontier complement. -/
theorem exists_bounded_component {C : Set ℂ} (hC : IsClosed C)
    (hb : Bornology.IsBounded C) (hi : (interior C).Nonempty) :
    ∃ z : ℂ, z ∈ (frontier C)ᶜ ∧
      (connectedComponentIn (frontier C)ᶜ z).Nonempty ∧
      Bornology.IsBounded (connectedComponentIn (frontier C)ᶜ z) := by
  obtain ⟨z, hz⟩ := hi
  have hzF : z ∈ (frontier C)ᶜ := by
    rw [hC.frontier_eq]
    exact fun h => h.2 hz
  refine ⟨z, hzF, ⟨z, mem_connectedComponentIn hzF⟩, ?_⟩
  exact hb.subset ((interior_component_subset hC hz).trans interior_subset)

#print axioms bounded_component_closure_subset
#print axioms exists_bounded_component
end KovacecComponent
