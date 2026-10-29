import LeafMode.Semantics

/-! Relabelling invariance of the ordinary domination polynomial. -/
noncomputable section
open scoped BigOperators
open Polynomial

namespace LeafMode

attribute [local instance] Classical.propDecidable

theorem dominates_map_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    {G : SimpleGraph α} {H : SimpleGraph β} (e : G ≃g H) (s : Finset α) :
    Dominates H (s.map e.toEquiv.toEmbedding) ↔ Dominates G s := by
  constructor
  · intro h x
    rcases h (e x) with hx | ⟨y, hy, hxy⟩
    · left
      exact (Finset.mem_map' e.toEquiv.toEmbedding).mp hx
    · obtain ⟨z, rfl⟩ := e.surjective y
      exact Or.inr ⟨z, (Finset.mem_map' e.toEquiv.toEmbedding).mp hy, e.map_adj_iff.mp hxy⟩
  · intro h y
    obtain ⟨x, rfl⟩ := e.surjective y
    rcases h x with hx | ⟨z, hz, hxz⟩
    · left
      exact Finset.mem_map_of_mem e.toEquiv.toEmbedding hx
    · exact Or.inr ⟨e z, Finset.mem_map_of_mem e.toEquiv.toEmbedding hz, e.map_adj_iff.mpr hxz⟩

theorem dominationPolynomial_iso {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {G : SimpleGraph α} {H : SimpleGraph β}
    (e : G ≃g H) : dominationPolynomial G = dominationPolynomial H := by
  classical
  unfold dominationPolynomial
  apply Fintype.sum_equiv e.toEquiv.finsetCongr
  intro s
  simp [Equiv.finsetCongr_apply, dominates_map_iff e]

end LeafMode
