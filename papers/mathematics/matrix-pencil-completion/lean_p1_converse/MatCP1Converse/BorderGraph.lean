module

public import MatCP1Converse.CommonChart
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

namespace MatCP1Converse

variable {F V W Z : Type*} [Field F] [Infinite F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup Z] [Module F Z]
  [FiniteDimensional F V] [FiniteDimensional F W] [FiniteDimensional F Z]

omit [FiniteDimensional F Z] in
/-- A map of rank at least the border dimension admits an invertible graph
compression whose source and target border-coordinate blocks are identities.
This proves the graph selection from its actual rank hypothesis. -/
theorem exists_invertible_border_graph
    (H : (W × V) →ₗ[F] (Z × V))
    (hRank : Module.finrank F V ≤ Module.finrank F (LinearMap.range H)) :
    ∃ (s : V →ₗ[F] W) (u : Z →ₗ[F] V),
      Function.Bijective
        ((u.coprod LinearMap.id).comp (H.comp (s.prod LinearMap.id))) := by
  classical
  obtain ⟨q0, hq0⟩ := finrank_le_iff_exists_linearMap.mp hRank
  let g : V →ₗ[F] (Z × V) := (LinearMap.range H).subtype.comp q0
  obtain ⟨q, hq⟩ := exists_lift_of_range_mem H g (fun x => (q0 x).property)
  have hHq : Function.Injective (H.comp q) := by
    rw [hq]
    exact Subtype.val_injective.comp hq0
  let e : V →ₗ[F] (W × V) := LinearMap.inr F W V
  let b : (W × V) →ₗ[F] V := LinearMap.snd F W V
  have h0 : Function.Bijective (b.comp e + (0 : F) • b.comp (q - e)) := by
    simpa [e, b] using (Function.bijective_id : Function.Bijective (id : V → V))
  have h1 : Function.Injective (H.comp e + (1 : F) • H.comp (q - e)) := by
    have heq : H.comp e + (1 : F) • H.comp (q - e) = H.comp q := by
      simp only [one_smul, LinearMap.comp_sub]
      abel
    rw [heq]
    exact hHq
  obtain ⟨z, hzB, hzH⟩ :=
    ((MatCP1.eventually_bijective_affine (b.comp e) (b.comp (q - e)) 0 h0).and
      (MatCP1.eventually_injective_affine (H.comp e) (H.comp (q - e)) 1 h1)).exists
  let qz : V →ₗ[F] (W × V) := e + z • (q - e)
  have hB : Function.Bijective (b.comp qz) := by
    simpa only [qz, LinearMap.comp_add, LinearMap.comp_smul] using hzB
  have hHQ : Function.Injective (H.comp qz) := by
    simpa only [qz, LinearMap.comp_add, LinearMap.comp_smul] using hzH
  let B : V ≃ₗ[F] V := LinearEquiv.ofBijective (b.comp qz) hB
  let s : V →ₗ[F] W := (LinearMap.fst F W V).comp (qz.comp B.symm.toLinearMap)
  have hgraph : qz.comp B.symm.toLinearMap = s.prod LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · change b (qz (B.symm x)) = x
      exact B.apply_symm_apply x
  have hinj : Function.Injective (H.comp (s.prod LinearMap.id)) := by
    rw [← hgraph, ← LinearMap.comp_assoc]
    exact hHQ.comp B.symm.injective
  let h := H.comp (s.prod LinearMap.id)
  let a : V →ₗ[F] V := (LinearMap.snd F Z V).comp h
  let c : V →ₗ[F] Z := (LinearMap.fst F Z V).comp h
  have hac : Function.Injective (a.prod c) := by
    intro x y hxy
    apply hinj
    apply Prod.ext
    · exact congrArg Prod.snd hxy
    · exact congrArg Prod.fst hxy
  obtain ⟨u, hu⟩ := exists_invertible_graph a c hac
  refine ⟨s, u, ?_⟩
  have heq : (u.coprod LinearMap.id).comp (H.comp (s.prod LinearMap.id)) =
      a + u.comp c := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.id_apply,
      LinearMap.add_apply, a, c, h, LinearMap.snd_apply, LinearMap.fst_apply]
    exact add_comm _ _
  rw [heq]
  exact hu

end MatCP1Converse
