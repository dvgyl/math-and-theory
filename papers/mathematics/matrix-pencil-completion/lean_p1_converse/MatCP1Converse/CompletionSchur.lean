module

public import MatCP1Converse.CompletionGraph

@[expose] public section

namespace MatCP1Converse

variable {F U V W : Type*} [Field F]
  [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- Kernel/cokernel graph shears preserve the zero-order diagonal and the
original upper-left first-order corner, while exposing the graph compression
as the new lower-right coefficient. -/
theorem completion_graph_shear_pair
    (A0 A1 : U →ₗ[F] W) (X : V →ₗ[F] W) (Y : U →ₗ[F] V) (Z : V →ₗ[F] V)
    (S : V →ₗ[F] U) (T : W →ₗ[F] V)
    (hS : A0.comp S = 0) (hT : T.comp A0 = 0) :
    ∃ (L : (W × V) ≃ₗ[F] (W × V)) (R : (U × V) ≃ₗ[F] (U × V)),
      L.toLinearMap.comp ((A0.prodMap (0 : V →ₗ[F] V)).comp R.toLinearMap) =
        A0.prodMap (0 : V →ₗ[F] V) ∧
      L.toLinearMap.comp (((A1.coprod X).prod (Y.coprod Z)).comp R.toLinearMap) =
        (A1.coprod (A1.comp S + X)).prod ((T.comp A1 + Y).coprod
          ((T.coprod LinearMap.id).comp
            (((A1.coprod X).prod (Y.coprod Z)).comp (S.prod LinearMap.id)))) := by
  refine ⟨completionLowerShear (-T), completionUpperShear (-S), ?_, ?_⟩
  · apply LinearMap.ext
    rintro ⟨u, v⟩
    have hs := LinearMap.congr_fun hS v
    have ht := LinearMap.congr_fun hT u
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.zero_apply] at *
    simp [hs, ht]
  · apply LinearMap.ext
    rintro ⟨u, v⟩
    simp only [LinearMap.comp_apply, LinearMap.prod_apply]
    apply Prod.ext <;> simp [map_add] <;> abel

/-- Constant Schur shears split a normalized pencil with an invertible last
coefficient block. The residual perturbation has rank at most the border size. -/
theorem completion_schur_split
    [FiniteDimensional F U] [FiniteDimensional F V]
    (A0 A1 : U →ₗ[F] W) (X : V →ₗ[F] W) (Y : U →ₗ[F] V) (Z : V →ₗ[F] V)
    (hZ : Function.Bijective Z) :
    ∃ (E : U →ₗ[F] W) (L : (W × V) ≃ₗ[F] (W × V))
      (R : (U × V) ≃ₗ[F] (U × V)),
      Module.finrank F (LinearMap.range E) ≤ Module.finrank F V ∧
      L.toLinearMap.comp ((A0.prodMap (0 : V →ₗ[F] V)).comp R.toLinearMap) =
        A0.prodMap (0 : V →ₗ[F] V) ∧
      L.toLinearMap.comp (((A1.coprod X).prod (Y.coprod Z)).comp R.toLinearMap) =
        (A1 - E).prodMap (LinearMap.id : V →ₗ[F] V) := by
  classical
  let eZ := LinearEquiv.ofBijective Z hZ
  let E := X.comp (eZ.symm.toLinearMap.comp Y)
  let L := (completionUpperShear (X.comp eZ.symm.toLinearMap)).trans
    ((LinearEquiv.refl F W).prodCongr eZ.symm)
  let R := completionLowerShear (eZ.symm.toLinearMap.comp Y)
  have hZi (v : V) : eZ.symm (Z v) = v := eZ.symm_apply_apply v
  have hiZ (v : V) : Z (eZ.symm v) = v := eZ.apply_symm_apply v
  refine ⟨E, L, R, ?_, ?_, ?_⟩
  · exact (completion_finrank_range_comp_le _ _).trans
      ((completion_finrank_range_comp_le _ _).trans (LinearMap.range Y).finrank_le)
  · apply LinearMap.ext
    rintro ⟨u, v⟩
    simp [L, R]
  · apply LinearMap.ext
    rintro ⟨u, v⟩
    simp only [L, R, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, completionUpperShear_apply, completionLowerShear_apply,
      LinearMap.prod_apply, LinearMap.prodMap_apply,
      LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, map_sub,
      LinearMap.sub_apply, LinearMap.id_apply]
    apply Prod.ext
    · simp [E, hZi]
      abel
    · simp [hZi]

end MatCP1Converse
