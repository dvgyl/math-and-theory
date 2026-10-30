module

public import MatCP1Converse.CompletionGraph

@[expose] public section

namespace MatCP1Converse

variable {F U V W : Type*} [Field F]
  [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem completion_finrank_range_equiv [FiniteDimensional F U]
    (A : U →ₗ[F] W) (P : W ≃ₗ[F] W) (Q : U ≃ₗ[F] U) :
    Module.finrank F (LinearMap.range (P.toLinearMap.comp (A.comp Q.toLinearMap))) =
      Module.finrank F (LinearMap.range A) := by
  rw [LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top A Q.range]
  exact P.finrank_map_eq _

theorem completion_finrank_range_prod_zero [FiniteDimensional F U] [FiniteDimensional F V]
    (A : U →ₗ[F] W) :
    Module.finrank F (LinearMap.range (A.prodMap (0 : V →ₗ[F] V))) =
      Module.finrank F (LinearMap.range A) := by
  let B := A.prodMap (0 : V →ₗ[F] V)
  have hf : B = (LinearMap.inl F W V).comp (A.comp (LinearMap.fst F U V)) := by
    ext u <;> simp [B]
  have hb : A = (LinearMap.fst F W V).comp (B.comp (LinearMap.inl F U V)) := by
    ext u
    simp [B]
  change Module.finrank F (LinearMap.range B) = _
  apply le_antisymm
  · rw [hf]
    refine (completion_finrank_range_comp_le _ _).trans_eq ?_
    rw [LinearMap.range_comp_of_range_eq_top A]
    exact LinearMap.range_eq_top.mpr (fun u => ⟨(u, 0), rfl⟩)
  · calc
      Module.finrank F (LinearMap.range A) =
          Module.finrank F (LinearMap.range
            ((LinearMap.fst F W V).comp (B.comp (LinearMap.inl F U V)))) :=
        congrArg (fun M => Module.finrank F (LinearMap.range M)) hb
      _ ≤ Module.finrank F (LinearMap.range (B.comp (LinearMap.inl F U V))) :=
        completion_finrank_range_comp_le _ _
      _ ≤ Module.finrank F (LinearMap.range B) :=
        Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

/-- Every coefficient map is exactly its four coordinate blocks. -/
theorem completion_decompose (M : (U × V) →ₗ[F] (W × V)) :
    M =
      (((LinearMap.fst F W V).comp (M.comp (LinearMap.inl F U V))).coprod
        ((LinearMap.fst F W V).comp (M.comp (LinearMap.inr F U V)))).prod
      (((LinearMap.snd F W V).comp (M.comp (LinearMap.inl F U V))).coprod
        ((LinearMap.snd F W V).comp (M.comp (LinearMap.inr F U V)))) := by
  apply LinearMap.ext
  rintro ⟨u, v⟩
  change M (u, v) = M (u, 0) + M (0, v)
  have hm := M.map_add (u, 0) (0, v)
  simpa using hm

end MatCP1Converse
