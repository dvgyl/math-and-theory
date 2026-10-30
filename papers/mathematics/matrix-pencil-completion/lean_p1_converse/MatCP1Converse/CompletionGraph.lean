module

public import MatCP1Converse.CompletionDerivative
public import MatCP1Converse.BorderGraph

@[expose] public section

namespace MatCP1Converse

section Rank

variable {F V W Z : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup Z] [Module F Z] [FiniteDimensional F V]

theorem completion_finrank_range_comp_le (f : V →ₗ[F] W) (g : W →ₗ[F] Z) :
    Module.finrank F (LinearMap.range (g.comp f)) ≤
      Module.finrank F (LinearMap.range f) := by
  have hker := Submodule.finrank_mono (LinearMap.ker_le_ker_comp f g)
  have hf := f.finrank_range_add_finrank_ker
  have hgf := (g.comp f).finrank_range_add_finrank_ker
  omega

end Rank

section Border

variable {F U V W : Type*} [Field F]
  [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- In normalized border coordinates, the induced derivative has this graph
matrix on `ker A0 × V` and `(W / range A0) × V`. -/
def completionBorderDerivative
    (A0 A1 : U →ₗ[F] W) (X : V →ₗ[F] W) (Y : U →ₗ[F] V) (Z : V →ₗ[F] V) :
    (LinearMap.ker A0 × V) →ₗ[F] ((W ⧸ LinearMap.range A0) × V) :=
  (((LinearMap.range A0).mkQ.comp (A1.comp (LinearMap.ker A0).subtype)).coprod
    ((LinearMap.range A0).mkQ.comp X)).prod
  ((Y.comp (LinearMap.ker A0).subtype).coprod Z)

/-- The true induced derivative factors through the displayed border-coordinate
map. Consequently its rank cannot exceed the rank of that map. -/
theorem completion_derivative_rank_le_border
    [FiniteDimensional F U] [FiniteDimensional F V]
    (A0 A1 : U →ₗ[F] W) (X : V →ₗ[F] W) (Y : U →ₗ[F] V) (Z : V →ₗ[F] V) :
    Module.finrank F (LinearMap.range
      (completionDerivative (A0.prodMap (0 : V →ₗ[F] V))
        ((A1.coprod X).prod (Y.coprod Z)))) ≤
    Module.finrank F (LinearMap.range (completionBorderDerivative A0 A1 X Y Z)) := by
  classical
  let M0 := A0.prodMap (0 : V →ₗ[F] V)
  let M1 := (A1.coprod X).prod (Y.coprod Z)
  let q : (W × V) →ₗ[F] (W × V) ⧸ LinearMap.range M0 := (LinearMap.range M0).mkQ
  have hleft : LinearMap.range A0 ≤ LinearMap.ker (q.comp (LinearMap.inl F W V)) := by
    rintro w ⟨u, rfl⟩
    change q (A0 u, 0) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨(u, 0), by simp [M0]⟩
  let qleft := (LinearMap.range A0).liftQ (q.comp (LinearMap.inl F W V)) hleft
  let qright := q.comp (LinearMap.inr F W V)
  let r := qleft.coprod qright
  let ku : LinearMap.ker M0 →ₗ[F] LinearMap.ker A0 :=
    ((LinearMap.fst F U V).comp (LinearMap.ker M0).subtype).codRestrict
      (LinearMap.ker A0) (fun u => congrArg Prod.fst u.property)
  let kv := (LinearMap.snd F U V).comp (LinearMap.ker M0).subtype
  let k := ku.prod kv
  have hfactor : completionDerivative M0 M1 =
      r.comp ((completionBorderDerivative A0 A1 X Y Z).comp k) := by
    apply LinearMap.ext
    intro u
    change q (A1 u.val.1 + X u.val.2, Y u.val.1 + Z u.val.2) =
      qleft ((LinearMap.range A0).mkQ (A1 u.val.1) +
        (LinearMap.range A0).mkQ (X u.val.2)) +
      qright (Y u.val.1 + Z u.val.2)
    have hql (w : W) : qleft ((LinearMap.range A0).mkQ w) = q (w, 0) := rfl
    have hqr (v : V) : qright v = q (0, v) := rfl
    rw [map_add, hql, hql, hqr, ← map_add, ← map_add]
    exact congrArg q (by ext <;> simp)
  change Module.finrank F (LinearMap.range (completionDerivative M0 M1)) ≤ _
  rw [hfactor]
  exact (completion_finrank_range_comp_le _ _).trans
    (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))

/-- A normalized completion with a genuine scalar-summand strict equivalence
admits kernel/cokernel graph shears making its last derivative block invertible.
Both zero-order preservation constraints are proved in the conclusion. -/
theorem completion_invertible_normalized_border
    [Infinite F] [FiniteDimensional F U] [FiniteDimensional F V]
    (A0 A1 B0 B1 : U →ₗ[F] W)
    (X : V →ₗ[F] W) (Y : U →ₗ[F] V) (Z : V →ₗ[F] V)
    (P : (W × V) ≃ₗ[F] (W × V)) (Q : (U × V) ≃ₗ[F] (U × V))
    (h0 : A0.prodMap (0 : V →ₗ[F] V) =
      P.toLinearMap.comp ((B0.prodMap (0 : V →ₗ[F] V)).comp Q.toLinearMap))
    (h1 : (A1.coprod X).prod (Y.coprod Z) =
      P.toLinearMap.comp ((B1.prodMap (LinearMap.id : V →ₗ[F] V)).comp Q.toLinearMap)) :
    ∃ (S : V →ₗ[F] U) (T : W →ₗ[F] V),
      A0.comp S = 0 ∧ T.comp A0 = 0 ∧
      Function.Bijective ((T.coprod LinearMap.id).comp
        (((A1.coprod X).prod (Y.coprod Z)).comp (S.prod LinearMap.id))) := by
  have hdim := (completion_derivative_rank_ge_scalar_summand B0 B1
    (A0.prodMap (0 : V →ₗ[F] V)) ((A1.coprod X).prod (Y.coprod Z)) P Q h0 h1).trans
    (completion_derivative_rank_le_border A0 A1 X Y Z)
  obtain ⟨s, u, hsu⟩ := exists_invertible_border_graph
    (completionBorderDerivative A0 A1 X Y Z) hdim
  let S := (LinearMap.ker A0).subtype.comp s
  let T := u.comp (LinearMap.range A0).mkQ
  refine ⟨S, T, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro v
    exact (s v).property
  · apply LinearMap.ext
    intro v
    have hz : (LinearMap.range A0).mkQ (A0 v) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self A0 v)
    change u ((LinearMap.range A0).mkQ (A0 v)) = 0
    rw [hz, map_zero]
  · have heq : (T.coprod LinearMap.id).comp
        (((A1.coprod X).prod (Y.coprod Z)).comp (S.prod LinearMap.id)) =
        (u.coprod LinearMap.id).comp
          ((completionBorderDerivative A0 A1 X Y Z).comp (s.prod LinearMap.id)) := by
      apply LinearMap.ext
      intro v
      simp [S, T, completionBorderDerivative]
    rw [heq]
    exact hsu

end Border

end MatCP1Converse
