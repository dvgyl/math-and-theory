module

public import MatCP1Converse.NearbyEmbedding
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

namespace MatCP1Converse

section Shears

variable {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- The constant lower block shear `(v,w) ↦ (v,w - T v)`. -/
def completionLowerShear (T : V →ₗ[F] W) : (V × W) ≃ₗ[F] (V × W) :=
  LinearEquiv.ofLinearMap
    ((LinearMap.fst F V W).prod
      ((LinearMap.snd F V W) - T.comp (LinearMap.fst F V W)))
    ((LinearMap.fst F V W).prod
      ((LinearMap.snd F V W) + T.comp (LinearMap.fst F V W)))
    (by ext x <;> simp)
    (by ext x <;> simp)

/-- The constant upper block shear `(v,w) ↦ (v - U w,w)`. -/
def completionUpperShear (U : W →ₗ[F] V) : (V × W) ≃ₗ[F] (V × W) :=
  LinearEquiv.ofLinearMap
    (((LinearMap.fst F V W) - U.comp (LinearMap.snd F V W)).prod
      (LinearMap.snd F V W))
    (((LinearMap.fst F V W) + U.comp (LinearMap.snd F V W)).prod
      (LinearMap.snd F V W))
    (by ext x <;> simp)
    (by ext x <;> simp)

@[simp] theorem completionLowerShear_apply (T : V →ₗ[F] W) (x : V × W) :
    completionLowerShear T x = (x.1, x.2 - T x.1) := rfl

@[simp] theorem completionUpperShear_apply (U : W →ₗ[F] V) (x : V × W) :
    completionUpperShear U x = (x.1 - U x.2, x.2) := rfl

end Shears

variable {F V W X Y : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
  [FiniteDimensional F V] [FiniteDimensional F W]
  [FiniteDimensional F X] [FiniteDimensional F Y]

omit [FiniteDimensional F W] [FiniteDimensional F Y] in
/-- Equality of the full block rank and its corner rank forces both border
factorizations and the matching lower-right product. No nonsingular corner is assumed. -/
theorem completion_border_factorization
    (A : V →ₗ[F] W) (B : X →ₗ[F] W) (C : V →ₗ[F] Y) (D : X →ₗ[F] Y)
    (hRank : Module.finrank F (LinearMap.range ((A.coprod B).prod (C.coprod D))) =
      Module.finrank F (LinearMap.range A)) :
    ∃ (U : X →ₗ[F] V) (T : W →ₗ[F] Y),
      B = A.comp U ∧ C = T.comp A ∧ D = T.comp (A.comp U) := by
  classical
  let J := A.prod C
  let M := (A.coprod B).prod (C.coprod D)
  have hJM : LinearMap.range J ≤ LinearMap.range M := by
    rintro w ⟨v, rfl⟩
    exact ⟨(v, 0), by simp [M, J]⟩
  have hJA : LinearMap.ker J ≤ LinearMap.ker A := by
    intro v hv
    exact congrArg Prod.fst hv
  have hAJrank : Module.finrank F (LinearMap.range A) ≤
      Module.finrank F (LinearMap.range J) := by
    have hk := Submodule.finrank_mono hJA
    have hj := J.finrank_range_add_finrank_ker
    have ha := A.finrank_range_add_finrank_ker
    omega
  have hJrank : Module.finrank F (LinearMap.range J) =
      Module.finrank F (LinearMap.range A) := by
    apply le_antisymm
    · exact (Submodule.finrank_mono hJM).trans_eq hRank
    · exact hAJrank
  have hJMrange : LinearMap.range J = LinearMap.range M :=
    Submodule.eq_of_le_of_finrank_eq hJM (hJrank.trans hRank.symm)
  have hJAker : LinearMap.ker J = LinearMap.ker A := by
    apply Submodule.eq_of_le_of_finrank_eq hJA
    have hj := J.finrank_range_add_finrank_ker
    have ha := A.finrank_range_add_finrank_ker
    omega
  have hAC : LinearMap.ker A ≤ LinearMap.ker C := by
    intro v hv
    rw [← hJAker] at hv
    exact congrArg Prod.snd hv
  obtain ⟨T, hT⟩ := exists_factor_of_ker_le A C hAC
  have hBD (x : X) : (B.prod D) x ∈ LinearMap.range J := by
    rw [hJMrange]
    exact ⟨(0, x), by simp [M]⟩
  obtain ⟨U, hU⟩ := exists_lift_of_range_mem J (B.prod D) hBD
  have hB : B = A.comp U := by
    apply LinearMap.ext
    intro x
    exact (congrArg Prod.fst (LinearMap.congr_fun hU x)).symm
  have hD : D = C.comp U := by
    apply LinearMap.ext
    intro x
    exact (congrArg Prod.snd (LinearMap.congr_fun hU x)).symm
  refine ⟨U, T, hB, hT.symm, ?_⟩
  rw [hD, ← hT, LinearMap.comp_assoc]

omit [FiniteDimensional F W] [FiniteDimensional F Y] in
/-- Rank-equal border normalization is achieved by actual constant automorphisms.
The same shears preserve the original corner of every other coefficient map. -/
theorem completion_normalize_pair
    (A : V →ₗ[F] W) (B : X →ₗ[F] W) (C : V →ₗ[F] Y) (D : X →ₗ[F] Y)
    (N : (V × X) →ₗ[F] (W × Y))
    (hRank : Module.finrank F (LinearMap.range ((A.coprod B).prod (C.coprod D))) =
      Module.finrank F (LinearMap.range A)) :
    ∃ (L : (W × Y) ≃ₗ[F] (W × Y)) (R : (V × X) ≃ₗ[F] (V × X)),
      L.toLinearMap.comp (((A.coprod B).prod (C.coprod D)).comp R.toLinearMap) =
        A.prodMap (0 : X →ₗ[F] Y) ∧
      (LinearMap.fst F W Y).comp (L.toLinearMap.comp
        (N.comp (R.toLinearMap.comp (LinearMap.inl F V X)))) =
      (LinearMap.fst F W Y).comp (N.comp (LinearMap.inl F V X)) := by
  obtain ⟨U, T, hB, hC, hD⟩ := completion_border_factorization A B C D hRank
  refine ⟨completionLowerShear T, completionUpperShear U, ?_, ?_⟩
  · apply LinearMap.ext
    rintro ⟨v, x⟩
    simp [hB, hC, hD]
  · apply LinearMap.ext
    intro v
    simp

end MatCP1Converse
