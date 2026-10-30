module

public import MatCP1Converse.CompletionExtraction

@[expose] public section

namespace MatCP1Converse

variable {F U V W : Type*} [Field F] [Infinite F]
  [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
  [FiniteDimensional F U] [FiniteDimensional F V] [FiniteDimensional F W]

/-- The actual fixed-factor completion lemma at any prescribed scalar `d`.
It supplies constant equivalences and a constant rank-bounded perturbation for
the complete affine pencil identity, including the factor `(t-d)`. -/
theorem completion_extract_fixed_factor
    (d : F) (A0 A1 B0 B1 : U →ₗ[F] W)
    (M0 M1 : (U × V) →ₗ[F] (W × V))
    (P : (W × V) ≃ₗ[F] (W × V)) (Q : (U × V) ≃ₗ[F] (U × V))
    (hcorner0 : (LinearMap.fst F W V).comp (M0.comp (LinearMap.inl F U V)) = A0)
    (hcorner1 : (LinearMap.fst F W V).comp (M1.comp (LinearMap.inl F U V)) = A1)
    (hM0 : M0 = P.toLinearMap.comp
      ((B0.prodMap (-d • (LinearMap.id : V →ₗ[F] V))).comp Q.toLinearMap))
    (hM1 : M1 = P.toLinearMap.comp
      ((B1.prodMap (LinearMap.id : V →ₗ[F] V)).comp Q.toLinearMap))
    (hRank : Module.finrank F (LinearMap.range (A0 + d • A1)) =
      Module.finrank F (LinearMap.range (B0 + d • B1))) :
    ∃ (E : U →ₗ[F] W) (p : W ≃ₗ[F] W) (q : U ≃ₗ[F] U),
      Module.finrank F (LinearMap.range E) ≤ Module.finrank F V ∧
      A0 + d • E = p.toLinearMap.comp (B0.comp q.toLinearMap) ∧
      A1 - E = p.toLinearMap.comp (B1.comp q.toLinearMap) ∧
      ∀ t : F, A0 + t • A1 - (t - d) • E =
        p.toLinearMap.comp ((B0 + t • B1).comp q.toLinearMap) := by
  have hcornerd : (LinearMap.fst F W V).comp
      ((M0 + d • M1).comp (LinearMap.inl F U V)) = A0 + d • A1 := by
    simp only [LinearMap.add_comp, LinearMap.smul_comp, LinearMap.comp_add,
      LinearMap.comp_smul, hcorner0, hcorner1]
  have hMd : M0 + d • M1 = P.toLinearMap.comp
      (((B0 + d • B1).prodMap (0 : V →ₗ[F] V)).comp Q.toLinearMap) := by
    rw [hM0, hM1]
    apply LinearMap.ext
    intro x
    simp
    rw [← map_smul, ← map_add]
    congr 1
    ext <;> simp
  obtain ⟨E, p, q, hE, hc, hl⟩ := completion_extract_centered
    (A0 + d • A1) A1 (B0 + d • B1) B1 (M0 + d • M1) M1 P Q
    hcornerd hcorner1 hMd hM1 hRank
  have hc' : A0 + d • A1 = p.toLinearMap.comp (B0.comp q.toLinearMap) +
      d • p.toLinearMap.comp (B1.comp q.toLinearMap) := by
    simpa only [LinearMap.add_comp, LinearMap.smul_comp, LinearMap.comp_add,
      LinearMap.comp_smul] using hc
  have hconst : A0 + d • E = p.toLinearMap.comp (B0.comp q.toLinearMap) := by
    calc
      A0 + d • E = (A0 + d • A1) - d • (A1 - E) := by rw [smul_sub]; abel
      _ = (p.toLinearMap.comp (B0.comp q.toLinearMap) +
          d • p.toLinearMap.comp (B1.comp q.toLinearMap)) -
          d • p.toLinearMap.comp (B1.comp q.toLinearMap) := by rw [hc', hl]
      _ = p.toLinearMap.comp (B0.comp q.toLinearMap) := by abel
  refine ⟨E, p, q, hE, hconst, hl, ?_⟩
  intro t
  calc
    A0 + t • A1 - (t - d) • E = (A0 + d • E) + t • (A1 - E) := by
      rw [sub_smul, smul_sub]
      abel
    _ = p.toLinearMap.comp (B0.comp q.toLinearMap) +
        t • p.toLinearMap.comp (B1.comp q.toLinearMap) := by rw [hconst, hl]
    _ = p.toLinearMap.comp ((B0 + t • B1).comp q.toLinearMap) := by
      simp only [LinearMap.add_comp, LinearMap.smul_comp, LinearMap.comp_add,
        LinearMap.comp_smul]

end MatCP1Converse
