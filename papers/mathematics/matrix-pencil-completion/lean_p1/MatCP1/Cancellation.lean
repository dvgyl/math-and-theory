module

public import MatCP1.Compression
public import MatCP1.GenericRank

@[expose] public section

open Filter

namespace MatCP1

variable {F V A B S : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup A] [Module F A]
  [AddCommGroup B] [Module F B] [AddCommGroup S] [Module F S]

/-- A generic interpolation of the two summand maps preserves both required ranks. -/
theorem eventually_common_kernel_ranks
    [FiniteDimensional F V] [FiniteDimensional F A] [FiniteDimensional F S]
    (r : V →ₗ[F] B) (p : V →ₗ[F] A) (q s : V →ₗ[F] S)
    (hr : Function.Injective (r.prod q))
    (hp : Function.Surjective (p.prod s)) :
    ∀ᶠ z : F in cofinite,
      Function.Injective (r.prod (q + z • (s - q))) ∧
      Function.Surjective (p.prod (q + z • (s - q))) := by
  have hir : Function.Injective
      (r.prod q + (0 : F) • (0 : V →ₗ[F] B).prod (s - q)) := by
    simpa using hr
  have hsp : Function.Surjective
      (p.prod q + (1 : F) • (0 : V →ₗ[F] A).prod (s - q)) := by
    have heq : p.prod q + (1 : F) • (0 : V →ₗ[F] A).prod (s - q) = p.prod s := by
      ext x <;> simp
    rw [heq]
    exact hp
  filter_upwards
    [eventually_injective_affine (r.prod q) ((0 : V →ₗ[F] B).prod (s - q)) 0 hir,
     eventually_surjective_affine (p.prod q) ((0 : V →ₗ[F] A).prod (s - q)) 1 hsp]
    with z hzI hzS
  have hrz : r.prod q + z • (0 : V →ₗ[F] B).prod (s - q) =
      r.prod (q + z • (s - q)) := by
    ext x <;> simp
  have hpz : p.prod q + z • (0 : V →ₗ[F] A).prod (s - q) =
      p.prod (q + z • (s - q)) := by
    ext x <;> simp
  exact ⟨hrz ▸ hzI, hpz ▸ hzS⟩

variable {I VA WA VB WB VT WT XS YS : Type*}
  [AddCommGroup VA] [Module F VA] [AddCommGroup WA] [Module F WA]
  [AddCommGroup VB] [Module F VB] [AddCommGroup WB] [Module F WB]
  [AddCommGroup VT] [Module F VT] [AddCommGroup WT] [Module F WT]
  [AddCommGroup XS] [Module F XS] [AddCommGroup YS] [Module F YS]

/-- Cancel a common summand from any simultaneous subquotient diagram. The family index
may be infinite; only the spaces required for the generic ranks must be finite dimensional. -/
theorem jointCompression_of_common_summand_diagram
    [Infinite F]
    [FiniteDimensional F VT] [FiniteDimensional F WT]
    [FiniteDimensional F VA] [FiniteDimensional F WA]
    [FiniteDimensional F XS] [FiniteDimensional F YS]
    (A : I → VA →ₗ[F] WA) (B : I → VB →ₗ[F] WB)
    (S : I → XS →ₗ[F] YS) (T : I → VT →ₗ[F] WT)
    (rV : VT →ₗ[F] VB) (rW : WT →ₗ[F] WB)
    (pV : VT →ₗ[F] VA) (pW : WT →ₗ[F] WA)
    (qV sV : VT →ₗ[F] XS) (qW sW : WT →ₗ[F] YS)
    (hrV : Function.Injective (rV.prod qV))
    (hrW : Function.Injective (rW.prod qW))
    (hpV : Function.Surjective (pV.prod sV))
    (hpW : Function.Surjective (pW.prod sW))
    (hr : ∀ i, (B i).comp rV = rW.comp (T i))
    (hp : ∀ i, (A i).comp pV = pW.comp (T i))
    (hq : ∀ i, (S i).comp qV = qW.comp (T i))
    (hs : ∀ i, (S i).comp sV = sW.comp (T i)) :
    JointCompression A B := by
  obtain ⟨z, hzV, hzW⟩ :=
    ((eventually_common_kernel_ranks rV pV qV sV hrV hpV).and
      (eventually_common_kernel_ranks rW pW qW sW hrW hpW)).exists
  apply jointCompression_of_common_kernel A B S T rV rW pV pW
    (qV + z • (sV - qV)) (qW + z • (sW - qW))
    hzV.1 hzW.1 hzV.2 hzW.2 hr hp
  intro i
  simp only [LinearMap.comp_add, LinearMap.comp_smul, LinearMap.comp_sub,
    LinearMap.add_comp, LinearMap.smul_comp, LinearMap.sub_comp, hq i, hs i]

/-- Actual common-summand cancellation for a family of rectangular linear maps. The
compression maps are constant across the entire family, without restricting its index type. -/
theorem jointCompression_cancel_common_summand
    [Infinite F]
    [FiniteDimensional F VA] [FiniteDimensional F WA]
    [FiniteDimensional F WB] [FiniteDimensional F XS] [FiniteDimensional F YS]
    (A : I → VA →ₗ[F] WA) (B : I → VB →ₗ[F] WB) (S : I → XS →ₗ[F] YS)
    (h : JointCompression (fun i => (A i).prodMap (S i))
      (fun i => (B i).prodMap (S i))) :
    JointCompression A B := by
  rcases h with ⟨P, Q, hP, hQ, hPQ⟩
  apply jointCompression_of_common_summand_diagram A B S
    (fun i => ((B i).prodMap (S i)).comp Q)
    ((LinearMap.fst F VB XS).comp Q) (LinearMap.fst F WB YS)
    (LinearMap.fst F VA XS) ((LinearMap.fst F WA YS).comp P)
    ((LinearMap.snd F VB XS).comp Q) (LinearMap.snd F VA XS)
    (LinearMap.snd F WB YS) ((LinearMap.snd F WA YS).comp P)
  · simpa only [← LinearMap.prod_comp, LinearMap.pair_fst_snd,
      LinearMap.id_comp] using hQ
  · rw [LinearMap.pair_fst_snd]
    intro x y hxy
    simpa only [LinearMap.id_apply] using hxy
  · rw [LinearMap.pair_fst_snd]
    intro x
    exact ⟨x, LinearMap.id_apply x⟩
  · simpa only [← LinearMap.prod_comp, LinearMap.pair_fst_snd,
      LinearMap.id_comp] using hP
  · intro i
    apply LinearMap.ext
    intro x
    rfl
  · intro i
    apply LinearMap.ext
    intro x
    exact (congrArg Prod.fst (LinearMap.congr_fun (hPQ i) x)).symm
  · intro i
    apply LinearMap.ext
    intro x
    rfl
  · intro i
    apply LinearMap.ext
    intro x
    exact (congrArg Prod.snd (LinearMap.congr_fun (hPQ i) x)).symm

/-- Adding a common summand preserves simultaneous full-row/full-column compression. -/
theorem JointCompression.prodMap
    (A : I → VA →ₗ[F] WA) (B : I → VB →ₗ[F] WB) (S : I → XS →ₗ[F] YS)
    (h : JointCompression A B) :
    JointCompression (fun i => (A i).prodMap (S i))
      (fun i => (B i).prodMap (S i)) := by
  rcases h with ⟨P, Q, hP, hQ, hPQ⟩
  refine ⟨P.prodMap LinearMap.id, Q.prodMap LinearMap.id, ?_, ?_, ?_⟩
  · rintro ⟨a, s⟩
    obtain ⟨b, hb⟩ := hP a
    exact ⟨(b, s), Prod.ext hb rfl⟩
  · intro x y hxy
    apply Prod.ext
    · exact hQ (congrArg Prod.fst hxy)
    · exact congrArg (fun z : VB × XS => z.2) hxy
  · intro i
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact LinearMap.congr_fun (hPQ i) x.1
    · rfl

/-- An arbitrary simultaneous matrix-family compression is cancellative under a common
finite-dimensional summand over every infinite field. -/
theorem jointCompression_common_summand_iff
    [Infinite F]
    [FiniteDimensional F VA] [FiniteDimensional F WA]
    [FiniteDimensional F WB] [FiniteDimensional F XS] [FiniteDimensional F YS]
    (A : I → VA →ₗ[F] WA) (B : I → VB →ₗ[F] WB) (S : I → XS →ₗ[F] YS) :
    JointCompression (fun i => (A i).prodMap (S i))
      (fun i => (B i).prodMap (S i)) ↔ JointCompression A B :=
  ⟨jointCompression_cancel_common_summand A B S, JointCompression.prodMap A B S⟩

end MatCP1
