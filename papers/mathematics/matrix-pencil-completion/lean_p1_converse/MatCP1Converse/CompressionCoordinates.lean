module

public import MatCP1Converse.MatrixExtension

@[expose] public section

namespace MatCP1Converse

section Linear

variable {F V W Z A B : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup Z] [Module F Z] [AddCommGroup A] [Module F A]
  [AddCommGroup B] [Module F B]

/-- Transport quotient and kernel coordinates along the actual ambient automorphisms. -/
theorem transport_quotient_kernel
    (X0 X1 : W →ₗ[F] V) (Y0 Y1 : V →ₗ[F] Z)
    (Q : V →ₗ[F] A) (K : B →ₗ[F] V) (S Si T Ti : V →ₗ[F] V)
    (hSiS : Si.comp S = LinearMap.id) (hSSi : S.comp Si = LinearMap.id)
    (hTiT : Ti.comp T = LinearMap.id) (hTTi : T.comp Ti = LinearMap.id)
    (hSX : S.comp X0 = X1) (hYT : Y1.comp T = Y0)
    (hQ : Function.Surjective Q) (hK : Function.Injective K)
    (hker : LinearMap.ker Q = LinearMap.range X0)
    (hrange : LinearMap.range K = LinearMap.ker Y0) :
    Function.Surjective (Q.comp Si) ∧ Function.Injective (T.comp K) ∧
      LinearMap.ker (Q.comp Si) = LinearMap.range X1 ∧
      LinearMap.range (T.comp K) = LinearMap.ker Y1 := by
  have hSiS' (v : V) : Si (S v) = v := LinearMap.congr_fun hSiS v
  have hSSi' (v : V) : S (Si v) = v := LinearMap.congr_fun hSSi v
  have hTiT' (v : V) : Ti (T v) = v := LinearMap.congr_fun hTiT v
  have hTTi' (v : V) : T (Ti v) = v := LinearMap.congr_fun hTTi v
  have hSX' (w : W) : S (X0 w) = X1 w := LinearMap.congr_fun hSX w
  have hYT' (v : V) : Y1 (T v) = Y0 v := LinearMap.congr_fun hYT v
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hQ.comp (fun v => ⟨S v, hSiS' v⟩)
  · intro x y hxy
    apply hK
    have hh := congrArg Ti hxy
    simpa only [LinearMap.comp_apply, hTiT'] using hh
  · apply le_antisymm
    · intro v hv
      have hm : Si v ∈ LinearMap.range X0 := by
        rw [← hker]
        exact hv
      obtain ⟨w, hw⟩ := hm
      refine ⟨w, ?_⟩
      rw [← hSX', hw, hSSi']
    · rintro v ⟨w, rfl⟩
      change Q (Si (X1 w)) = 0
      rw [← hSX', hSiS']
      have hm := LinearMap.mem_range_self X0 w
      rw [← hker] at hm
      exact hm
  · apply le_antisymm
    · rintro v ⟨w, rfl⟩
      change Y1 (T (K w)) = 0
      rw [hYT']
      have hm := LinearMap.mem_range_self K w
      rw [hrange] at hm
      exact hm
    · intro v hv
      have hm : Ti v ∈ LinearMap.range K := by
        rw [hrange]
        change Y0 (Ti v) = 0
        rw [← hYT', hTTi']
        exact hv
      obtain ⟨w, hw⟩ := hm
      refine ⟨w, ?_⟩
      change T (K w) = v
      rw [hw, hTTi']

end Linear

section Matrix

variable {F n m p a b : Type*} [Field F]
  [Fintype n] [Fintype m] [Fintype p] [Fintype a] [Fintype b]
  [DecidableEq n]

omit [Fintype p] [Fintype a] in
/-- The transported matrices have the exact full ranks, kernel, and image required
to represent the new static compression. -/
theorem matrix_transport_quotient_kernel
    (X0 X1 : Matrix n m F) (Y0 Y1 : Matrix p n F)
    (Q : Matrix a n F) (K : Matrix n b F) (S Si T Ti : Matrix n n F)
    (hSiS : Si * S = 1) (hSSi : S * Si = 1)
    (hTiT : Ti * T = 1) (hTTi : T * Ti = 1)
    (hSX : S * X0 = X1) (hYT : Y1 * T = Y0)
    (hQ : Function.Surjective Q.mulVec) (hK : Function.Injective K.mulVec)
    (hker : LinearMap.ker Q.mulVecLin = LinearMap.range X0.mulVecLin)
    (hrange : LinearMap.range K.mulVecLin = LinearMap.ker Y0.mulVecLin) :
    Function.Surjective (Q * Si).mulVec ∧ Function.Injective (T * K).mulVec ∧
      LinearMap.ker (Q * Si).mulVecLin = LinearMap.range X1.mulVecLin ∧
      LinearMap.range (T * K).mulVecLin = LinearMap.ker Y1.mulVecLin := by
  have hSiSl : Si.mulVecLin.comp S.mulVecLin = LinearMap.id := by
    simpa only [Matrix.mulVecLin_mul, Matrix.mulVecLin_one] using congrArg Matrix.mulVecLin hSiS
  have hSSil : S.mulVecLin.comp Si.mulVecLin = LinearMap.id := by
    simpa only [Matrix.mulVecLin_mul, Matrix.mulVecLin_one] using congrArg Matrix.mulVecLin hSSi
  have hTiTl : Ti.mulVecLin.comp T.mulVecLin = LinearMap.id := by
    simpa only [Matrix.mulVecLin_mul, Matrix.mulVecLin_one] using congrArg Matrix.mulVecLin hTiT
  have hTTil : T.mulVecLin.comp Ti.mulVecLin = LinearMap.id := by
    simpa only [Matrix.mulVecLin_mul, Matrix.mulVecLin_one] using congrArg Matrix.mulVecLin hTTi
  have hSXl : S.mulVecLin.comp X0.mulVecLin = X1.mulVecLin := by
    simpa only [Matrix.mulVecLin_mul] using congrArg Matrix.mulVecLin hSX
  have hYTl : Y1.mulVecLin.comp T.mulVecLin = Y0.mulVecLin := by
    simpa only [Matrix.mulVecLin_mul] using congrArg Matrix.mulVecLin hYT
  change Function.Surjective (Q * Si).mulVecLin ∧ Function.Injective (T * K).mulVecLin ∧ _
  simpa only [Matrix.mulVecLin_mul] using transport_quotient_kernel
    X0.mulVecLin X1.mulVecLin Y0.mulVecLin Y1.mulVecLin Q.mulVecLin K.mulVecLin
    S.mulVecLin Si.mulVecLin T.mulVecLin Ti.mulVecLin
    hSiSl hSSil hTiTl hTTil hSXl hYTl hQ hK hker hrange

end Matrix

end MatCP1Converse
