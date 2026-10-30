module

public import MatCP1Converse.MatrixExtension

@[expose] public section

namespace MatCP1Converse

section Linear

variable {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Surjections with the same kernel differ by a target automorphism. -/
theorem exists_equiv_same_kernel (Q0 Q1 : V →ₗ[F] W)
    (h0 : Function.Surjective Q0) (h1 : Function.Surjective Q1)
    (hk : LinearMap.ker Q0 = LinearMap.ker Q1) :
    ∃ e : W ≃ₗ[F] W, e.toLinearMap.comp Q0 = Q1 := by
  obtain ⟨L, hL⟩ := exists_factor_of_ker_le Q0 Q1 hk.le
  have hL' (v : V) : L (Q0 v) = Q1 v := LinearMap.congr_fun hL v
  have hLs : Function.Surjective L := by
    intro w
    obtain ⟨v, hv⟩ := h1 w
    exact ⟨Q0 v, (hL' v).trans hv⟩
  have hLi : Function.Injective L := by
    intro a b hab
    obtain ⟨v, hv⟩ := h0 a
    obtain ⟨w, hw⟩ := h0 b
    have heq : Q1 v = Q1 w := by rw [← hL', ← hL', hv, hw]; exact hab
    have hh : v - w ∈ LinearMap.ker Q1 := by
      change Q1 (v - w) = 0
      rw [map_sub, heq, sub_self]
    rw [← hk] at hh
    have heq0 : Q0 v = Q0 w := sub_eq_zero.mp
      (by simpa only [map_sub] using (show Q0 (v - w) = 0 from hh))
    exact hv.symm.trans (heq0.trans hw)
  exact ⟨LinearEquiv.ofBijective L ⟨hLi, hLs⟩, hL⟩

/-- Embeddings with the same range differ by a source automorphism. -/
theorem exists_equiv_same_range (K0 K1 : W →ₗ[F] V)
    (h0 : Function.Injective K0) (h1 : Function.Injective K1)
    (hr : LinearMap.range K0 = LinearMap.range K1) :
    ∃ e : W ≃ₗ[F] W, K0.comp e.toLinearMap = K1 := by
  obtain ⟨R, hR⟩ := exists_lift_of_range_mem K0 K1 (fun w => by
    rw [hr]
    exact LinearMap.mem_range_self K1 w)
  have hR' (w : W) : K0 (R w) = K1 w := LinearMap.congr_fun hR w
  have hRi : Function.Injective R := by
    intro a b hab
    apply h1
    rw [← hR', ← hR', hab]
  have hRs : Function.Surjective R := by
    intro w
    have hm := LinearMap.mem_range_self K0 w
    rw [hr] at hm
    obtain ⟨v, hv⟩ := hm
    exact ⟨v, h0 ((hR' v).trans hv)⟩
  exact ⟨LinearEquiv.ofBijective R ⟨hRi, hRs⟩, hR⟩

end Linear

section Matrix

variable {F n a b : Type*} [Field F]
  [Fintype n] [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- Any two full-row quotient matrices with the same kernel differ by an explicitly
invertible constant left multiplier. -/
theorem exists_quotient_matrix_equivalence (Q0 Q1 : Matrix a n F)
    (h0 : Function.Surjective Q0.mulVec) (h1 : Function.Surjective Q1.mulVec)
    (hk : LinearMap.ker Q0.mulVecLin = LinearMap.ker Q1.mulVecLin) :
    ∃ L Linv : Matrix a a F, L * Linv = 1 ∧ Linv * L = 1 ∧ L * Q0 = Q1 := by
  classical
  have h0' : Function.Surjective (Matrix.toLin' Q0) := by rw [Matrix.toLin'_apply']; exact h0
  have h1' : Function.Surjective (Matrix.toLin' Q1) := by rw [Matrix.toLin'_apply']; exact h1
  have hk' : LinearMap.ker (Matrix.toLin' Q0) = LinearMap.ker (Matrix.toLin' Q1) := by
    simpa only [Matrix.toLin'_apply'] using hk
  obtain ⟨e, he⟩ := exists_equiv_same_kernel (Matrix.toLin' Q0) (Matrix.toLin' Q1) h0' h1' hk'
  refine ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    toMatrix_equiv_mul_symm e, toMatrix_equiv_mul_symm e.symm, ?_⟩
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using
    congrArg LinearMap.toMatrix' he

omit [Fintype n] in
/-- Any two full-column kernel matrices with the same image differ by an explicitly
invertible constant right multiplier. -/
theorem exists_kernel_matrix_equivalence (K0 K1 : Matrix n b F)
    (h0 : Function.Injective K0.mulVec) (h1 : Function.Injective K1.mulVec)
    (hr : LinearMap.range K0.mulVecLin = LinearMap.range K1.mulVecLin) :
    ∃ R Rinv : Matrix b b F, R * Rinv = 1 ∧ Rinv * R = 1 ∧ K0 * R = K1 := by
  classical
  have h0' : Function.Injective (Matrix.toLin' K0) := by rw [Matrix.toLin'_apply']; exact h0
  have h1' : Function.Injective (Matrix.toLin' K1) := by rw [Matrix.toLin'_apply']; exact h1
  have hr' : LinearMap.range (Matrix.toLin' K0) = LinearMap.range (Matrix.toLin' K1) := by
    simpa only [Matrix.toLin'_apply'] using hr
  obtain ⟨e, he⟩ := exists_equiv_same_range (Matrix.toLin' K0) (Matrix.toLin' K1) h0' h1' hr'
  refine ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    toMatrix_equiv_mul_symm e, toMatrix_equiv_mul_symm e.symm, ?_⟩
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using
    congrArg LinearMap.toMatrix' he

end Matrix

end MatCP1Converse
