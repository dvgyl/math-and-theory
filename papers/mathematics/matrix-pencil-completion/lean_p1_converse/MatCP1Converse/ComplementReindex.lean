module

public import MatCP1Converse.ComplementContraction
public import MatCP1Converse.OrbitDistance

@[expose] public section

namespace MatCP1Converse

open Matrix

section Coordinates

variable {F o i o' i' : Type*} [Field F]
  [Fintype o] [Fintype i] [Fintype o'] [Fintype i']

theorem complement_submatrix_injective
    (M : Matrix o i F) (eo : o' ≃ o) (ei : i' ≃ i)
    (hM : Function.Injective M.mulVec) :
    Function.Injective (M.submatrix eo ei).mulVec := by
  intro v w h
  have hh : M *ᵥ (v ∘ ei.symm) = M *ᵥ (w ∘ ei.symm) := by
    funext j
    have hz := congrFun h (eo.symm j)
    simpa only [Matrix.submatrix_mulVec_equiv, Function.comp_apply, eo.apply_symm_apply] using hz
  have hvw := hM hh
  funext j
  have hz := congrFun hvw (ei j)
  simpa only [Function.comp_apply, ei.symm_apply_apply] using hz

theorem complement_submatrix_surjective
    (M : Matrix o i F) (eo : o' ≃ o) (ei : i' ≃ i)
    (hM : Function.Surjective M.mulVec) :
    Function.Surjective (M.submatrix eo ei).mulVec := by
  intro v
  obtain ⟨w, hw⟩ := hM (v ∘ eo.symm)
  refine ⟨w ∘ ei, ?_⟩
  rw [Matrix.submatrix_mulVec_equiv]
  have heq : (w ∘ ei) ∘ ei.symm = w := by funext j; simp
  rw [heq, hw]
  funext j
  simp

theorem complement_submatrix_range
    (M : Matrix o i F) (ei : i' ≃ i) :
    LinearMap.range (M.submatrix (Equiv.refl o) ei).mulVecLin =
      LinearMap.range M.mulVecLin := by
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    exact ⟨w ∘ ei.symm, by simp only [Matrix.mulVecLin_apply,
      Matrix.submatrix_mulVec_equiv, Equiv.coe_refl, Function.comp_id]⟩
  · rintro v ⟨w, rfl⟩
    refine ⟨w ∘ ei, ?_⟩
    change M.submatrix (Equiv.refl o) ei *ᵥ (w ∘ ei) = M *ᵥ w
    rw [Matrix.submatrix_mulVec_equiv]
    have heq : (w ∘ ei) ∘ ei.symm = w := by funext j; simp
    simp only [heq, Equiv.coe_refl, Function.comp_id]

theorem complement_submatrix_kernel
    (M : Matrix o i F) (eo : o' ≃ o) :
    LinearMap.ker (M.submatrix eo (Equiv.refl i)).mulVecLin =
      LinearMap.ker M.mulVecLin := by
  apply le_antisymm
  · intro v hv
    change M *ᵥ v = 0
    funext j
    have hh := congrFun (show M.submatrix eo (Equiv.refl i) *ᵥ v = 0 from hv) (eo.symm j)
    rw [Matrix.submatrix_mulVec_equiv] at hh
    simpa using hh
  · intro v hv
    change M.submatrix eo (Equiv.refl i) *ᵥ v = 0
    have hz : M *ᵥ v = 0 := hv
    rw [Matrix.submatrix_mulVec_equiv]
    simp [hz]

end Coordinates

namespace ComplementPresentation

variable {F o i o' i' a b r s : Type*} [Field F]
  [Fintype o] [Fintype i] [Fintype o'] [Fintype i']
  [Fintype a] [Fintype b] [Fintype r] [Fintype s]
  [DecidableEq r] [DecidableEq s]

/-- Reindexing only the ambient row and column coordinates leaves the
intrinsic output pencil unchanged, with every presentation condition proved. -/
def reindex {E H : Matrix o i F} {A : Pencil F a b}
    (w : ComplementPresentation r s E H A) (eo : o' ≃ o) (ei : i' ≃ i) :
    ComplementPresentation r s (E.submatrix eo ei) (H.submatrix eo ei) A := by
  have ht : fromRows (w.rightE.submatrix (Equiv.refl r) ei)
      (w.rightH.submatrix (Equiv.refl s) ei) =
        (fromRows w.rightE w.rightH).submatrix (Equiv.refl (r ⊕ s)) ei := by
    ext j k
    cases j <;> rfl
  have hs : fromCols (w.leftE.submatrix eo (Equiv.refl r))
      (w.leftH.submatrix eo (Equiv.refl s)) =
        (fromCols w.leftE w.leftH).submatrix eo (Equiv.refl (r ⊕ s)) := by
    ext j k
    cases k <;> rfl
  exact {
    leftE := w.leftE.submatrix eo (Equiv.refl r)
    rightE := w.rightE.submatrix (Equiv.refl r) ei
    leftH := w.leftH.submatrix eo (Equiv.refl s)
    rightH := w.rightH.submatrix (Equiv.refl s) ei
    leftE_injective := complement_submatrix_injective _ eo _ w.leftE_injective
    rightE_surjective := complement_submatrix_surjective _ _ ei w.rightE_surjective
    leftH_injective := complement_submatrix_injective _ eo _ w.leftH_injective
    rightH_surjective := complement_submatrix_surjective _ _ ei w.rightH_surjective
    factorE := by rw [Matrix.submatrix_mul_equiv, w.factorE]
    factorH := by rw [Matrix.submatrix_mul_equiv, w.factorH]
    quotient := w.quotient
    kernel := w.kernel
    quotient_surjective := w.quotient_surjective
    kernel_injective := w.kernel_injective
    quotient_kernel := by rw [ht, complement_submatrix_range]; exact w.quotient_kernel
    kernel_range := by rw [hs, complement_submatrix_kernel]; exact w.kernel_range
    coefficients := w.coefficients }

end ComplementPresentation

section General

variable {F o i n a b : Type*} [Field F] [Infinite F]
  [Fintype o] [Fintype i] [Fintype n] [Fintype a] [Fintype b]
  [DecidableEq o] [DecidableEq i] [DecidableEq n] [DecidableEq a] [DecidableEq b]

/-- Full intrinsic common-coefficient contraction for arbitrary original row
and column index types, with all empty-dimensional cases included. -/
theorem complement_common_coefficient_contraction_general
    (E H0 H1 : Matrix o i F)
    (hE : E.rank = Fintype.card n)
    (h0 : H0.rank = Fintype.card n) (h1 : H1.rank = Fintype.card n)
    (hj0 : Function.Injective (fromRows E H0).mulVec)
    (hj1 : Function.Injective (fromRows E H1).mulVec)
    (hs0 : Function.Surjective (fromCols E H0).mulVec)
    (hs1 : Function.Surjective (fromCols E H1).mulVec)
    (A0 A1 : Pencil F a b)
    (w0 : ComplementPresentation n n E H0 A0)
    (w1 : ComplementPresentation n n E H1 A1) :
    ∃ (L Li : Matrix a a F) (R Ri : Matrix b b F),
      L * Li = 1 ∧ Li * L = 1 ∧ R * Ri = 1 ∧ Ri * R = 1 ∧
      Pencil.normalRank ((L * A1.1 * R, L * A1.2 * R) - A0) ≤ (H1 - H0).rank := by
  classical
  have hno : Fintype.card n ≤ Fintype.card o := hE.symm.trans_le (Matrix.rank_le_card_height E)
  have hni : Fintype.card n ≤ Fintype.card i := hE.symm.trans_le (Matrix.rank_le_card_width E)
  let eo : (n ⊕ Fin (Fintype.card o - Fintype.card n)) ≃ o :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  let ei : (n ⊕ Fin (Fintype.card i - Fintype.card n)) ≃ i :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  have hi (H : Matrix o i F) (hh : Function.Injective (fromRows E H).mulVec) :
      Function.Injective (fromRows (E.submatrix eo ei) (H.submatrix eo ei)).mulVec := by
    have heq : fromRows (E.submatrix eo ei) (H.submatrix eo ei) =
        (fromRows E H).submatrix (Equiv.sumCongr eo eo) ei := by
      ext j k
      cases j <;> rfl
    rw [heq]
    exact complement_submatrix_injective _ _ _ hh
  have hs (H : Matrix o i F) (hh : Function.Surjective (fromCols E H).mulVec) :
      Function.Surjective (fromCols (E.submatrix eo ei) (H.submatrix eo ei)).mulVec := by
    have heq : fromCols (E.submatrix eo ei) (H.submatrix eo ei) =
        (fromCols E H).submatrix eo (Equiv.sumCongr ei ei) := by
      ext j k
      cases k <;> rfl
    rw [heq]
    exact complement_submatrix_surjective _ _ _ hh
  obtain ⟨L, Li, R, Ri, hLl, hLr, hRl, hRr, hRank⟩ :=
    complement_common_coefficient_contraction
      (E.submatrix eo ei) (H0.submatrix eo ei) (H1.submatrix eo ei)
      (by simpa only [Matrix.rank_submatrix] using hE)
      (by simpa only [Matrix.rank_submatrix] using h0)
      (by simpa only [Matrix.rank_submatrix] using h1)
      (hi H0 hj0) (hi H1 hj1) (hs H0 hs0) (hs H1 hs1)
      A0 A1 (w0.reindex eo ei) (w1.reindex eo ei)
  refine ⟨L, Li, R, Ri, hLl, hLr, hRl, hRr, ?_⟩
  have heq : H1.submatrix eo ei - H0.submatrix eo ei = (H1 - H0).submatrix eo ei := rfl
  rw [heq, Matrix.rank_submatrix] at hRank
  exact hRank

/-- The same intrinsic theorem as an inequality for the actual minimum over
both complete strict-equivalence classes. -/
theorem complement_orbitDistance_contraction
    (E H0 H1 : Matrix o i F)
    (hE : E.rank = Fintype.card n)
    (h0 : H0.rank = Fintype.card n) (h1 : H1.rank = Fintype.card n)
    (hj0 : Function.Injective (fromRows E H0).mulVec)
    (hj1 : Function.Injective (fromRows E H1).mulVec)
    (hs0 : Function.Surjective (fromCols E H0).mulVec)
    (hs1 : Function.Surjective (fromCols E H1).mulVec)
    (A0 A1 : Pencil F a b)
    (w0 : ComplementPresentation n n E H0 A0)
    (w1 : ComplementPresentation n n E H1 A1) :
    Pencil.orbitDistance A1 A0 ≤ (H1 - H0).rank := by
  obtain ⟨L, Li, R, Ri, hLl, hLr, hRl, hRr, hRank⟩ :=
    complement_common_coefficient_contraction_general E H0 H1 hE h0 h1
      hj0 hj1 hs0 hs1 A0 A1 w0 w1
  apply (Pencil.orbitDistance_le_iff A1 A0 _).mpr
  refine ⟨Pencil.transform L R A1, A0,
    ⟨L, Li, R, Ri, hLl, hLr, hRl, hRr, rfl⟩,
    Pencil.strictEquivalent_refl A0, ?_⟩
  exact hRank

end General

end MatCP1Converse
