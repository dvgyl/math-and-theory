module

public import MatCP1Converse.ForwardDilationRecovery
public import MatCP1Converse.ForwardDilationMatrix
public import MatCP1Converse.ComplementPresentation

@[expose] public section

namespace MatCP1Converse

section Coordinates

variable {F i j k : Type*} [Field F]
  [Fintype i] [Fintype j] [Fintype k]
  [DecidableEq i] [DecidableEq j] [DecidableEq k]
  {V W Z : Type*} [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup Z] [Module F Z]

noncomputable def recoveryConjMatrix (ew : (j → F) ≃ₗ[F] W)
    (ev : (i → F) ≃ₗ[F] V) (f : V →ₗ[F] W) : Matrix j i F :=
  LinearMap.toMatrix' (ew.symm.toLinearMap.comp (f.comp ev.toLinearMap))

omit [Fintype j] [DecidableEq j] in
@[simp] theorem recoveryConjMatrix_mulVec (ew : (j → F) ≃ₗ[F] W)
    (ev : (i → F) ≃ₗ[F] V) (f : V →ₗ[F] W) (x : i → F) :
    (recoveryConjMatrix ew ev f).mulVec x = ew.symm (f (ev x)) := by
  simp [recoveryConjMatrix]

omit [Fintype k] [DecidableEq k] in
theorem recoveryConjMatrix_comp (ez : (k → F) ≃ₗ[F] Z)
    (ew : (j → F) ≃ₗ[F] W) (ev : (i → F) ≃ₗ[F] V)
    (f : W →ₗ[F] Z) (g : V →ₗ[F] W) :
    recoveryConjMatrix ez ew f * recoveryConjMatrix ew ev g =
      recoveryConjMatrix ez ev (f.comp g) := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul]
  apply LinearMap.ext
  intro x
  simp [Matrix.toLin'_apply]

omit [Fintype j] [DecidableEq j] in
theorem recoveryConjMatrix_injective (ew : (j → F) ≃ₗ[F] W)
    (ev : (i → F) ≃ₗ[F] V) (f : V →ₗ[F] W) (hf : Function.Injective f) :
    Function.Injective (recoveryConjMatrix ew ev f).mulVec := by
  intro x y h
  rw [recoveryConjMatrix_mulVec, recoveryConjMatrix_mulVec] at h
  exact ev.injective (hf (ew.symm.injective h))

omit [Fintype j] [DecidableEq j] in
theorem recoveryConjMatrix_surjective (ew : (j → F) ≃ₗ[F] W)
    (ev : (i → F) ≃ₗ[F] V) (f : V →ₗ[F] W) (hf : Function.Surjective f) :
    Function.Surjective (recoveryConjMatrix ew ev f).mulVec := by
  intro w
  obtain ⟨v, hv⟩ := hf (ew w)
  exact ⟨ev.symm v, by simp [hv]⟩

omit [Fintype k] [DecidableEq k] in
theorem recoveryConjMatrix_kernel_range (ez : (k → F) ≃ₗ[F] Z)
    (ew : (j → F) ≃ₗ[F] W) (ev : (i → F) ≃ₗ[F] V)
    (f : W →ₗ[F] Z) (g : V →ₗ[F] W) (h : LinearMap.ker f = LinearMap.range g) :
    LinearMap.ker (recoveryConjMatrix ez ew f).mulVecLin =
      LinearMap.range (recoveryConjMatrix ew ev g).mulVecLin := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    have hx' : f (ew x) = 0 := by
      have hz : (recoveryConjMatrix ez ew f).mulVec x = 0 := hx
      rw [recoveryConjMatrix_mulVec] at hz
      exact ez.symm.injective (by simpa using hz)
    have hmem : ew x ∈ LinearMap.range g := by rw [← h]; exact hx'
    obtain ⟨v, hv⟩ := hmem
    refine ⟨ev.symm v, ?_⟩
    change (recoveryConjMatrix ew ev g).mulVec (ev.symm v) = x
    simp [hv]
  · rintro ⟨v, rfl⟩
    change (recoveryConjMatrix ez ew f).mulVec
      ((recoveryConjMatrix ew ev g).mulVec v) = 0
    simp only [recoveryConjMatrix_mulVec, LinearEquiv.apply_symm_apply]
    have hv : g (ev v) ∈ LinearMap.ker f := by rw [h]; exact ⟨ev v, rfl⟩
    change f (g (ev v)) = 0 at hv
    simp [hv]

def recoveryPairCoordinate (e : (i → F) ≃ₗ[F] V) :
    ((i ⊕ i) → F) ≃ₗ[F] (V × V) :=
  (LinearEquiv.sumArrowLequivProdArrow i i F F).trans (e.prodCongr e)

omit [Fintype j] [DecidableEq j] in
theorem recoveryConjMatrix_prod (ew : (j → F) ≃ₗ[F] W)
    (ev : (i → F) ≃ₗ[F] V) (f g : V →ₗ[F] W) :
    recoveryConjMatrix (recoveryPairCoordinate ew) ev (f.prod g) =
      Matrix.fromRows (recoveryConjMatrix ew ev f) (recoveryConjMatrix ew ev g) := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  funext r
  rcases r with r | r <;>
    simp [Matrix.toLin'_apply, recoveryConjMatrix_mulVec, Matrix.fromRows_mulVec,
      recoveryPairCoordinate, LinearEquiv.sumArrowLequivProdArrow]

omit [Fintype j] [DecidableEq j] in
theorem recoveryConjMatrix_coprod (ew : (j → F) ≃ₗ[F] W)
    (ev : (i → F) ≃ₗ[F] V) (f g : V →ₗ[F] W) :
    recoveryConjMatrix ew (recoveryPairCoordinate ev) (f.coprod g) =
      Matrix.fromCols (recoveryConjMatrix ew ev f) (recoveryConjMatrix ew ev g) := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp [Matrix.toLin'_apply, recoveryConjMatrix_mulVec, Matrix.fromCols_mulVec,
    recoveryPairCoordinate, LinearEquiv.sumArrowLequivProdArrow]
  rfl

omit [Fintype j] [DecidableEq j] in
theorem recoveryConjMatrix_prodMap (ew : (j → F) ≃ₗ[F] W)
    (ev : (i → F) ≃ₗ[F] V) (f g : V →ₗ[F] W) :
    recoveryConjMatrix (recoveryPairCoordinate ew) (recoveryPairCoordinate ev)
      (f.prodMap g) = Matrix.fromBlocks (recoveryConjMatrix ew ev f) 0 0
        (recoveryConjMatrix ew ev g) := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  funext r
  rcases r with r | r <;>
    simp [Matrix.toLin'_apply, recoveryConjMatrix_mulVec, Matrix.fromBlocks_mulVec,
      recoveryPairCoordinate, LinearEquiv.sumArrowLequivProdArrow]
  all_goals rfl

omit [Fintype j] [DecidableEq j] in
@[simp] theorem recoveryConjMatrix_zero (ew : (j → F) ≃ₗ[F] W)
    (ev : (i → F) ≃ₗ[F] V) : recoveryConjMatrix ew ev (0 : V →ₗ[F] W) = 0 := by
  simp [recoveryConjMatrix]

@[simp] theorem recoveryConjMatrix_id (ev : (i → F) ≃ₗ[F] V) :
    recoveryConjMatrix ev ev LinearMap.id = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp [Matrix.toLin'_apply]

omit [Fintype j] [DecidableEq j] in
theorem recoveryConjMatrix_rank (ew : (j → F) ≃ₗ[F] W)
    (ev : (i → F) ≃ₗ[F] V) (f : V →ₗ[F] W) :
    (recoveryConjMatrix ew ev f).rank = Module.finrank F (LinearMap.range f) := by
  change Module.finrank F (LinearMap.range (Matrix.toLin' (recoveryConjMatrix ew ev f))) = _
  rw [recoveryConjMatrix, Matrix.toLin'_toMatrix', LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top f ev.range]
  exact ew.symm.finrank_map_eq _

end Coordinates

section Dilation

variable {F m n : Type*} [Field F] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

def matrixDilationEval (A0 A1 : Matrix m n F) (c d t : F) :
    Matrix (m ⊕ (m ⊕ n)) (n ⊕ (n ⊕ m)) F :=
  matrixDilationConstant A0 c d + t • matrixDilationLinear A1

theorem matrixDilationEval_conj (A0 A1 : Matrix m n F) (c d t : F) :
    (dilationSumCoordinate (F := F) m n).toLinearMap.comp
      ((Matrix.toLin' (matrixDilationEval A0 A1 c d t)).comp
        (dilationSumCoordinate (F := F) n m).symm.toLinearMap) =
      dilationEval (Matrix.toLin' A0) (Matrix.toLin' A1) c d t := by
  simp only [matrixDilationEval, map_add, map_smul, LinearMap.add_comp, LinearMap.smul_comp,
    LinearMap.comp_add, LinearMap.comp_smul, matrixDilationConstant_conj,
    matrixDilationLinear_conj, dilationEval]

theorem matrixDilationEval_eq_conjMatrix (A0 A1 : Matrix m n F) (c d t : F) :
    matrixDilationEval A0 A1 c d t =
      recoveryConjMatrix (dilationSumCoordinate (F := F) m n)
        (dilationSumCoordinate (F := F) n m)
        (dilationEval (Matrix.toLin' A0) (Matrix.toLin' A1) c d t) := by
  apply Matrix.toLin'.injective
  simp only [recoveryConjMatrix, Matrix.toLin'_toMatrix']
  rw [← matrixDilationEval_conj]
  apply LinearMap.ext
  intro x
  simp

theorem matrix_dilation_rank_at_d (A0 A1 : Matrix m n F) (c d : F) :
    (matrixDilationEval A0 A1 c d d).rank = Fintype.card (n ⊕ m) := by
  rw [matrixDilationEval_eq_conjMatrix, recoveryConjMatrix_rank]
  simpa only [Module.finrank_pi, Module.finrank_self, mul_one, Fintype.card_sum] using
    dilation_rank_at_d (Matrix.toLin' A0) (Matrix.toLin' A1) c d

theorem matrix_dilation_rank_at_c (A0 A1 : Matrix m n F) (c d : F) :
    (matrixDilationEval A0 A1 c d c).rank = Fintype.card (n ⊕ m) := by
  rw [matrixDilationEval_eq_conjMatrix, recoveryConjMatrix_rank]
  simpa only [Module.finrank_pi, Module.finrank_self, mul_one, Fintype.card_sum] using
    dilation_rank_at_c (Matrix.toLin' A0) (Matrix.toLin' A1) c d

theorem matrix_dilation_joint_injective (A0 A1 : Matrix m n F) (c d : F) (hcd : c ≠ d) :
    Function.Injective (Matrix.fromRows (matrixDilationEval A0 A1 c d d)
      (matrixDilationEval A0 A1 c d c)).mulVec := by
  rw [matrixDilationEval_eq_conjMatrix, matrixDilationEval_eq_conjMatrix,
    ← recoveryConjMatrix_prod]
  exact recoveryConjMatrix_injective _ _ _
    (dilation_anchor_pair_injective (Matrix.toLin' A0) (Matrix.toLin' A1) c d hcd)

theorem matrix_dilation_joint_surjective (A0 A1 : Matrix m n F) (c d : F) (hcd : c ≠ d) :
    Function.Surjective (Matrix.fromCols (matrixDilationEval A0 A1 c d d)
      (matrixDilationEval A0 A1 c d c)).mulVec := by
  rw [matrixDilationEval_eq_conjMatrix, matrixDilationEval_eq_conjMatrix,
    ← recoveryConjMatrix_coprod]
  exact recoveryConjMatrix_surjective _ _ _
    (dilation_anchor_coprod_surjective (Matrix.toLin' A0) (Matrix.toLin' A1) c d hcd)

/-- The actual complementary presentation of the dilation at its two anchors.
Every full-rank, kernel, range and coefficient condition is constructed and
proved here; the result has no eigenstructure or recovery premise. -/
noncomputable def matrix_dilation_complement_presentation
    (A0 A1 : Matrix m n F) (c d : F) (hcd : c ≠ d) :
    ComplementPresentation (n ⊕ m) (n ⊕ m)
      (matrixDilationEval A0 A1 c d d) (matrixDilationEval A0 A1 c d c)
      (A0 + d • A1, A0 + c • A1) := by
  let a0 := Matrix.toLin' A0
  let a1 := Matrix.toLin' A1
  let en := dilationSumCoordinate (F := F) n m
  let em := dilationSumCoordinate (F := F) m n
  let ej := LinearEquiv.sumArrowLequivProdArrow n m F F
  let ejj := recoveryPairCoordinate ej
  let uE := dilationELeft a0 a1 c d
  let vE := dilationERight (F := F) (V := n → F) (W := m → F)
  let uH := dilationHLeft (F := F) (V := n → F) (W := m → F)
  let vH := dilationHRight a0 a1 c d
  let q := dilationQuotient a0 a1 c
  let k := dilationKernelLift a0 a1 d
  let er := LinearEquiv.refl F (m → F)
  let ec := LinearEquiv.refl F (n → F)
  have hd0 : Matrix.fromBlocks (0 : Matrix (n ⊕ m) (n ⊕ m) F) 0 0 1 =
      recoveryConjMatrix ejj ejj
        ((0 : ((n → F) × (m → F)) →ₗ[F] ((n → F) × (m → F))).prodMap LinearMap.id) := by
    simpa only [recoveryConjMatrix_zero, recoveryConjMatrix_id, ejj] using
      (recoveryConjMatrix_prodMap ej ej 0 LinearMap.id).symm
  have hd1 : Matrix.fromBlocks (1 : Matrix (n ⊕ m) (n ⊕ m) F) 0 0 0 =
      recoveryConjMatrix ejj ejj
        (LinearMap.id.prodMap (0 : ((n → F) × (m → F)) →ₗ[F] ((n → F) × (m → F)))) := by
    simpa only [recoveryConjMatrix_zero, recoveryConjMatrix_id, ejj] using
      (recoveryConjMatrix_prodMap ej ej LinearMap.id 0).symm
  refine {
    leftE := recoveryConjMatrix em ej uE
    rightE := recoveryConjMatrix ej en vE
    leftH := recoveryConjMatrix em ej uH
    rightH := recoveryConjMatrix ej en vH
    leftE_injective := recoveryConjMatrix_injective _ _ _ (dilationELeft_injective a0 a1 c d)
    rightE_surjective := recoveryConjMatrix_surjective _ _ _ dilationERight_surjective
    leftH_injective := recoveryConjMatrix_injective _ _ _ dilationHLeft_injective
    rightH_surjective := recoveryConjMatrix_surjective _ _ _ (dilationHRight_surjective a0 a1 c d)
    factorE := ?_
    factorH := ?_
    quotient := recoveryConjMatrix er ejj q
    kernel := recoveryConjMatrix ejj ec k
    quotient_surjective := recoveryConjMatrix_surjective _ _ _ (dilationQuotient_surjective a0 a1 c)
    kernel_injective := recoveryConjMatrix_injective _ _ _ (dilationKernelLift_injective a0 a1 d)
    quotient_kernel := ?_
    kernel_range := ?_
    coefficients := ?_ }
  · rw [recoveryConjMatrix_comp]
    change recoveryConjMatrix em en ((dilationELeft a0 a1 c d).comp dilationERight) = _
    rw [dilation_factor_E]
    exact (matrixDilationEval_eq_conjMatrix A0 A1 c d d).symm
  · rw [recoveryConjMatrix_comp]
    change recoveryConjMatrix em en (dilationHLeft.comp (dilationHRight a0 a1 c d)) = _
    rw [dilation_factor_H]
    exact (matrixDilationEval_eq_conjMatrix A0 A1 c d c).symm
  · have hq := recoveryConjMatrix_kernel_range er ejj en q (vE.prod vH)
      (dilationQuotient_ker a0 a1 c d hcd)
    simpa only [ejj, recoveryConjMatrix_prod] using hq
  · have hk := recoveryConjMatrix_kernel_range em ejj ec (uE.coprod uH) k
      (dilationKernelLift_range a0 a1 c d hcd).symm
    simpa only [ejj, recoveryConjMatrix_coprod] using hk.symm
  · apply Prod.ext
    · change recoveryConjMatrix er ejj q * Matrix.fromBlocks 0 0 0 1 *
        recoveryConjMatrix ejj ec k = A0 + d • A1
      rw [hd0, recoveryConjMatrix_comp, recoveryConjMatrix_comp]
      change recoveryConjMatrix er ec
        ((dilationQuotient a0 a1 c).comp
          (((0 : ((n → F) × (m → F)) →ₗ[F] ((n → F) × (m → F))).prodMap LinearMap.id).comp
            (dilationKernelLift a0 a1 d))) = _
      rw [dilation_complement_constant]
      simp [recoveryConjMatrix, er, ec, a0, a1]
    · change recoveryConjMatrix er ejj q * Matrix.fromBlocks 1 0 0 0 *
        recoveryConjMatrix ejj ec k = A0 + c • A1
      rw [hd1, recoveryConjMatrix_comp, recoveryConjMatrix_comp]
      change recoveryConjMatrix er ec
        ((dilationQuotient a0 a1 c).comp
          ((LinearMap.id.prodMap (0 : ((n → F) × (m → F)) →ₗ[F] ((n → F) × (m → F)))).comp
            (dilationKernelLift a0 a1 d))) = _
      rw [dilation_complement_linear]
      simp [recoveryConjMatrix, er, ec, a0, a1]

end Dilation

end MatCP1Converse
