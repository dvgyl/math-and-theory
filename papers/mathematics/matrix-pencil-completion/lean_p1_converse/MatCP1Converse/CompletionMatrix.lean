module

public import MatCP1Converse.CompletionShift
public import MatCP1Converse.MatrixExtension
public import MatCP1.MatrixCompression
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

namespace MatCP1Converse

variable {F m n x : Type*} [Field F]
  [Fintype m] [Fintype n] [Fintype x]
  [DecidableEq m] [DecidableEq n] [DecidableEq x]

omit [Fintype m] [DecidableEq m] in
/-- General block matrices, including their off-diagonal borders, act as the
four-block linear map in product coordinates. -/
theorem completion_matrix_blocks_conj
    (A : Matrix m n F) (B : Matrix m x F) (C : Matrix x n F) (D : Matrix x x F) :
    (LinearEquiv.sumArrowLequivProdArrow m x F F).toLinearMap.comp
      ((Matrix.toLin' (Matrix.fromBlocks A B C D)).comp
        (LinearEquiv.sumArrowLequivProdArrow n x F F).symm.toLinearMap) =
      ((Matrix.toLin' A).coprod (Matrix.toLin' B)).prod
        ((Matrix.toLin' C).coprod (Matrix.toLin' D)) := by
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · funext i
    simp [Matrix.toLin'_apply, Matrix.fromBlocks_mulVec,
      LinearEquiv.sumArrowLequivProdArrow]
    rfl
  · funext i
    simp [Matrix.toLin'_apply, Matrix.fromBlocks_mulVec,
      LinearEquiv.sumArrowLequivProdArrow]
    rfl

/-- Literal-matrix fixed-factor extraction. All strict-equivalence inverses are
explicit. The rank bound is the actual matrix rank over `F`, and the conclusion
is the full affine pencil identity for every parameter `t`. -/
theorem matrix_completion_extract_fixed_factor [Infinite F]
    (d : F) (A0 A1 B0 B1 : Matrix m n F)
    (X0 X1 : Matrix m x F) (Y0 Y1 : Matrix x n F) (Z0 Z1 : Matrix x x F)
    (P Pi : Matrix (m ⊕ x) (m ⊕ x) F) (Q Qi : Matrix (n ⊕ x) (n ⊕ x) F)
    (hPPi : P * Pi = 1) (hPiP : Pi * P = 1)
    (hQQi : Q * Qi = 1) (hQiQ : Qi * Q = 1)
    (hM0 : P * Matrix.fromBlocks B0 0 0 (-d • (1 : Matrix x x F)) * Q =
      Matrix.fromBlocks A0 X0 Y0 Z0)
    (hM1 : P * Matrix.fromBlocks B1 0 0 (1 : Matrix x x F) * Q =
      Matrix.fromBlocks A1 X1 Y1 Z1)
    (hRank : (A0 + d • A1).rank = (B0 + d • B1).rank) :
    ∃ (E : Matrix m n F) (p pi : Matrix m m F) (q qi : Matrix n n F),
      E.rank ≤ Fintype.card x ∧
      p * pi = 1 ∧ pi * p = 1 ∧ q * qi = 1 ∧ qi * q = 1 ∧
      A0 + d • E = p * B0 * q ∧ A1 - E = p * B1 * q ∧
      ∀ t : F, A0 + t • A1 - (t - d) • E = p * (B0 + t • B1) * q := by
  classical
  have hP1 : (Matrix.toLin' P).comp (Matrix.toLin' Pi) = LinearMap.id := by
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_one] using congrArg Matrix.toLin' hPPi
  have hP2 : (Matrix.toLin' Pi).comp (Matrix.toLin' P) = LinearMap.id := by
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_one] using congrArg Matrix.toLin' hPiP
  have hQ1 : (Matrix.toLin' Q).comp (Matrix.toLin' Qi) = LinearMap.id := by
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_one] using congrArg Matrix.toLin' hQQi
  have hQ2 : (Matrix.toLin' Qi).comp (Matrix.toLin' Q) = LinearMap.id := by
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_one] using congrArg Matrix.toLin' hQiQ
  let eP : ((m ⊕ x) → F) ≃ₗ[F] ((m ⊕ x) → F) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' P) (Matrix.toLin' Pi) hP1 hP2
  let eQ : ((n ⊕ x) → F) ≃ₗ[F] ((n ⊕ x) → F) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' Q) (Matrix.toLin' Qi) hQ1 hQ2
  let em := LinearEquiv.sumArrowLequivProdArrow m x F F
  let en := LinearEquiv.sumArrowLequivProdArrow n x F F
  let P' := (em.symm.trans eP).trans em
  let Q' := (en.symm.trans eQ).trans en
  let M0 := ((Matrix.toLin' A0).coprod (Matrix.toLin' X0)).prod
    ((Matrix.toLin' Y0).coprod (Matrix.toLin' Z0))
  let M1 := ((Matrix.toLin' A1).coprod (Matrix.toLin' X1)).prod
    ((Matrix.toLin' Y1).coprod (Matrix.toLin' Z1))
  have hC0 : (LinearMap.fst F (m → F) (x → F)).comp
      (M0.comp (LinearMap.inl F (n → F) (x → F))) = Matrix.toLin' A0 := by
    ext v i
    simp [M0]
  have hC1 : (LinearMap.fst F (m → F) (x → F)).comp
      (M1.comp (LinearMap.inl F (n → F) (x → F))) = Matrix.toLin' A1 := by
    ext v i
    simp [M1]
  have hcoef (B A : Matrix m n F) (X : Matrix m x F) (Y : Matrix x n F)
      (Z D : Matrix x x F)
      (hh : P * Matrix.fromBlocks B 0 0 D * Q = Matrix.fromBlocks A X Y Z) :
      ((Matrix.toLin' A).coprod (Matrix.toLin' X)).prod
        ((Matrix.toLin' Y).coprod (Matrix.toLin' Z)) =
      P'.toLinearMap.comp (((Matrix.toLin' B).prodMap (Matrix.toLin' D)).comp
        Q'.toLinearMap) := by
    rw [← completion_matrix_blocks_conj, ← hh]
    have hd := MatCP1.block_mulVecLin_conj B D
    simp only [← Matrix.toLin'_apply'] at hd
    rw [← hd]
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
    apply LinearMap.ext
    intro v
    simp only [P', Q', eP, eQ, em, en, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, LinearEquiv.coe_ofLinearMap,
      LinearEquiv.symm_apply_apply]
  have hc0 := hcoef B0 A0 X0 Y0 Z0 (-d • (1 : Matrix x x F)) hM0
  have hc1 := hcoef B1 A1 X1 Y1 Z1 (1 : Matrix x x F) hM1
  have hR : Module.finrank F (LinearMap.range (Matrix.toLin' A0 + d • Matrix.toLin' A1)) =
      Module.finrank F (LinearMap.range (Matrix.toLin' B0 + d • Matrix.toLin' B1)) := by
    change Module.finrank F (LinearMap.range (Matrix.toLin' (A0 + d • A1))) =
      Module.finrank F (LinearMap.range (Matrix.toLin' (B0 + d • B1))) at hRank
    have heval (C0 C1 : Matrix m n F) :
        Matrix.toLin' (C0 + d • C1) = Matrix.toLin' C0 + d • Matrix.toLin' C1 := by
      apply LinearMap.ext
      intro v
      simp [Matrix.toLin'_apply]
    rw [heval, heval] at hRank
    exact hRank
  obtain ⟨E, p, q, hE, h0, h1, ht⟩ := completion_extract_fixed_factor d
    (Matrix.toLin' A0) (Matrix.toLin' A1) (Matrix.toLin' B0) (Matrix.toLin' B1)
    M0 M1 P' Q' hC0 hC1
    (by simpa only [map_smul, Matrix.toLin'_one] using hc0)
    (by simpa only [Matrix.toLin'_one] using hc1) hR
  refine ⟨LinearMap.toMatrix' E, LinearMap.toMatrix' p.toLinearMap,
    LinearMap.toMatrix' p.symm.toLinearMap, LinearMap.toMatrix' q.toLinearMap,
    LinearMap.toMatrix' q.symm.toLinearMap, ?_, toMatrix_equiv_mul_symm p,
    toMatrix_equiv_mul_symm p.symm, toMatrix_equiv_mul_symm q,
    toMatrix_equiv_mul_symm q.symm, ?_, ?_, ?_⟩
  · change Module.finrank F (LinearMap.range (Matrix.toLin' (LinearMap.toMatrix' E))) ≤
      Fintype.card x
    rw [Matrix.toLin'_toMatrix']
    simpa only [Module.finrank_pi, Module.finrank_self, mul_one] using hE
  · simpa only [map_add, map_smul, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_comp,
      Matrix.mul_assoc] using congrArg LinearMap.toMatrix' h0
  · simpa only [map_sub, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_comp,
      Matrix.mul_assoc] using congrArg LinearMap.toMatrix' h1
  · intro t
    simpa only [map_add, map_smul, map_sub, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_comp, Matrix.mul_assoc] using congrArg LinearMap.toMatrix' (ht t)

end MatCP1Converse
