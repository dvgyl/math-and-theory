module

public import MatCP1Converse.CompletionShift
public import MatCP1Converse.CompressionCompletion
public import MatCP1Converse.CompletionMatrix

@[expose] public section

namespace MatCP1Converse

section Linear

variable {F U V W : Type*} [Field F] [Infinite F]
  [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
  [FiniteDimensional F U] [FiniteDimensional F V] [FiniteDimensional F W]

/-- Fixed-factor extraction directly from the original subpencil/compression
premise. The actual completion and its strict equivalences are constructed. -/
theorem subpencil_extract_fixed_factor
    (d : F) (A0 A1 B0 B1 : U →ₗ[F] W)
    (h : MatCP1.JointCompression (fun i : Bool => if i then A1 else A0)
      (fun i : Bool => if i then B1.prodMap (LinearMap.id : V →ₗ[F] V)
        else B0.prodMap (-d • (LinearMap.id : V →ₗ[F] V))))
    (hRank : Module.finrank F (LinearMap.range (A0 + d • A1)) =
      Module.finrank F (LinearMap.range (B0 + d • B1))) :
    ∃ (E : U →ₗ[F] W) (p : W ≃ₗ[F] W) (q : U ≃ₗ[F] U),
      Module.finrank F (LinearMap.range E) ≤ Module.finrank F V ∧
      A0 + d • E = p.toLinearMap.comp (B0.comp q.toLinearMap) ∧
      A1 - E = p.toLinearMap.comp (B1.comp q.toLinearMap) ∧
      ∀ t : F, A0 + t • A1 - (t - d) • E =
        p.toLinearMap.comp ((B0 + t • B1).comp q.toLinearMap) := by
  obtain ⟨M, P, Q, hcorner, hM⟩ := jointCompression_exists_strict_completion _ _ h
  exact completion_extract_fixed_factor d A0 A1 B0 B1 (M false) (M true) P Q
    (hcorner false) (hcorner true) (hM false) (hM true) hRank

end Linear

section Matrix

variable {F I m n x : Type*} [Field F]
  [Fintype m] [Fintype n] [Fintype x]
  [DecidableEq m] [DecidableEq n] [DecidableEq x]

omit [DecidableEq m] in
theorem completion_matrix_compression_to_product
    (A B : I → Matrix m n F) (S : I → Matrix x x F)
    (h : MatCP1.MatrixJointCompression A (fun i => Matrix.fromBlocks (B i) 0 0 (S i))) :
    MatCP1.JointCompression (fun i => Matrix.toLin' (A i))
      (fun i => (Matrix.toLin' (B i)).prodMap (Matrix.toLin' (S i))) := by
  obtain ⟨p, q, hp, hq, hpq⟩ := (MatCP1.matrixJointCompression_iff_linear _ _).mp h
  let em := LinearEquiv.sumArrowLequivProdArrow m x F F
  let en := LinearEquiv.sumArrowLequivProdArrow n x F F
  refine ⟨p.comp em.symm.toLinearMap, en.toLinearMap.comp q,
    hp.comp em.symm.surjective, en.injective.comp hq, ?_⟩
  intro i
  have hd := MatCP1.block_mulVecLin_conj (B i) (S i)
  simp only [← Matrix.toLin'_apply'] at hd
  change (p.comp em.symm.toLinearMap).comp
    (((Matrix.toLin' (B i)).prodMap (Matrix.toLin' (S i))).comp (en.toLinearMap.comp q)) =
      Matrix.toLin' (A i)
  rw [← hd]
  apply LinearMap.ext
  intro v
  simpa only [em, en, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Matrix.toLin'_apply'] using LinearMap.congr_fun (hpq i) v

/-- The literal matrix form of the complete conditional lemma, starting from
the original full-row/full-column subpencil witnesses rather than an assumed
invertible completion. All output inverses and both coefficients are explicit. -/
theorem matrix_subpencil_extract_fixed_factor [Infinite F]
    (d : F) (A0 A1 B0 B1 : Matrix m n F)
    (P : Matrix m (m ⊕ x) F) (Q : Matrix (n ⊕ x) n F)
    (hP : Function.Surjective P.mulVec) (hQ : Function.Injective Q.mulVec)
    (h0 : P * Matrix.fromBlocks B0 0 0 (-d • (1 : Matrix x x F)) * Q = A0)
    (h1 : P * Matrix.fromBlocks B1 0 0 (1 : Matrix x x F) * Q = A1)
    (hRank : (A0 + d • A1).rank = (B0 + d • B1).rank) :
    ∃ (E : Matrix m n F) (p pi : Matrix m m F) (q qi : Matrix n n F),
      E.rank ≤ Fintype.card x ∧
      p * pi = 1 ∧ pi * p = 1 ∧ q * qi = 1 ∧ qi * q = 1 ∧
      A0 + d • E = p * B0 * q ∧ A1 - E = p * B1 * q ∧
      ∀ t : F, A0 + t • A1 - (t - d) • E = p * (B0 + t • B1) * q := by
  classical
  let AA := fun i : Bool => if i then A1 else A0
  let BB := fun i : Bool => if i then B1 else B0
  let SS := fun i : Bool => if i then (1 : Matrix x x F) else -d • 1
  have hc : MatCP1.MatrixJointCompression AA (fun i => Matrix.fromBlocks (BB i) 0 0 (SS i)) := by
    exact ⟨P, Q, hP, hQ, by intro i; cases i <;> assumption⟩
  have hc' := completion_matrix_compression_to_product AA BB SS hc
  have hl : MatCP1.JointCompression
      (fun i : Bool => if i then Matrix.toLin' A1 else Matrix.toLin' A0)
      (fun i : Bool => if i then (Matrix.toLin' B1).prodMap (LinearMap.id : (x → F) →ₗ[F] (x → F))
        else (Matrix.toLin' B0).prodMap (-d • (LinearMap.id : (x → F) →ₗ[F] (x → F)))) := by
    convert hc' using 1 <;> funext i <;> cases i <;> simp [AA, BB, SS, neg_smul]
    exact congrArg ((Matrix.toLin' B0).prodMap)
      (neg_smul d (LinearMap.id : (x → F) →ₗ[F] (x → F)))
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
  obtain ⟨E, p, q, hE, he0, he1, het⟩ := subpencil_extract_fixed_factor d
    (Matrix.toLin' A0) (Matrix.toLin' A1) (Matrix.toLin' B0) (Matrix.toLin' B1) hl hR
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
      Matrix.mul_assoc] using congrArg LinearMap.toMatrix' he0
  · simpa only [map_sub, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_comp,
      Matrix.mul_assoc] using congrArg LinearMap.toMatrix' he1
  · intro t
    simpa only [map_add, map_smul, map_sub, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_comp, Matrix.mul_assoc] using congrArg LinearMap.toMatrix' (het t)

end Matrix

end MatCP1Converse
