module

public import MatCP1Converse.ComplementInvariance
public import MatCP1Converse.RankChart

@[expose] public section

namespace MatCP1Converse

open Matrix

variable {F n p m : Type*} [Field F]
  [Fintype n] [Fintype p] [Fintype m]
  [DecidableEq n] [DecidableEq p] [DecidableEq m]

/-- A block matrix of actual rank `card n` with an invertible `n`-corner has
the forced lower-right block. No rank-factorization or Schur condition is assumed. -/
theorem matrix_block_completed_of_rank
    (G Gi : Matrix n n F) (B : Matrix n m F) (C : Matrix p n F) (D : Matrix p m F)
    (hGiG : Gi * G = 1)
    (hRank : (fromBlocks G B C D).rank = Fintype.card n) :
    D = C * Gi * B := by
  let J : Matrix (n ⊕ p) n F := fromRows G C
  let H := fromBlocks G B C D
  have hJ : Function.Injective J.mulVec := by
    intro v w hvw
    have hh := congrArg (fun x : n ⊕ p → F => x ∘ Sum.inl) hvw
    have heq : G *ᵥ v = G *ᵥ w := by simpa [J, fromRows_mulVec] using hh
    have hh := congrArg (fun x => Gi *ᵥ x) heq
    simpa only [Matrix.mulVec_mulVec, hGiG, Matrix.one_mulVec] using hh
  have hJrank : Module.finrank F (LinearMap.range J.mulVecLin) = Fintype.card n := by
    rw [LinearMap.finrank_range_of_inj hJ, Module.finrank_fintype_fun_eq_card]
  have hr : LinearMap.range J.mulVecLin ≤ LinearMap.range H.mulVecLin := by
    rintro w ⟨v, rfl⟩
    refine ⟨Sum.elim v 0, ?_⟩
    simp [H, J, fromBlocks_mulVec, fromRows_mulVec]
  have heq : LinearMap.range J.mulVecLin = LinearMap.range H.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hr (hJrank.trans hRank.symm)
  apply Matrix.mulVec_injective
  funext v
  have hm : H *ᵥ Sum.elim (0 : n → F) v ∈ LinearMap.range J.mulVecLin := by
    rw [heq]
    exact LinearMap.mem_range_self H.mulVecLin _
  obtain ⟨w, hw⟩ := hm
  have ht : G *ᵥ w = B *ᵥ v := by
    have hh := congrArg (fun x : n ⊕ p → F => x ∘ Sum.inl) hw
    simpa [H, J, fromBlocks_mulVec, fromRows_mulVec] using hh
  have hb : C *ᵥ w = D *ᵥ v := by
    have hh := congrArg (fun x : n ⊕ p → F => x ∘ Sum.inr) hw
    simpa [H, J, fromBlocks_mulVec, fromRows_mulVec] using hh
  have hw' : w = Gi *ᵥ (B *ᵥ v) := by
    have hh := congrArg (fun x => Gi *ᵥ x) ht
    simpa only [Matrix.mulVec_mulVec, hGiG, Matrix.one_mulVec] using hh
  rw [hw'] at hb
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hb.symm

/-- The actual absence of a common constant right kernel forces the chart's
upper-right block to have full column rank. -/
theorem complement_chartB_injective_of_joint
    (G Gi : Matrix n n F) (B : Matrix n m F) (C : Matrix p n F)
    (hjoint : Function.Injective
      (fromRows (fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F))
        (completedBlock G Gi B C)).mulVec) :
    Function.Injective B.mulVec := by
  intro v w hvw
  have hh : (Sum.elim (0 : n → F) v : n ⊕ m → F) = Sum.elim (0 : n → F) w := by
    apply hjoint
    simp [fromRows_mulVec, completedBlock, fromBlocks_mulVec,
      ← Matrix.mulVec_mulVec, hvw]
  exact congrArg (fun x : n ⊕ m → F => x ∘ Sum.inr) hh

/-- The actual spanning of the target by the two coefficient ranges forces
the chart's lower-left block to have full row rank. -/
theorem complement_chartC_surjective_of_joint
    (G Gi : Matrix n n F) (B : Matrix n m F) (C : Matrix p n F)
    (hjoint : Function.Surjective
      (fromCols (fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F))
        (completedBlock G Gi B C)).mulVec) :
    Function.Surjective C.mulVec := by
  intro w
  obtain ⟨v, hv⟩ := hjoint (Sum.elim 0 w)
  refine ⟨((v ∘ Sum.inr) ∘ Sum.inl) +
    Gi *ᵥ (B *ᵥ ((v ∘ Sum.inr) ∘ Sum.inr)), ?_⟩
  have hh := congrArg (fun x : n ⊕ p → F => x ∘ Sum.inr) hv
  funext i
  simpa [fromCols_mulVec, completedBlock, fromBlocks_mulVec,
    Matrix.mulVec_add, ← Matrix.mulVec_mulVec, Function.comp_def] using congrFun hh i

end MatCP1Converse
