module

public import MatCP1Converse.Pencil
public import MatCP1Converse.CompletionNormalization
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace MatCP1Converse

open Matrix
open scoped Polynomial

section Schur

variable {F n p q : Type*} [Field F]
  [Fintype n] [Fintype p] [Fintype q] [DecidableEq n]

omit [Fintype p] [DecidableEq n] in
/-- Four-block matrices and their product-space maps have the same actual rank,
including unequal lower row and column dimensions. -/
theorem rank_blocks_product_map
    (A : Matrix n n F) (B : Matrix n q F) (C : Matrix p n F) (D : Matrix p q F) :
    (fromBlocks A B C D).rank =
      Module.finrank F (LinearMap.range
        ((A.mulVecLin.coprod B.mulVecLin).prod (C.mulVecLin.coprod D.mulVecLin))) := by
  let en := LinearEquiv.sumArrowLequivProdArrow n q F F
  let em := LinearEquiv.sumArrowLequivProdArrow n p F F
  have heq : em.toLinearMap.comp
      ((fromBlocks A B C D).mulVecLin.comp en.symm.toLinearMap) =
      (A.mulVecLin.coprod B.mulVecLin).prod (C.mulVecLin.coprod D.mulVecLin) := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · funext i
      simp [Matrix.fromBlocks_mulVec, en, em, LinearEquiv.sumArrowLequivProdArrow]
      rfl
    · funext j
      simp [Matrix.fromBlocks_mulVec, en, em, LinearEquiv.sumArrowLequivProdArrow]
      rfl
  rw [← heq, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ en.symm.range]
  exact (em.finrank_map_eq _).symm

omit [Fintype p] in
/-- An invertible square corner and a full-block rank bound force the literal
Schur complement to vanish. -/
theorem block_schur_eq_of_rank_le
    (G Gi : Matrix n n F) (B : Matrix n q F) (C : Matrix p n F) (D : Matrix p q F)
    (hGiG : Gi * G = 1) (hGGi : G * Gi = 1)
    (hRank : (fromBlocks G B C D).rank ≤ Fintype.card n) :
    D = C * Gi * B := by
  have hG : G.rank = Fintype.card n :=
    Matrix.rank_of_det_ne_zero (Matrix.det_ne_zero_of_left_inverse hGiG)
  have hlow : G.rank ≤ (fromBlocks G B C D).rank := by
    have heq : (fromBlocks G B C D).submatrix Sum.inl Sum.inl = G := by ext; rfl
    simpa only [heq] using
      (Matrix.rank_submatrix_le (fromBlocks G B C D) Sum.inl Sum.inl)
  have hr : (fromBlocks G B C D).rank = G.rank := le_antisymm
    (hRank.trans_eq hG.symm) hlow
  have hr' : Module.finrank F (LinearMap.range
      ((G.mulVecLin.coprod B.mulVecLin).prod (C.mulVecLin.coprod D.mulVecLin))) =
      Module.finrank F (LinearMap.range G.mulVecLin) := by
    rw [← rank_blocks_product_map]
    exact hr
  obtain ⟨U, T, hB, hC, hD⟩ := completion_border_factorization
    G.mulVecLin B.mulVecLin C.mulVecLin D.mulVecLin hr'
  apply Matrix.mulVec_injective
  funext v
  have hb := LinearMap.congr_fun hB v
  have hd := LinearMap.congr_fun hD v
  have hc := LinearMap.congr_fun hC (Gi *ᵥ (B *ᵥ v))
  change B *ᵥ v = G *ᵥ U v at hb
  change D *ᵥ v = T (G *ᵥ U v) at hd
  change C *ᵥ (Gi *ᵥ (B *ᵥ v)) = T (G *ᵥ (Gi *ᵥ (B *ᵥ v))) at hc
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hGGi, Matrix.one_mul] at hc
  simpa only [Matrix.mulVec_mulVec] using (hd.trans (congrArg T hb.symm)).trans hc.symm

end Schur

section Polynomial

variable {F n p q k : Type*} [Field F]

/-- Constant polynomial matrix used in the exact rank-decomposition argument. -/
def rankPolynomialConst (A : Matrix p q F) : Matrix p q F[X] := A.map Polynomial.C

@[simp] theorem rankPolynomialConst_mul [Fintype n]
    (A : Matrix p n F) (B : Matrix n q F) :
    rankPolynomialConst (A * B) = rankPolynomialConst A * rankPolynomialConst B :=
  Matrix.map_mul

@[simp] theorem rankPolynomialConst_zero :
    rankPolynomialConst (0 : Matrix p q F) = 0 := by ext; simp [rankPolynomialConst]

@[simp] theorem rankPolynomialConst_eval (a : F) (A : Matrix p q F) :
    (rankPolynomialConst A).map (Polynomial.evalRingHom a) = A := by
  ext; simp [rankPolynomialConst]

def rankPolynomialResolvent [DecidableEq n] (A : Matrix n n F) : Matrix n n F[X] :=
  1 + (Polynomial.X : F[X]) • rankPolynomialConst A

@[simp] theorem rankPolynomialResolvent_eval_zero [DecidableEq n] (A : Matrix n n F) :
    (rankPolynomialResolvent A).map (Polynomial.evalRingHom 0) = 1 := by
  ext i j
  simp [rankPolynomialResolvent, rankPolynomialConst, Matrix.one_apply]
  split_ifs <;> simp

@[simp] theorem rankPolynomialAdjugate_eval_zero [Fintype n] [DecidableEq n]
    (A : Matrix n n F) :
    (rankPolynomialResolvent A).adjugate.map (Polynomial.evalRingHom 0) = 1 := by
  have h := (Polynomial.evalRingHom (0 : F)).map_adjugate (rankPolynomialResolvent A)
  change ((rankPolynomialResolvent A).adjugate.map (Polynomial.evalRingHom 0)) =
    ((rankPolynomialResolvent A).map (Polynomial.evalRingHom 0)).adjugate at h
  simpa only [rankPolynomialResolvent_eval_zero, Matrix.adjugate_one] using h

theorem rankPolynomialDet_eval_zero [Fintype n] [DecidableEq n]
    (A : Matrix n n F) : (rankPolynomialResolvent A).det.eval 0 = 1 := by
  have h := (Polynomial.evalRingHom (0 : F)).map_det (rankPolynomialResolvent A)
  change (rankPolynomialResolvent A).det.eval 0 =
    ((rankPolynomialResolvent A).map (Polynomial.evalRingHom 0)).det at h
  simpa only [rankPolynomialResolvent_eval_zero, Matrix.det_one] using h

variable [Fintype n] [DecidableEq n]

/-- A vanishing polynomial adjugate transfer forces every reachability moment to
vanish. The proof uses the exact adjugate identity and evaluation at zero, not
formal power series or an assumed minimal realization. -/
theorem all_moments_zero_of_adjugate_transfer_zero
    (A : Matrix n n F) (B : Matrix n q F) (C : Matrix p n F)
    (hzero : rankPolynomialConst C * (rankPolynomialResolvent A).adjugate *
      rankPolynomialConst B = 0) :
    ∀ j : ℕ, C * A ^ j * B = 0 := by
  let J := (rankPolynomialResolvent A).adjugate
  let f := (rankPolynomialResolvent A).det
  have hEval (j : ℕ)
      (h : rankPolynomialConst (C * A ^ j) * J * rankPolynomialConst B = 0) :
      C * A ^ j * B = 0 := by
    have hh := congrArg (fun M : Matrix p q F[X] => M.map (Polynomial.evalRingHom 0)) h
    simpa only [Matrix.map_mul, rankPolynomialConst_eval, J,
      rankPolynomialAdjugate_eval_zero, Matrix.mul_one, Matrix.map_zero _ (map_zero _)] using hh
  have hAll : ∀ j : ℕ,
      rankPolynomialConst (C * A ^ j) * J * rankPolynomialConst B = 0 := by
    intro j
    induction j with
    | zero => simpa [J] using hzero
    | succ j ih =>
      have hm := congrArg (fun M : Matrix n n F[X] =>
        rankPolynomialConst (C * A ^ j) * M * rankPolynomialConst B)
        (Matrix.mul_adjugate (rankPolynomialResolvent A))
      have hp : rankPolynomialConst (C * A ^ j) * rankPolynomialConst A =
          rankPolynomialConst (C * A ^ (j + 1)) := by
        rw [← rankPolynomialConst_mul, Matrix.mul_assoc, pow_succ]
      have hi := hEval j ih
      have heq : (Polynomial.X : F[X]) •
          (rankPolynomialConst (C * A ^ (j + 1)) * J * rankPolynomialConst B) = 0 := by
        change rankPolynomialConst (C * A ^ j) *
          ((1 + (Polynomial.X : F[X]) • rankPolynomialConst A) * J) * rankPolynomialConst B =
          rankPolynomialConst (C * A ^ j) * (f • 1) * rankPolynomialConst B at hm
        simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
          Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hp,
          ih, zero_add, Matrix.mul_one, ← rankPolynomialConst_mul, hi,
          rankPolynomialConst_zero, smul_zero] at hm
        exact hm
      apply Matrix.ext
      intro i l
      have hh := congrFun (congrFun heq i) l
      exact (mul_eq_zero.mp hh).resolve_left Polynomial.X_ne_zero
  exact fun j => hEval j (hAll j)

end Polynomial

section Normalized

variable {F n p q : Type*} [Field F]
  [Fintype n] [Fintype p] [Fintype q] [DecidableEq n]

def rankNormalizedPencil (A : Matrix n n F) (B : Matrix n q F)
    (C : Matrix p n F) (D : Matrix p q F) : Pencil F (n ⊕ p) (n ⊕ q) :=
  (fromBlocks 1 0 0 0, fromBlocks A B C D)

theorem rank_matrix_map_smul {R S m k : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (u : R) (A : Matrix m k R) :
    (u • A).map f = f u • A.map f := by
  apply Matrix.ext
  intro i j
  exact f.map_mul u (A i j)

omit [Fintype p] [Fintype q] in
@[simp] theorem rankPolynomialConst_rat_map (A : Matrix p q F) :
    (rankPolynomialConst A).map (algebraMap F[X] (RatFunc F)) = Pencil.const A := by
  apply Matrix.ext
  intro i j
  rfl

omit [Fintype n] in
theorem rankPolynomialResolvent_rat_map (A : Matrix n n F) :
    (rankPolynomialResolvent A).map (algebraMap F[X] (RatFunc F)) =
      (1 : Matrix n n (RatFunc F)) + (RatFunc.X : RatFunc F) • Pencil.const A := by
  apply Matrix.ext
  intro i j
  simp [rankPolynomialResolvent, rankPolynomialConst, Pencil.const, Matrix.one_apply]
  exact mul_comm _ _

omit [Fintype n] [Fintype p] [Fintype q] in
theorem generic_rankNormalizedPencil (A : Matrix n n F) (B : Matrix n q F)
    (C : Matrix p n F) (D : Matrix p q F) :
    (rankNormalizedPencil A B C D).generic =
      fromBlocks (1 + (RatFunc.X : RatFunc F) • Pencil.const A)
        ((RatFunc.X : RatFunc F) • Pencil.const B)
        ((RatFunc.X : RatFunc F) • Pencil.const C)
        ((RatFunc.X : RatFunc F) • Pencil.const D) := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [rankNormalizedPencil, Pencil.generic, Pencil.const, Matrix.fromBlocks,
      Matrix.one_apply]

omit [Fintype p] in
/-- The actual normal-rank bound on a normalized pencil forces the zero lower
coefficient and all reachability moments. No Kronecker form or moment hypothesis
is assumed. -/
theorem normalized_pencil_all_moments
    (A : Matrix n n F) (B : Matrix n q F) (C : Matrix p n F) (D : Matrix p q F)
    (hRank : (rankNormalizedPencil A B C D).normalRank ≤ Fintype.card n) :
    D = 0 ∧ ∀ j : ℕ, C * A ^ j * B = 0 := by
  let G := rankPolynomialResolvent A
  let J := G.adjugate
  let f := G.det
  let qF := algebraMap F[X] (RatFunc F)
  let g := G.map qF
  let j := J.map qF
  let s : RatFunc F := RatFunc.X
  have hf0 : f.eval 0 = 1 := rankPolynomialDet_eval_zero A
  have hf : qF f ≠ 0 := by
    intro hz
    have hz' : f = 0 := RatFunc.algebraMap_injective F (by simpa only [map_zero] using hz)
    have hh := congrArg (Polynomial.eval 0) hz'
    rw [hf0] at hh
    simp at hh
  have hgJ : g * j = qF f • (1 : Matrix n n (RatFunc F)) := by
    have hh := congrArg (fun M : Matrix n n F[X] => M.map qF) (Matrix.mul_adjugate G)
    simpa only [Matrix.map_mul, rank_matrix_map_smul,
      Matrix.map_one _ (map_zero _) (map_one _)] using hh
  have hJg : j * g = qF f • (1 : Matrix n n (RatFunc F)) := by
    have hh := congrArg (fun M : Matrix n n F[X] => M.map qF) (Matrix.adjugate_mul G)
    simpa only [Matrix.map_mul, rank_matrix_map_smul,
      Matrix.map_one _ (map_zero _) (map_one _)] using hh
  let gi : Matrix n n (RatFunc F) := (qF f)⁻¹ • j
  have hg1 : g * gi = 1 := by
    simp only [gi, Matrix.mul_smul, hgJ, smul_smul, inv_mul_cancel₀ hf, one_smul]
  have hg2 : gi * g = 1 := by
    simp only [gi, Matrix.smul_mul, hJg, smul_smul, inv_mul_cancel₀ hf, one_smul]
  have hfull : (fromBlocks g (s • Pencil.const B) (s • Pencil.const C)
      (s • Pencil.const D)).rank ≤ Fintype.card n := by
    change (rankNormalizedPencil A B C D).generic.rank ≤ Fintype.card n at hRank
    simpa only [generic_rankNormalizedPencil, g, G, qF,
      rankPolynomialResolvent_rat_map, s] using hRank
  have hd := block_schur_eq_of_rank_le g gi (s • Pencil.const B)
    (s • Pencil.const C) (s • Pencil.const D) hg2 hg1 hfull
  have hs : s ≠ 0 := RatFunc.X_ne_zero
  have htransfer : qF f • Pencil.const D =
      s • (Pencil.const C * j * Pencil.const B) := by
    have hh := congrArg (fun M : Matrix p q (RatFunc F) => (qF f / s) • M) hd
    simp only [gi, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at hh
    have hleft : qF f / s * s = qF f := div_mul_cancel₀ _ hs
    have hright : qF f / s * (s * ((qF f)⁻¹ * s)) = s := by
      field_simp
    simpa only [hleft, hright] using hh
  have hp : f • rankPolynomialConst D =
      (Polynomial.X : F[X]) • (rankPolynomialConst C * J * rankPolynomialConst B) := by
    have hh : (f • rankPolynomialConst D).map qF =
        ((Polynomial.X : F[X]) •
          (rankPolynomialConst C * J * rankPolynomialConst B)).map qF := by
      simpa only [rank_matrix_map_smul, Matrix.map_mul, qF,
        rankPolynomialConst_rat_map, RatFunc.algebraMap_X, j, s] using htransfer
    apply Matrix.ext
    intro i l
    exact RatFunc.algebraMap_injective F (congrFun (congrFun hh i) l)
  have hD : D = 0 := by
    have hh := congrArg (fun M : Matrix p q F[X] => M.map (Polynomial.evalRingHom 0)) hp
    rw [rank_matrix_map_smul, rank_matrix_map_smul] at hh
    rw [rankPolynomialConst_eval] at hh
    simpa only [Polynomial.coe_evalRingHom, hf0,
      Polynomial.eval_X, zero_smul, one_smul] using hh
  have hCB : rankPolynomialConst C * J * rankPolynomialConst B = 0 := by
    rw [hD, rankPolynomialConst_zero, smul_zero] at hp
    apply Matrix.ext
    intro i l
    have hh := congrFun (congrFun hp.symm i) l
    exact (mul_eq_zero.mp hh).resolve_left Polynomial.X_ne_zero
  exact ⟨hD, all_moments_zero_of_adjugate_transfer_zero A B C hCB⟩

end Normalized

end MatCP1Converse
