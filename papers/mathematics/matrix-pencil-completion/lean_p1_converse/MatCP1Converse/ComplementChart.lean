module

public import MatCP1Converse.PivotCompression
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

namespace MatCP1Converse

open Matrix

section Definition

variable {F r s a b : Type*} [Field F]
  [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

/-- The actual two coefficient matrices of the kernel/quotient complementary
pencil `Q diag(z I, I) K`. The kernel and quotient conditions are stated in the
theorems using this definition, not built in as substitute axioms. -/
def complementPencil (Q : Matrix a (r ⊕ s) F) (K : Matrix (r ⊕ s) b F) :
    Pencil F a b :=
  (Q * fromBlocks (0 : Matrix r r F) 0 0 (1 : Matrix s s F) * K,
   Q * fromBlocks (1 : Matrix r r F) 0 0 (0 : Matrix s s F) * K)

end Definition

section Chart

variable {F n p m a b : Type*} [Field F]
  [Fintype n] [Fintype p] [Fintype m] [Fintype a] [Fintype b]
  [DecidableEq n] [DecidableEq p] [DecidableEq m]

/-- Joint image map of the rank factorizations of `diag(I,0)` and the
completed pivot-chart coefficient. -/
def complementChartS (G : Matrix n n F) (C : Matrix p n F) :
    Matrix (n ⊕ p) (n ⊕ n) F :=
  fromBlocks 1 G 0 C

/-- Joint coimage map of the same rank factorizations. -/
def complementChartT (Gi : Matrix n n F) (B : Matrix n m F) :
    Matrix (n ⊕ n) (n ⊕ m) F :=
  fromBlocks 1 0 1 (Gi * B)

def complementChartK (Gi : Matrix n n F) (K : Matrix n b F) :
    Matrix (n ⊕ n) b F := fromRows (-K) (Gi * K)

def complementChartQ (Q : Matrix a n F) : Matrix a (n ⊕ n) F :=
  fromCols (-Q) Q

omit [Fintype p] [Fintype m] [DecidableEq p] [DecidableEq m] in
theorem complement_chart_factorization
    (G Gi : Matrix n n F) (B : Matrix n m F) (C : Matrix p n F)
    (hG : G * Gi = 1) :
    fromRows (1 : Matrix n n F) (0 : Matrix p n F) *
        fromCols (1 : Matrix n n F) (0 : Matrix n m F) =
      fromBlocks (1 : Matrix n n F) 0 0 (0 : Matrix p m F) ∧
    fromRows G C * fromCols (1 : Matrix n n F) (Gi * B) =
      completedBlock G Gi B C := by
  constructor
  · rw [fromRows_mul_fromCols]
    simp
  · rw [fromRows_mul_fromCols]
    simp [completedBlock, ← Matrix.mul_assoc, hG]

omit [Fintype p] [DecidableEq p] in
theorem complement_chartS_surjective
    (G : Matrix n n F) (C : Matrix p n F)
    (hC : Function.Surjective C.mulVec) :
    Function.Surjective (complementChartS G C).mulVec := by
  intro w
  obtain ⟨v, hv⟩ := hC (w ∘ Sum.inr)
  refine ⟨Sum.elim ((w ∘ Sum.inl) - G *ᵥ v) v, ?_⟩
  ext i
  cases i <;> simp [complementChartS, fromBlocks_mulVec, Function.comp_def, hv]

omit [DecidableEq m] in
theorem complement_chartT_injective
    (G Gi : Matrix n n F) (B : Matrix n m F)
    (hG : G * Gi = 1) (hB : Function.Injective B.mulVec) :
    Function.Injective (complementChartT Gi B).mulVec := by
  intro v w h
  have htop : v ∘ Sum.inl = w ∘ Sum.inl := by
    have hh := congrArg (fun x : n ⊕ n → F => x ∘ Sum.inl) h
    simpa [complementChartT, fromBlocks_mulVec] using hh
  have hbot : (Gi * B) *ᵥ (v ∘ Sum.inr) = (Gi * B) *ᵥ (w ∘ Sum.inr) := by
    have hh := congrArg (fun x : n ⊕ n → F => x ∘ Sum.inr) h
    simpa [complementChartT, fromBlocks_mulVec, htop] using hh
  have hlast : v ∘ Sum.inr = w ∘ Sum.inr := by
    apply hB
    have hh := congrArg (fun x => G *ᵥ x) hbot
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hG, Matrix.one_mul] using hh
  funext i
  cases i with
  | inl i => exact congrFun htop i
  | inr i => exact congrFun hlast i

omit [Fintype a] [DecidableEq n] in
theorem complement_chartQ_surjective
    (Q : Matrix a n F) (hQ : Function.Surjective Q.mulVec) :
    Function.Surjective (complementChartQ Q).mulVec := by
  intro w
  obtain ⟨v, hv⟩ := hQ w
  refine ⟨Sum.elim 0 v, ?_⟩
  simpa [complementChartQ, fromCols_mulVec] using hv

omit [DecidableEq n] in
theorem complement_chartK_injective
    (Gi : Matrix n n F) (K : Matrix n b F) (hK : Function.Injective K.mulVec) :
    Function.Injective (complementChartK Gi K).mulVec := by
  intro v w h
  apply hK
  have hh := congrArg (fun x : n ⊕ n → F => x ∘ Sum.inl) h
  simpa [complementChartK, fromRows_mulVec, Matrix.neg_mulVec] using hh

omit [Fintype p] [DecidableEq p] in
theorem complement_chartK_range
    (G Gi : Matrix n n F) (C : Matrix p n F) (K : Matrix n b F)
    (hGiG : Gi * G = 1) (hGGi : G * Gi = 1)
    (hK : LinearMap.range K.mulVecLin = LinearMap.ker (C * Gi).mulVecLin) :
    LinearMap.range (complementChartK Gi K).mulVecLin =
      LinearMap.ker (complementChartS G C).mulVecLin := by
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    have hv : (C * Gi) *ᵥ (K *ᵥ v) = 0 := by
      have hm := LinearMap.mem_range_self K.mulVecLin v
      rw [hK] at hm
      exact hm
    change (complementChartS G C) *ᵥ ((complementChartK Gi K) *ᵥ v) = 0
    have hv' : (C * Gi * K) *ᵥ v = 0 := by
      simpa only [Matrix.mulVec_mulVec] using hv
    ext i
    cases i with
    | inl i =>
      simp [complementChartS, complementChartK, fromBlocks_mulVec, fromRows_mulVec,
        Matrix.neg_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hGGi]
    | inr i =>
      simpa [complementChartS, complementChartK, fromBlocks_mulVec, fromRows_mulVec,
        Matrix.mulVec_mulVec, ← Matrix.mul_assoc] using congrFun hv' i
  · intro w hw
    have htop : w ∘ Sum.inl + G *ᵥ (w ∘ Sum.inr) = 0 := by
      have hh := congrArg (fun x : n ⊕ p → F => x ∘ Sum.inl)
        (show (complementChartS G C) *ᵥ w = 0 from hw)
      simpa [complementChartS, fromBlocks_mulVec] using hh
    have hbot : C *ᵥ (w ∘ Sum.inr) = 0 := by
      have hh := congrArg (fun x : n ⊕ p → F => x ∘ Sum.inr)
        (show (complementChartS G C) *ᵥ w = 0 from hw)
      simpa [complementChartS, fromBlocks_mulVec] using hh
    have hm : G *ᵥ (w ∘ Sum.inr) ∈ LinearMap.range K.mulVecLin := by
      rw [hK]
      change (C * Gi) *ᵥ (G *ᵥ (w ∘ Sum.inr)) = 0
      simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hGiG, Matrix.mul_one] using hbot
    obtain ⟨v, hv⟩ := hm
    change K *ᵥ v = G *ᵥ (w ∘ Sum.inr) at hv
    refine ⟨v, ?_⟩
    change (complementChartK Gi K) *ᵥ v = w
    have ht : -(G *ᵥ (w ∘ Sum.inr)) = w ∘ Sum.inl :=
      (eq_neg_of_add_eq_zero_left htop).symm
    ext i
    cases i with
    | inl i =>
      simpa [complementChartK, fromRows_mulVec, Matrix.neg_mulVec, hv] using congrFun ht i
    | inr i =>
      have hh : (Gi * K) *ᵥ v = w ∘ Sum.inr := by
        rw [← Matrix.mulVec_mulVec, show K *ᵥ v = G *ᵥ (w ∘ Sum.inr) from hv,
          Matrix.mulVec_mulVec, hGiG, Matrix.one_mulVec]
      simpa [complementChartK, fromRows_mulVec] using congrFun hh i

omit [Fintype a] [DecidableEq m] in
theorem complement_chartQ_kernel
    (Gi : Matrix n n F) (B : Matrix n m F) (Q : Matrix a n F)
    (hQ : LinearMap.ker Q.mulVecLin = LinearMap.range (Gi * B).mulVecLin) :
    LinearMap.ker (complementChartQ Q).mulVecLin =
      LinearMap.range (complementChartT Gi B).mulVecLin := by
  apply le_antisymm
  · intro w hw
    have hh : Q *ᵥ ((w ∘ Sum.inr) - (w ∘ Sum.inl)) = 0 := by
      have hz : (complementChartQ Q) *ᵥ w = 0 := hw
      simpa [complementChartQ, fromCols_mulVec, Matrix.neg_mulVec,
        Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_neg,
        sub_eq_add_neg, add_comm] using hz
    have hm : (w ∘ Sum.inr) - (w ∘ Sum.inl) ∈
        LinearMap.range (Gi * B).mulVecLin := by
      rw [← hQ]
      exact hh
    obtain ⟨v, hv⟩ := hm
    change (Gi * B) *ᵥ v = (w ∘ Sum.inr) - (w ∘ Sum.inl) at hv
    refine ⟨Sum.elim (w ∘ Sum.inl) v, ?_⟩
    change (complementChartT Gi B) *ᵥ Sum.elim (w ∘ Sum.inl) v = w
    ext i
    cases i <;> simp [complementChartT, fromBlocks_mulVec, hv]
  · rintro w ⟨v, rfl⟩
    have hm := LinearMap.mem_range_self (Gi * B).mulVecLin (v ∘ Sum.inr)
    rw [← hQ] at hm
    have hh : Q *ᵥ ((Gi * B) *ᵥ (v ∘ Sum.inr)) = 0 := hm
    change (complementChartQ Q) *ᵥ ((complementChartT Gi B) *ᵥ v) = 0
    simp [complementChartQ, complementChartT, fromCols_mulVec, fromBlocks_mulVec,
      Matrix.neg_mulVec, Matrix.mulVec_add, hh]

omit [Fintype a] [Fintype b] in
/-- Exact identification of both intrinsic-complement coefficients with the
static compression in the common invertible pivot chart. -/
theorem complement_chart_coefficients
    (Gi : Matrix n n F) (Q : Matrix a n F) (K : Matrix n b F) :
    complementPencil (complementChartQ Q) (complementChartK Gi K) =
      (Q * Gi * K, Q * K) := by
  apply Prod.ext <;>
    simp [complementPencil, complementChartQ, complementChartK,
      fromCols_mul_fromBlocks, fromCols_mul_fromRows, Matrix.mul_assoc]

end Chart

end MatCP1Converse
