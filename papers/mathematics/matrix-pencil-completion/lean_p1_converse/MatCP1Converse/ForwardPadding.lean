module

public import MatCP1Converse.ForwardDilationMatrix
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

noncomputable section

namespace MatCP1Converse

open Matrix

section Compression

variable {F I m n p q u v : Type*} [Field F]
  [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype u] [Fintype v]

omit [Fintype m] in
/-- Constant full-rank simultaneous compression is transitive. -/
theorem matrixJointCompression_trans
    {A : I → Matrix m n F} {B : I → Matrix p q F} {C : I → Matrix u v F}
    (hAB : MatCP1.MatrixJointCompression A B)
    (hBC : MatCP1.MatrixJointCompression B C) :
    MatCP1.MatrixJointCompression A C := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := hAB
  obtain ⟨R, S, hR, hS, hRS⟩ := hBC
  refine ⟨P * R, S * Q, ?_, ?_, ?_⟩
  · simpa only [Matrix.mulVec_mulVec, Function.comp_def] using hP.comp hR
  · simpa only [Matrix.mulVec_mulVec, Function.comp_def] using hS.comp hQ
  · intro i
    calc
      (P * R) * C i * (S * Q) = P * (R * C i * S) * Q := by
        simp only [Matrix.mul_assoc]
      _ = A i := by rw [hRS, hPQ]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-- Selecting any injective sets of row and column coordinates is an actual
full-row/full-column compression, even when some index types are empty. -/
theorem matrixJointCompression_submatrix (B : I → Matrix p q F)
    (f : m → p) (g : n → q) (hf : Function.Injective f) (hg : Function.Injective g) :
    MatCP1.MatrixJointCompression (fun i => (B i).submatrix f g) B := by
  let P : Matrix m p F := (1 : Matrix p p F).submatrix f id
  let Pi : Matrix p m F := (1 : Matrix p p F).submatrix id f
  let Q : Matrix q n F := (1 : Matrix q q F).submatrix id g
  let Qi : Matrix n q F := (1 : Matrix q q F).submatrix g id
  have hP : P * Pi = 1 := by
    rw [show P * Pi = (1 : Matrix p p F).submatrix f f by
      simpa only [P, Pi, Equiv.coe_refl, Equiv.refl_symm, Function.id_comp,
        Matrix.submatrix_submatrix, Function.comp_id] using
        Matrix.one_submatrix_mul f (Equiv.refl p) Pi]
    exact Matrix.submatrix_one f hf
  have hQ : Qi * Q = 1 := by
    rw [show Qi * Q = (1 : Matrix q q F).submatrix g g by
      simpa only [Q, Qi, Equiv.coe_refl, Equiv.refl_symm, Function.id_comp,
        Matrix.submatrix_submatrix, Function.comp_id] using
        Matrix.one_submatrix_mul g (Equiv.refl q) Q]
    exact Matrix.submatrix_one g hg
  refine ⟨P, Q, ?_, ?_, ?_⟩
  · intro z
    refine ⟨Pi.mulVec z, ?_⟩
    rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
  · intro z w h
    have hh := congrArg Qi.mulVec h
    simpa only [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec] using hh
  · intro i
    change ((1 : Matrix p p F).submatrix f (Equiv.refl p)) * B i *
      ((1 : Matrix q q F).submatrix (Equiv.refl q) g) = _
    rw [Matrix.one_submatrix_mul, Matrix.mul_submatrix_one]
    rfl

end Compression

section Padding

variable {F m n a b x : Type*} [Field F]
  [Fintype m] [Fintype n] [Fintype a] [Fintype b] [Fintype x]
  [DecidableEq m] [DecidableEq n] [DecidableEq a] [DecidableEq b] [DecidableEq x]

/-- Two scalar summands at the same anchor can be combined and padded to any
prescribed larger size by constant coordinate embeddings. -/
theorem matrix_scalar_sum_padding (A : Bool → Matrix m n F) (d : F)
    (hcard : Fintype.card a + Fintype.card b ≤ Fintype.card x) :
    MatCP1.MatrixJointCompression
      (fun i => fromBlocks (fromBlocks (A i) 0 0
        (scalarMatrixDilationFamily (a := a) d i)) 0 0
        (scalarMatrixDilationFamily (a := b) d i))
      (fun i => fromBlocks (A i) 0 0
        (scalarMatrixDilationFamily (a := x) d i)) := by
  classical
  have hc : Fintype.card (a ⊕ b) ≤ Fintype.card x := by simpa using hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  let f : ((m ⊕ a) ⊕ b) → m ⊕ x :=
    fun z => match z with
    | .inl (.inl i) => .inl i
    | .inl (.inr j) => .inr (e (.inl j))
    | .inr k => .inr (e (.inr k))
  let g : ((n ⊕ a) ⊕ b) → n ⊕ x :=
    fun z => match z with
    | .inl (.inl i) => .inl i
    | .inl (.inr j) => .inr (e (.inl j))
    | .inr k => .inr (e (.inr k))
  have hf : Function.Injective f := by
    intro z w h
    rcases z with (i | j) | k <;> rcases w with (i' | j') | k' <;>
      simp only [f, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
        Sum.inr_ne_inl, e.injective.eq_iff] at h ⊢ <;> exact h
  have hg : Function.Injective g := by
    intro z w h
    rcases z with (i | j) | k <;> rcases w with (i' | j') | k' <;>
      simp only [g, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
        Sum.inr_ne_inl, e.injective.eq_iff] at h ⊢ <;> exact h
  have hh := matrixJointCompression_submatrix
    (fun i => fromBlocks (A i) 0 0 (scalarMatrixDilationFamily (a := x) d i)) f g hf hg
  convert hh using 1
  funext i z w
  rcases z with (j | k) | l <;> rcases w with (j' | k') | l' <;>
    cases i <;>
    simp [f, g, scalarMatrixDilationFamily, Matrix.one_apply, e.injective.eq_iff]

end Padding

end MatCP1Converse
