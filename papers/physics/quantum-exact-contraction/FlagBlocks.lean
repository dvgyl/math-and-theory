import TraceNormBounds

/-!
# Orthogonal block sums for the spectral trace norm

All norms in this file are `CMICounterexample.traceNorm`, defined from the actual
Hermitian eigenvalues.  The proof of additivity uses the already established
spectral positive/negative decomposition for its upper bound and spectral dual
certificates for its lower bound.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace CMICounterexample

noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The orthogonal direct sum of two square matrices. -/
def blockSum (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ := Matrix.fromBlocks A 0 0 B

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem blockSum_hermitian [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (blockSum A B).IsHermitian :=
  hA.fromBlocks (by simp) hB

theorem blockSum_posSemidef (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (blockSum A B).PosSemidef := by
  refine ⟨blockSum_hermitian A B hA.1 hB.1, ?_⟩
  intro x
  have h := add_nonneg (hA.2 (x ∘ Sum.inl)) (hB.2 (x ∘ Sum.inr))
  simpa only [blockSum, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec,
    add_zero, zero_add, dotProduct, Fintype.sum_sum_type,
    Pi.star_apply, Function.comp_apply, Sum.elim_inl, Sum.elim_inr] using h

omit [DecidableEq m] [DecidableEq n] in
theorem blockSum_trace [DecidableEq m] [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    (blockSum A B).trace = A.trace + B.trace := by
  simp [blockSum, Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.fromBlocks]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem blockSum_add [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A C : Matrix m m ℂ) (B D : Matrix n n ℂ) :
    blockSum A B + blockSum C D = blockSum (A + C) (B + D) := by
  simp only [blockSum, Matrix.fromBlocks_add, add_zero]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem blockSum_neg [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    -blockSum A B = blockSum (-A) (-B) := by
  simp only [blockSum, Matrix.fromBlocks_neg, neg_zero]

theorem blockSum_sub (A C : Matrix m m ℂ) (B D : Matrix n n ℂ) :
    blockSum A B - blockSum C D = blockSum (A - C) (B - D) := by
  simp only [sub_eq_add_neg, blockSum_neg, blockSum_add]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem blockSum_smul [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix n n ℂ) (c : ℝ) :
    c • blockSum A B = blockSum (c • A) (c • B) := by
  simp only [blockSum, Matrix.fromBlocks_smul, smul_zero]

omit [Fintype m] [Fintype n] in
theorem blockSum_one [Fintype m] [Fintype n] : blockSum (1 : Matrix m m ℂ) (1 : Matrix n n ℂ) = 1 :=
  Matrix.fromBlocks_one

theorem blockSum_one_sub (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    1 - blockSum A B = blockSum (1 - A) (1 - B) := by
  calc
    1 - blockSum A B = blockSum 1 1 - blockSum A B := by rw [blockSum_one]
    _ = blockSum (1 - A) (1 - B) := blockSum_sub _ _ _ _

theorem blockSum_one_add (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    1 + blockSum A B = blockSum (1 + A) (1 + B) := by
  calc
    1 + blockSum A B = blockSum 1 1 + blockSum A B := by rw [blockSum_one]
    _ = blockSum (1 + A) (1 + B) := blockSum_add _ _ _ _

omit [DecidableEq m] [DecidableEq n] in
theorem blockSum_mul [DecidableEq m] [DecidableEq n] (A C : Matrix m m ℂ) (B D : Matrix n n ℂ) :
    blockSum A B * blockSum C D = blockSum (A * C) (B * D) := by
  simp only [blockSum, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]

/-- The actual spectral trace norm is additive on orthogonal blocks. -/
theorem traceNorm_blockSum (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceNorm (blockSum A B) (blockSum_hermitian A B hA hB) =
      traceNorm A hA + traceNorm B hB := by
  apply le_antisymm
  · obtain ⟨PA, QA, hPA, hQA, hAeq, hAcost⟩ := exists_posSemidef_decomposition A hA
    obtain ⟨PB, QB, hPB, hQB, hBeq, hBcost⟩ := exists_posSemidef_decomposition B hB
    have hdiff : blockSum A B = blockSum PA PB - blockSum QA QB := by
      rw [blockSum_sub, ← hAeq, ← hBeq]
    have h := traceNorm_sub_le_of_posSemidef (blockSum PA PB) (blockSum QA QB)
      (blockSum_posSemidef PA PB hPA hPB) (blockSum_posSemidef QA QB hQA hQB)
    simp only [← hdiff, blockSum_trace, Complex.add_re] at h
    linarith
  · obtain ⟨TA, hTA, hmA, hpA, heqA⟩ := exists_traceNorm_dual A hA
    obtain ⟨TB, hTB, hmB, hpB, heqB⟩ := exists_traceNorm_dual B hB
    have hm : (1 - blockSum TA TB).PosSemidef := by
      rw [blockSum_one_sub]
      exact blockSum_posSemidef _ _ hmA hmB
    have hp : (1 + blockSum TA TB).PosSemidef := by
      rw [blockSum_one_add]
      exact blockSum_posSemidef _ _ hpA hpB
    have h := trace_mul_le_traceNorm (blockSum A B)
      (blockSum_hermitian A B hA hB) (blockSum TA TB) hm hp
    simpa only [blockSum_mul, blockSum_trace, Complex.add_re, heqA, heqB] using h

/-- A positive orthogonal flag contributes exactly its trace to the norm. -/
theorem traceNorm_blockSum_posSemidef (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.PosSemidef) :
    traceNorm (blockSum A B) (blockSum_hermitian A B hA hB.1) =
      traceNorm A hA + B.trace.re := by
  rw [traceNorm_blockSum, traceNorm_eq_trace_of_posSemidef B hB]

/-- A negative positive-semidefinite flag contributes the same trace. -/
theorem traceNorm_blockSum_neg_posSemidef (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.PosSemidef) :
    traceNorm (blockSum A (-B)) (blockSum_hermitian A (-B) hA hB.1.neg) =
      traceNorm A hA + B.trace.re := by
  rw [traceNorm_blockSum, traceNorm_neg B hB.1, traceNorm_eq_trace_of_posSemidef B hB]

omit [DecidableEq m] [DecidableEq n] in
/-- Relabelling a finite orthonormal basis preserves the trace. -/
theorem trace_submatrix_equiv [DecidableEq m] [DecidableEq n] (A : Matrix n n ℂ) (e : m ≃ n) :
    (A.submatrix e e).trace = A.trace := by
  change (∑ i, A (e i) (e i)) = ∑ i, A i i
  exact e.sum_comp (fun i => A i i)

/-- Relabelling a finite orthonormal basis preserves the actual spectral trace norm. -/
theorem traceNorm_submatrix_equiv (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (e : m ≃ n) :
    traceNorm (A.submatrix e e) (hA.submatrix e) = traceNorm A hA := by
  apply le_antisymm
  · exact traceNorm_map_le (fun M => M.submatrix e e)
      (fun _ _ => rfl) (fun _ hM => hM.submatrix e)
      (fun M => trace_submatrix_equiv M e) A hA (hA.submatrix e)
  · have h := traceNorm_map_le (fun M : Matrix m m ℂ => M.submatrix e.symm e.symm)
      (fun _ _ => rfl) (fun _ hM => hM.submatrix e.symm)
      (fun M => trace_submatrix_equiv M e.symm)
      (A.submatrix e e) (hA.submatrix e) ((hA.submatrix e).submatrix e.symm)
    simpa using h

variable {R A : Type*} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]

/-- Partial trace over the second tensor factor, written in matrix coordinates. -/
def partialTraceMatrix (X : Matrix (R × A) (R × A) ℂ) : Matrix R R ℂ :=
  fun r s => ∑ a, X (r, a) (s, a)

omit [Fintype R] [DecidableEq R] [DecidableEq A] in
theorem partialTraceMatrix_hermitian [Fintype R] [DecidableEq R] [DecidableEq A] (X : Matrix (R × A) (R × A) ℂ)
    (hX : X.IsHermitian) : (partialTraceMatrix X).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro r s
  simp only [partialTraceMatrix, star_sum, hX.apply]

omit [DecidableEq R] in
theorem partialTraceMatrix_posSemidef [DecidableEq R] (X : Matrix (R × A) (R × A) ℂ)
    (hX : X.PosSemidef) : (partialTraceMatrix X).PosSemidef := by
  have hsum : ∀ s : Finset A,
      (∑ a ∈ s, X.submatrix (fun r => (r, a)) (fun r => (r, a))).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact Matrix.PosSemidef.zero
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact (hX.submatrix (fun r => (r, a))).add ih
  have heq : partialTraceMatrix X =
      ∑ a, X.submatrix (fun r => (r, a)) (fun r => (r, a)) := by
    ext r s
    simp only [partialTraceMatrix, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [heq]
  exact hsum Finset.univ

omit [DecidableEq R] [DecidableEq A] in
theorem partialTraceMatrix_trace [DecidableEq R] [DecidableEq A] (X : Matrix (R × A) (R × A) ℂ) :
    (partialTraceMatrix X).trace = X.trace := by
  simp only [partialTraceMatrix, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

omit [Fintype R] [DecidableEq R] [DecidableEq A] in
theorem partialTraceMatrix_add [Fintype R] [DecidableEq R] [DecidableEq A] (X Y : Matrix (R × A) (R × A) ℂ) :
    partialTraceMatrix (X + Y) = partialTraceMatrix X + partialTraceMatrix Y := by
  ext r s
  simp only [partialTraceMatrix, Matrix.add_apply, Finset.sum_add_distrib]

omit [Fintype R] [DecidableEq R] [DecidableEq A] in
theorem partialTraceMatrix_sub [Fintype R] [DecidableEq R] [DecidableEq A] (X Y : Matrix (R × A) (R × A) ℂ) :
    partialTraceMatrix (X - Y) = partialTraceMatrix X - partialTraceMatrix Y := by
  ext r s
  simp only [partialTraceMatrix, Matrix.sub_apply, Finset.sum_sub_distrib]

omit [Fintype R] [DecidableEq R] [DecidableEq A] in
theorem partialTraceMatrix_smul [Fintype R] [DecidableEq R] [DecidableEq A] (X : Matrix (R × A) (R × A) ℂ) (c : ℝ) :
    partialTraceMatrix (c • X) = c • partialTraceMatrix X := by
  ext r s
  simp only [partialTraceMatrix, Matrix.smul_apply, Finset.smul_sum]

/-- Moving the added reference flag past the input tensor factor. -/
def referenceFlagEquiv (R A : Type*) : ((R ⊕ Unit) × A) ≃ ((R × A) ⊕ A) where
  toFun x := match x with
    | (Sum.inl r, a) => Sum.inl (r, a)
    | (Sum.inr _, a) => Sum.inr a
  invFun x := match x with
    | Sum.inl (r, a) => (Sum.inl r, a)
    | Sum.inr a => (Sum.inr (), a)
  left_inv := by
    rintro ⟨r, a⟩
    rcases r with r | u
    · rfl
    · cases u
      rfl
  right_inv := by
    intro x
    rcases x with ⟨r, a⟩ | a <;> rfl

/-- Append a block carried by one new, orthogonal reference value. -/
def flagMatrix (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ) :
    Matrix ((R ⊕ Unit) × A) ((R ⊕ Unit) × A) ℂ :=
  (blockSum X W).submatrix (referenceFlagEquiv R A) (referenceFlagEquiv R A)

omit [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] in
@[simp] theorem flagMatrix_inl_inl [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ)
    (r s : R) (a b : A) :
    flagMatrix X W (Sum.inl r, a) (Sum.inl s, b) = X (r, a) (s, b) := rfl

omit [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] in
@[simp] theorem flagMatrix_inl_inr [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ)
    (r : R) (u : Unit) (a b : A) :
    flagMatrix X W (Sum.inl r, a) (Sum.inr u, b) = 0 := rfl

omit [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] in
@[simp] theorem flagMatrix_inr_inl [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ)
    (u : Unit) (r : R) (a b : A) :
    flagMatrix X W (Sum.inr u, a) (Sum.inl r, b) = 0 := rfl

omit [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] in
@[simp] theorem flagMatrix_inr_inr [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ)
    (u v : Unit) (a b : A) :
    flagMatrix X W (Sum.inr u, a) (Sum.inr v, b) = W a b := rfl

theorem flagMatrix_hermitian (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ)
    (hX : X.IsHermitian) (hW : W.IsHermitian) : (flagMatrix X W).IsHermitian :=
  (blockSum_hermitian X W hX hW).submatrix (referenceFlagEquiv R A)

theorem flagMatrix_posSemidef (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ)
    (hX : X.PosSemidef) (hW : W.PosSemidef) : (flagMatrix X W).PosSemidef :=
  (blockSum_posSemidef X W hX hW).submatrix (referenceFlagEquiv R A)

theorem flagMatrix_trace (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ) :
    (flagMatrix X W).trace = X.trace + W.trace := by
  rw [flagMatrix, trace_submatrix_equiv, blockSum_trace]

theorem flagMatrix_add (X Y : Matrix (R × A) (R × A) ℂ) (W V : Matrix A A ℂ) :
    flagMatrix X W + flagMatrix Y V = flagMatrix (X + Y) (W + V) := by
  change (blockSum X W + blockSum Y V).submatrix
    (referenceFlagEquiv R A) (referenceFlagEquiv R A) = _
  rw [blockSum_add]
  rfl

theorem flagMatrix_sub (X Y : Matrix (R × A) (R × A) ℂ) (W V : Matrix A A ℂ) :
    flagMatrix X W - flagMatrix Y V = flagMatrix (X - Y) (W - V) := by
  change (blockSum X W - blockSum Y V).submatrix
    (referenceFlagEquiv R A) (referenceFlagEquiv R A) = _
  rw [blockSum_sub]
  rfl

theorem flagMatrix_smul (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ) (c : ℝ) :
    c • flagMatrix X W = flagMatrix (c • X) (c • W) := by
  change (c • blockSum X W).submatrix (referenceFlagEquiv R A)
    (referenceFlagEquiv R A) = _
  rw [blockSum_smul]
  rfl

theorem traceNorm_flagMatrix (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ)
    (hX : X.IsHermitian) (hW : W.IsHermitian) :
    traceNorm (flagMatrix X W) (flagMatrix_hermitian X W hX hW) =
      traceNorm X hX + traceNorm W hW := by
  exact (traceNorm_submatrix_equiv (blockSum X W) (blockSum_hermitian X W hX hW)
    (referenceFlagEquiv R A)).trans (traceNorm_blockSum X W hX hW)

/-- The one-dimensional matrix with the given scalar entry. -/
def scalarFlag (z : ℂ) : Matrix Unit Unit ℂ := fun _ _ => z

theorem scalarFlag_trace (z : ℂ) : (scalarFlag z).trace = z := by
  simp [scalarFlag, Matrix.trace, Matrix.diag]

theorem scalarFlag_neg (z : ℂ) : scalarFlag (-z) = -scalarFlag z := rfl

theorem scalarFlag_posSemidef (z : ℂ) (hz : 0 ≤ z) : (scalarFlag z).PosSemidef := by
  have heq : scalarFlag z = Matrix.diagonal (fun _ : Unit => z) := by
    ext i j
    cases i
    cases j
    simp [scalarFlag]
  rw [heq]
  exact Matrix.PosSemidef.diagonal (fun _ => hz)

theorem trace_nonneg_of_posSemidef (W : Matrix A A ℂ) (hW : W.PosSemidef) :
    0 ≤ W.trace := by
  unfold Matrix.trace
  apply Finset.sum_nonneg
  intro i _
  have h := hW.2 (Pi.single i 1)
  simpa only [← Pi.single_star, star_one, Matrix.mulVec_single_one,
    single_one_dotProduct, Matrix.transpose_apply, Matrix.diag_apply] using h

omit [Fintype R] [DecidableEq R] [DecidableEq A] in
theorem partialTrace_flagMatrix [Fintype R] [DecidableEq R] [DecidableEq A] (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ) :
    partialTraceMatrix (flagMatrix X W) = blockSum (partialTraceMatrix X) (scalarFlag W.trace) := by
  ext r s
  rcases r with r | u <;> rcases s with s | v <;>
    simp [partialTraceMatrix, flagMatrix, referenceFlagEquiv, blockSum,
      Matrix.fromBlocks, Matrix.submatrix_apply, scalarFlag, Matrix.trace, Matrix.diag]

theorem traceNorm_flagMatrix_posSemidef (X : Matrix (R × A) (R × A) ℂ)
    (W : Matrix A A ℂ) (hX : X.IsHermitian) (hW : W.PosSemidef) :
    traceNorm (flagMatrix X W) (flagMatrix_hermitian X W hX hW.1) =
      traceNorm X hX + W.trace.re := by
  rw [traceNorm_flagMatrix, traceNorm_eq_trace_of_posSemidef W hW]

theorem traceNorm_partialTrace_flagMatrix_posSemidef
    (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ)
    (hX : X.IsHermitian) (hW : W.PosSemidef) :
    traceNorm (partialTraceMatrix (flagMatrix X W))
      (partialTraceMatrix_hermitian _ (flagMatrix_hermitian X W hX hW.1)) =
      traceNorm (partialTraceMatrix X) (partialTraceMatrix_hermitian X hX) + W.trace.re := by
  have hscalar := scalarFlag_posSemidef W.trace (trace_nonneg_of_posSemidef W hW)
  have h := traceNorm_blockSum_posSemidef (partialTraceMatrix X) (scalarFlag W.trace)
    (partialTraceMatrix_hermitian X hX) hscalar
  simpa only [← partialTrace_flagMatrix, scalarFlag_trace] using h

/-- A positive orthogonal reference flag cancels exactly from the norm gap. -/
theorem traceNorm_gap_flagMatrix_posSemidef
    (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ)
    (hX : X.IsHermitian) (hW : W.PosSemidef) :
    traceNorm (flagMatrix X W) (flagMatrix_hermitian X W hX hW.1) -
      traceNorm (partialTraceMatrix (flagMatrix X W))
        (partialTraceMatrix_hermitian _ (flagMatrix_hermitian X W hX hW.1)) =
      traceNorm X hX - traceNorm (partialTraceMatrix X) (partialTraceMatrix_hermitian X hX) := by
  rw [traceNorm_flagMatrix_posSemidef X W hX hW,
    traceNorm_partialTrace_flagMatrix_posSemidef X W hX hW]
  ring

theorem traceNorm_flagMatrix_neg_posSemidef (X : Matrix (R × A) (R × A) ℂ)
    (W : Matrix A A ℂ) (hX : X.IsHermitian) (hW : W.PosSemidef) :
    traceNorm (flagMatrix X (-W)) (flagMatrix_hermitian X (-W) hX hW.1.neg) =
      traceNorm X hX + W.trace.re := by
  rw [traceNorm_flagMatrix, traceNorm_neg W hW.1, traceNorm_eq_trace_of_posSemidef W hW]

theorem traceNorm_partialTrace_flagMatrix_neg_posSemidef
    (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ)
    (hX : X.IsHermitian) (hW : W.PosSemidef) :
    traceNorm (partialTraceMatrix (flagMatrix X (-W)))
      (partialTraceMatrix_hermitian _ (flagMatrix_hermitian X (-W) hX hW.1.neg)) =
      traceNorm (partialTraceMatrix X) (partialTraceMatrix_hermitian X hX) + W.trace.re := by
  have hscalar := scalarFlag_posSemidef W.trace (trace_nonneg_of_posSemidef W hW)
  have heq : partialTraceMatrix (flagMatrix X (-W)) =
      blockSum (partialTraceMatrix X) (-scalarFlag W.trace) := by
    rw [partialTrace_flagMatrix, Matrix.trace_neg, scalarFlag_neg]
  have h := traceNorm_blockSum_neg_posSemidef (partialTraceMatrix X) (scalarFlag W.trace)
    (partialTraceMatrix_hermitian X hX) hscalar
  simpa only [← heq, scalarFlag_trace] using h

/-- A negative positive-semidefinite reference flag also cancels from the norm gap. -/
theorem traceNorm_gap_flagMatrix_neg_posSemidef
    (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ)
    (hX : X.IsHermitian) (hW : W.PosSemidef) :
    traceNorm (flagMatrix X (-W)) (flagMatrix_hermitian X (-W) hX hW.1.neg) -
      traceNorm (partialTraceMatrix (flagMatrix X (-W)))
        (partialTraceMatrix_hermitian _ (flagMatrix_hermitian X (-W) hX hW.1.neg)) =
      traceNorm X hX - traceNorm (partialTraceMatrix X) (partialTraceMatrix_hermitian X hX) := by
  rw [traceNorm_flagMatrix_neg_posSemidef X W hX hW,
    traceNorm_partialTrace_flagMatrix_neg_posSemidef X W hX hW]
  ring

end

end CMICounterexample
