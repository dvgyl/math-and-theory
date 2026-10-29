import GeneralContraction
import CoefficientConvexity
import ReplacerBounds

/-! Exact transport through an orthogonal family of bipartite density matrices. -/
open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey GeneralContraction CoefficientConvexity

namespace BellEncoding
noncomputable section

variable {S A B I : Type} [Fintype S] [DecidableEq S]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype I] [DecidableEq I]

def tensorSum (Φ : I → Matrix B B ℂ) (X : I → Matrix S S ℂ) :
    Matrix (S × B) (S × B) ℂ := ∑ i, X i ⊗ₖ Φ i

omit [DecidableEq I] in
theorem tensorSum_hermitian [DecidableEq I] (Φ : I → Matrix B B ℂ) (X : I → Matrix S S ℂ)
    (hΦ : ∀ i, (Φ i).IsHermitian) (hX : ∀ i, (X i).IsHermitian) :
    (tensorSum Φ X).IsHermitian :=
  sum_hermitian _ (fun i => kronecker_hermitian _ _ (hX i) (hΦ i))

omit [DecidableEq I] in
theorem tensorSum_positive [DecidableEq I] (Φ : I → Matrix B B ℂ) (X : I → Matrix S S ℂ)
    (hΦ : ∀ i, (Φ i).PosSemidef) (hX : ∀ i, (X i).PosSemidef) :
    (tensorSum Φ X).PosSemidef := by
  exact Finset.sum_induction _ _ (fun P Q hP hQ => hP.add hQ)
    Matrix.PosSemidef.zero (fun i _ => kronecker_positive _ _ (hX i) (hΦ i))

omit [DecidableEq S] [DecidableEq B] [DecidableEq I] in
theorem tensorSum_trace [DecidableEq S] [DecidableEq B] [DecidableEq I] (Φ : I → Matrix B B ℂ) (X : I → Matrix S S ℂ)
    (hΦ : ∀ i, (Φ i).trace = 1) : (tensorSum Φ X).trace = ∑ i, (X i).trace := by
  simp only [tensorSum, Matrix.trace_sum, Matrix.trace_kronecker, hΦ, mul_one]

omit [DecidableEq I] in
theorem tensorSum_sub [DecidableEq I] (Φ : I → Matrix B B ℂ) (X Y : I → Matrix S S ℂ) :
    tensorSum Φ (fun i => X i - Y i) = tensorSum Φ X - tensorSum Φ Y := by
  simp only [tensorSum, ReplacerBounds.sub_kronecker, Finset.sum_sub_distrib]

omit [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B] [DecidableEq I] in
theorem tensorSum_add [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B] [DecidableEq I] (Φ : I → Matrix B B ℂ) (X Y : I → Matrix S S ℂ) :
    tensorSum Φ (fun i => X i + Y i) = tensorSum Φ X + tensorSum Φ Y := by
  simp only [tensorSum, Matrix.add_kronecker, Finset.sum_add_distrib]

omit [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B] [DecidableEq I] in
theorem tensorSum_real_smul [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B] [DecidableEq I] (Φ : I → Matrix B B ℂ) (X : I → Matrix S S ℂ) (c : ℝ) :
    tensorSum Φ (fun i => c • X i) = c • tensorSum Φ X := by
  simp only [tensorSum, Matrix.smul_kronecker, Finset.smul_sum]

omit [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B] [DecidableEq I] in
theorem tensorSum_sub_right [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B] [DecidableEq I] (Φ Ψ : I → Matrix B B ℂ) (X : I → Matrix S S ℂ) :
    tensorSum (fun i => Φ i - Ψ i) X = tensorSum Φ X - tensorSum Ψ X := by
  ext p q
  simp only [tensorSum, Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply,
    mul_sub, Finset.sum_sub_distrib]

omit [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B] [DecidableEq I] in
theorem tensorSum_real_smul_right [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B] [DecidableEq I] (Φ : I → Matrix B B ℂ)
    (X : I → Matrix S S ℂ) (c : ℝ) :
    tensorSum (fun i => c • Φ i) X = c • tensorSum Φ X := by
  simp only [tensorSum, Matrix.kronecker_smul, Finset.smul_sum]

omit [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B] [DecidableEq I] in
theorem tensorSum_const_right [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B] [DecidableEq I] (M : Matrix B B ℂ) (X : I → Matrix S S ℂ) :
    tensorSum (fun _ => M) X = (∑ i, X i) ⊗ₖ M := by
  ext p q
  simp only [tensorSum, Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

omit [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B] [DecidableEq I] in
theorem tensorSum_const [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B] [DecidableEq I] (Φ : I → Matrix B B ℂ) (X : Matrix S S ℂ) :
    tensorSum Φ (fun _ => X) = X ⊗ₖ (∑ i, Φ i) := by
  ext p q
  simp only [tensorSum, Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]

theorem tensorSum_one (Φ : I → Matrix B B ℂ) (hΦ : ∑ i, Φ i = 1) :
    tensorSum Φ (fun _ => (1 : Matrix S S ℂ)) = 1 := by
  rw [tensorSum_const, hΦ, Matrix.one_kronecker_one]

theorem tensorSum_affine (Φ : I → Matrix B B ℂ) (X : I → Matrix S S ℂ)
    (b s : ℝ) (hsum : ∑ i, Φ i = 1) :
    tensorSum (fun i => b • 1 - s • Φ i) X =
      tensorSum Φ (fun i => b • (∑ j, X j) - s • X i) := by
  rw [tensorSum_sub_right, tensorSum_real_smul_right, tensorSum_real_smul_right,
    tensorSum_const_right, tensorSum_sub, tensorSum_real_smul, tensorSum_real_smul,
    tensorSum_const, hsum]

omit [DecidableEq S] [DecidableEq B] in
theorem tensorSum_mul [DecidableEq S] [DecidableEq B] (Φ : I → Matrix B B ℂ) (X Y : I → Matrix S S ℂ)
    (hΦ : ∀ i j, Φ i * Φ j = if i = j then Φ i else 0) :
    tensorSum Φ X * tensorSum Φ Y = tensorSum Φ (fun i => X i * Y i) := by
  simp only [tensorSum, Matrix.sum_mul, Matrix.mul_sum, ← Matrix.mul_kronecker_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [hΦ]
  · intro j _ hji
    simp [hΦ, hji, Matrix.kronecker_zero]
  · simp

theorem traceNorm_tensorSum (Φ : I → Matrix B B ℂ) (X : I → Matrix S S ℂ)
    (hΦ : ∀ i, (Φ i).PosSemidef) (htrace : ∀ i, (Φ i).trace = 1)
    (horth : ∀ i j, Φ i * Φ j = if i = j then Φ i else 0)
    (hsum : ∑ i, Φ i = 1) (hX : ∀ i, (X i).IsHermitian) :
    traceNorm (tensorSum Φ X) (tensorSum_hermitian Φ X (fun i => (hΦ i).1) hX) =
      ∑ i, traceNorm (X i) (hX i) := by
  apply le_antisymm
  · have h := traceNorm_sum_le (fun i => X i ⊗ₖ Φ i)
      (fun i => kronecker_hermitian _ _ (hX i) (hΦ i).1)
    apply h.trans
    apply Finset.sum_le_sum
    intro i _
    simpa only [htrace i, Complex.one_re, one_mul] using
      ReplacerBounds.traceNorm_kronecker_le (X i) (Φ i) (hX i) (hΦ i)
  · choose T hT hm hp ht using fun i => exists_traceNorm_dual (X i) (hX i)
    have hm' : (1 - tensorSum Φ T).PosSemidef := by
      rw [← tensorSum_one Φ hsum, ← tensorSum_sub]
      exact tensorSum_positive Φ _ hΦ hm
    have hp' : (1 + tensorSum Φ T).PosSemidef := by
      rw [← tensorSum_one Φ hsum, ← tensorSum_add]
      exact tensorSum_positive Φ _ hΦ hp
    have h := trace_mul_le_traceNorm (tensorSum Φ X)
      (tensorSum_hermitian Φ X (fun i => (hΦ i).1) hX) (tensorSum Φ T) hm' hp'
    simpa only [tensorSum_mul Φ T X horth, tensorSum_trace Φ _ htrace,
      Complex.re_sum, ht] using h

def encode (Φ : I → Matrix (A × A) (A × A) ℂ) (X : I → Matrix S S ℂ) :
    Matrix ((S × A) × A) ((S × A) × A) ℂ :=
  (tensorSum Φ X).submatrix (Equiv.prodAssoc S A A) (Equiv.prodAssoc S A A)

omit [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [DecidableEq I] in
theorem encode_apply [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [DecidableEq I] (Φ : I → Matrix (A × A) (A × A) ℂ)
    (X : I → Matrix S S ℂ) (p q : (S × A) × A) :
    encode Φ X p q = ∑ i, X i p.1.1 q.1.1 * Φ i (p.1.2,p.2) (q.1.2,q.2) := by
  change (∑ i, X i ⊗ₖ Φ i) (p.1.1,(p.1.2,p.2)) (q.1.1,(q.1.2,q.2)) = _
  rw [Matrix.sum_apply]
  rfl

theorem encode_hermitian (Φ : I → Matrix (A × A) (A × A) ℂ)
    (X : I → Matrix S S ℂ) (hΦ : ∀ i, (Φ i).IsHermitian)
    (hX : ∀ i, (X i).IsHermitian) : (encode Φ X).IsHermitian :=
  (tensorSum_hermitian Φ X hΦ hX).submatrix _

theorem encode_positive (Φ : I → Matrix (A × A) (A × A) ℂ)
    (X : I → Matrix S S ℂ) (hΦ : ∀ i, (Φ i).PosSemidef)
    (hX : ∀ i, (X i).PosSemidef) : (encode Φ X).PosSemidef :=
  (tensorSum_positive Φ X hΦ hX).submatrix _

theorem encode_trace (Φ : I → Matrix (A × A) (A × A) ℂ)
    (X : I → Matrix S S ℂ) (hΦ : ∀ i, (Φ i).trace = 1) :
    (encode Φ X).trace = ∑ i, (X i).trace := by
  rw [encode, trace_submatrix_equiv, tensorSum_trace Φ X hΦ]

theorem traceNorm_encode (Φ : I → Matrix (A × A) (A × A) ℂ)
    (X : I → Matrix S S ℂ) (hΦ : ∀ i, (Φ i).PosSemidef)
    (htrace : ∀ i, (Φ i).trace = 1)
    (horth : ∀ i j, Φ i * Φ j = if i = j then Φ i else 0)
    (hsum : ∑ i, Φ i = 1) (hX : ∀ i, (X i).IsHermitian) :
    traceNorm (encode Φ X) (encode_hermitian Φ X (fun i => (hΦ i).1) hX) =
      ∑ i, traceNorm (X i) (hX i) := by
  exact (traceNorm_submatrix_equiv (tensorSum Φ X)
    (tensorSum_hermitian Φ X (fun i => (hΦ i).1) hX) (Equiv.prodAssoc S A A)).trans
      (traceNorm_tensorSum Φ X hΦ htrace horth hsum hX)

theorem encode_sub (Φ : I → Matrix (A × A) (A × A) ℂ)
    (X Y : I → Matrix S S ℂ) :
    encode Φ (fun i => X i - Y i) = encode Φ X - encode Φ Y := by
  unfold encode
  rw [tensorSum_sub]
  rfl

theorem encode_real_smul (Φ : I → Matrix (A × A) (A × A) ℂ)
    (X : I → Matrix S S ℂ) (c : ℝ) :
    encode Φ (fun i => c • X i) = c • encode Φ X := by
  ext p q
  simp only [encode_apply, Matrix.smul_apply, smul_mul_assoc, Finset.smul_sum]

omit [Fintype S] [DecidableEq S] [DecidableEq A] in
theorem partialTrace_kronecker [Fintype S] [DecidableEq S] [DecidableEq A] (X : Matrix S S ℂ) (M : Matrix A A ℂ) :
    partialTraceMatrix (X ⊗ₖ M) = M.trace • X := by
  ext r t
  simp only [partialTraceMatrix, Matrix.kroneckerMap_apply, Matrix.smul_apply,
    Matrix.trace, Matrix.diag, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem traceNorm_kronecker_density (X : Matrix S S ℂ) (M : Matrix A A ℂ)
    (hX : X.IsHermitian) (hM : M.PosSemidef) (htrace : M.trace = 1) :
    traceNorm (X ⊗ₖ M) (kronecker_hermitian X M hX hM.1) = traceNorm X hX := by
  apply le_antisymm
  · simpa only [htrace, Complex.one_re, one_mul] using
      ReplacerBounds.traceNorm_kronecker_le X M hX hM
  · have h := partialTrace_norm_le (X ⊗ₖ M) (kronecker_hermitian X M hX hM.1)
    simpa only [partialTrace_kronecker, htrace, one_smul] using h

theorem partialTrace_encode (Φ : I → Matrix (A × A) (A × A) ℂ)
    (X : I → Matrix S S ℂ) (M : Matrix A A ℂ)
    (hmargin : ∀ i, partialTraceMatrix (Φ i) = M) :
    partialTraceMatrix (encode Φ X) = (∑ i, X i) ⊗ₖ M := by
  ext r t
  simp only [partialTraceMatrix, encode_apply, Matrix.kroneckerMap_apply, Matrix.sum_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hm (i : I) : (∑ a, Φ i (r.2,a) (t.2,a)) = M r.2 t.2 :=
    congrArg (fun Z => Z r.2 t.2) (hmargin i)
  simp only [hm, Finset.sum_mul]

theorem traceNorm_partialTrace_encode (Φ : I → Matrix (A × A) (A × A) ℂ)
    (X : I → Matrix S S ℂ) (M : Matrix A A ℂ)
    (hΦ : ∀ i, (Φ i).IsHermitian) (hX : ∀ i, (X i).IsHermitian)
    (hM : M.PosSemidef) (htrace : M.trace = 1)
    (hmargin : ∀ i, partialTraceMatrix (Φ i) = M) :
    traceNorm (partialTraceMatrix (encode Φ X))
      (partialTraceMatrix_hermitian _ (encode_hermitian Φ X hΦ hX)) =
      traceNorm (∑ i, X i) (sum_hermitian X hX) := by
  have heq := partialTrace_encode Φ X M hmargin
  have h := traceNorm_kronecker_density (∑ i, X i) M (sum_hermitian X hX) hM htrace
  simpa only [← heq] using h

def mixedMarginal : Matrix A A ℂ := (Fintype.card A : ℝ)⁻¹ • 1

theorem mixedMarginal_positive : (mixedMarginal (A := A)).PosSemidef :=
  posSemidef_real_smul _ Matrix.PosSemidef.one _ (inv_nonneg.mpr (by positivity))

theorem mixedMarginal_trace [Nonempty A] : (mixedMarginal (A := A)).trace = 1 := by
  rw [mixedMarginal, Matrix.trace_smul, Matrix.trace_one]
  have hc : (Fintype.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simpa only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast] using
    inv_mul_cancel₀ hc

theorem traceNorm_partialTrace_encode_mixed [Nonempty A]
    (Φ : I → Matrix (A × A) (A × A) ℂ) (X : I → Matrix S S ℂ)
    (hΦ : ∀ i, (Φ i).IsHermitian) (hX : ∀ i, (X i).IsHermitian)
    (hmargin : ∀ i, partialTraceMatrix (Φ i) = mixedMarginal) :
    traceNorm (partialTraceMatrix (encode Φ X))
      (partialTraceMatrix_hermitian _ (encode_hermitian Φ X hΦ hX)) =
      traceNorm (∑ i, X i) (sum_hermitian X hX) :=
  traceNorm_partialTrace_encode Φ X mixedMarginal hΦ hX
    mixedMarginal_positive mixedMarginal_trace hmargin

theorem positiveTraceGap_encode [Nonempty A]
    (Φ : I → Matrix (A × A) (A × A) ℂ) (X : I → Matrix S S ℂ)
    (hΦ : ∀ i, (Φ i).PosSemidef) (htrace : ∀ i, (Φ i).trace = 1)
    (horth : ∀ i j, Φ i * Φ j = if i = j then Φ i else 0)
    (hsum : ∑ i, Φ i = 1) (hX : ∀ i, (X i).IsHermitian)
    (hmargin : ∀ i, partialTraceMatrix (Φ i) = mixedMarginal) :
    positiveTraceGap (encode Φ X) (encode_hermitian Φ X (fun i => (hΦ i).1) hX) =
      ((∑ i, traceNorm (X i) (hX i)) - traceNorm (∑ i, X i) (sum_hermitian X hX)) / 2 := by
  rw [positiveTraceGap_eq]
  unfold normGap
  rw [traceNorm_encode Φ X hΦ htrace horth hsum hX,
    traceNorm_partialTrace_encode_mixed Φ X (fun i => (hΦ i).1) hX hmargin]

def encodedDensity (Φ : I → Matrix (A × A) (A × A) ℂ)
    (X : I → Matrix S S ℂ) (hΦ : ∀ i, (Φ i).PosSemidef)
    (htrace : ∀ i, (Φ i).trace = 1) (hX : ∀ i, (X i).PosSemidef)
    (hnorm : ∑ i, (X i).trace = 1) : Density ((S × A) × A) where
  mat := encode Φ X
  positive := encode_positive Φ X hΦ hX
  normalized := (encode_trace Φ X htrace).trans hnorm

theorem amplify_encode (N : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ)
    (Φ : I → Matrix (A × A) (A × A) ℂ) (X : I → Matrix S S ℂ) :
    amplify N (encode Φ X) = encode (fun i => amplify N (Φ i)) X := by
  ext p q
  have hs : (fun a b => encode Φ X (p.1,a) (q.1,b)) =
      ∑ i, X i p.1.1 q.1.1 • (fun a b => Φ i (p.1.2,a) (q.1.2,b)) := by
    ext a b
    simp only [encode_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change N (fun a b => encode Φ X (p.1,a) (q.1,b)) p.2 q.2 = _
  rw [hs, map_sum]
  simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    encode_apply, amplify]

theorem amplify_encode_affine (N : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ)
    (Φ : I → Matrix (A × A) (A × A) ℂ) (X : I → Matrix S S ℂ)
    (b s : ℝ) (hsum : ∑ i, Φ i = 1)
    (haction : ∀ i, amplify N (Φ i) = b • 1 - s • Φ i) :
    amplify N (encode Φ X) = encode Φ (fun i => b • (∑ j, X j) - s • X i) := by
  rw [amplify_encode]
  have heq : (fun i => amplify N (Φ i)) = (fun i => b • 1 - s • Φ i) := funext haction
  rw [heq]
  unfold encode
  rw [tensorSum_affine Φ X b s hsum]

omit [Fintype S] [DecidableEq S] in
theorem amplify_depolarizing [Fintype S] [DecidableEq S] (N : QuantumChannel A A) (s : ℝ)
    (hN : ∀ X, N.map X = ((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1 : Matrix A A ℂ)) - s • X)
    (X : Matrix (S × A) (S × A) ℂ) :
    amplify N.map X = ((1+s)/(Fintype.card A : ℝ)) •
      (partialTraceMatrix X ⊗ₖ (1 : Matrix A A ℂ)) - s • X := by
  ext p q
  change N.map (fun a b => X (p.1,a) (q.1,b)) p.2 q.2 = _
  rw [hN]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.trace, Matrix.diag,
    partialTraceMatrix, Matrix.kroneckerMap_apply, smul_eq_mul]

theorem amplify_depolarizing_bell (N : QuantumChannel A A) (s : ℝ)
    (hN : ∀ X, N.map X = ((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1 : Matrix A A ℂ)) - s • X)
    (Φ : Matrix (A × A) (A × A) ℂ)
    (hmargin : partialTraceMatrix Φ = mixedMarginal) :
    amplify N.map Φ = ((1+s)/(Fintype.card A : ℝ)^2) • 1 - s • Φ := by
  rw [amplify_depolarizing N s hN Φ, hmargin, mixedMarginal,
    Matrix.smul_kronecker, Matrix.one_kronecker_one, smul_smul]
  have hc : ((1+s)/(Fintype.card A : ℝ)) * (Fintype.card A : ℝ)⁻¹ =
      (1+s)/(Fintype.card A : ℝ)^2 := by
    simp [div_eq_mul_inv, pow_two, _root_.mul_inv_rev, mul_assoc]
  rw [hc]

theorem amplify_encode_depolarizing (N : QuantumChannel A A) (s : ℝ)
    (hN : ∀ X, N.map X = ((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1 : Matrix A A ℂ)) - s • X)
    (Φ : I → Matrix (A × A) (A × A) ℂ) (X : I → Matrix S S ℂ)
    (hsum : ∑ i, Φ i = 1)
    (hmargin : ∀ i, partialTraceMatrix (Φ i) = mixedMarginal) :
    amplify N.map (encode Φ X) =
      encode Φ (fun i => ((1+s)/(Fintype.card A : ℝ)^2) • (∑ j, X j) - s • X i) :=
  amplify_encode_affine N.map Φ X _ s hsum
    (fun i => amplify_depolarizing_bell N s hN (Φ i) (hmargin i))

end
end BellEncoding
