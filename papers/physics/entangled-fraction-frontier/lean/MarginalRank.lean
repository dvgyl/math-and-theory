import OptimizerComplementarity
import Mathlib.Analysis.Matrix.Spectrum

set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder Kronecker
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open MilneExpanded
open MilneNew.RankOneExtraction

namespace MilneContinuation

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def tensorVector (u : a → ℂ) (v : b → ℂ) (ij : a × b) : ℂ := u ij.1 * v ij.2

omit [Fintype a] [DecidableEq a] in
lemma tensorVector_right_expansion (u : a → ℂ) (v : b → ℂ) :
    tensorVector u v = ∑ j, v j • tensorVector u (Pi.single j 1) := by
  funext ij
  simp [tensorVector, Pi.single_apply, mul_comm]

omit [Fintype b] [DecidableEq b] in
lemma tensorVector_left_expansion (u : a → ℂ) (v : b → ℂ) :
    tensorVector u v = ∑ i, u i • tensorVector (Pi.single i 1) v := by
  funext ij
  simp [tensorVector, Pi.single_apply, mul_comm]

omit [DecidableEq a] in
lemma partialTraceRight_expectation_sum
    (R : Matrix (a × b) (a × b) ℂ) (u : a → ℂ) :
    ∑ j, expectation R (tensorVector u (Pi.single j 1)) =
      (star u ⬝ᵥ (partialTraceRight R *ᵥ u)).re := by
  simp only [expectation, tensorVector, mulVec, dotProduct, partialTraceRight,
    Fintype.sum_prod_type, Pi.star_apply, star_zero,
    Pi.single_apply, ite_mul, mul_one, zero_mul, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul,
    Finset.mul_sum, Complex.re_sum, apply_ite, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

omit [DecidableEq b] in
lemma partialTraceLeft_expectation_sum
    (R : Matrix (a × b) (a × b) ℂ) (v : b → ℂ) :
    ∑ i, expectation R (tensorVector (Pi.single i 1) v) =
      (star v ⬝ᵥ (partialTraceLeft R *ᵥ v)).re := by
  simp only [expectation, tensorVector, mulVec, dotProduct, partialTraceLeft,
    Fintype.sum_prod_type, Pi.star_apply, star_zero,
    Pi.single_apply, ite_mul, one_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul,
    Finset.mul_sum, Complex.re_sum, apply_ite, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]


/-- A kernel vector of Alice's actual marginal annihilates every product
vector formed with it in the PSD bipartite operator. -/
theorem partialTraceRight_kernel_lift
    {R : Matrix (a × b) (a × b) ℂ} (hR : R.PosSemidef)
    (u : a → ℂ) (v : b → ℂ) (hu : partialTraceRight R *ᵥ u = 0) :
    R *ᵥ tensorVector u v = 0 := by
  have hsum : ∑ j, expectation R (tensorVector u (Pi.single j 1)) = 0 := by
    rw [partialTraceRight_expectation_sum, hu]
    simp
  have hterm : ∀ j, expectation R (tensorVector u (Pi.single j 1)) = 0 := by
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      (Complex.nonneg_iff.mp (hR.dotProduct_mulVec_nonneg _)).1).mp hsum j (Finset.mem_univ j)
  have hker : ∀ j, R *ᵥ tensorVector u (Pi.single j 1) = 0 :=
    fun j => (expectation_zero_iff_mulVec_zero hR _).mp (hterm j)
  change R.mulVecLin (tensorVector u v) = 0
  rw [tensorVector_right_expansion, map_sum]
  simp only [map_smul, Matrix.mulVecLin_apply, hker, smul_zero, Finset.sum_const_zero]

/-- The corresponding kernel lifting theorem for Bob's actual marginal. -/
theorem partialTraceLeft_kernel_lift
    {R : Matrix (a × b) (a × b) ℂ} (hR : R.PosSemidef)
    (u : a → ℂ) (v : b → ℂ) (hv : partialTraceLeft R *ᵥ v = 0) :
    R *ᵥ tensorVector u v = 0 := by
  have hsum : ∑ i, expectation R (tensorVector (Pi.single i 1) v) = 0 := by
    rw [partialTraceLeft_expectation_sum, hv]
    simp
  have hterm : ∀ i, expectation R (tensorVector (Pi.single i 1) v) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      (Complex.nonneg_iff.mp (hR.dotProduct_mulVec_nonneg _)).1).mp hsum i (Finset.mem_univ i)
  have hker : ∀ i, R *ᵥ tensorVector (Pi.single i 1) v = 0 :=
    fun i => (expectation_zero_iff_mulVec_zero hR _).mp (hterm i)
  change R.mulVecLin (tensorVector u v) = 0
  rw [tensorVector_left_expansion, map_sum]
  simp only [map_smul, Matrix.mulVecLin_apply, hker, smul_zero, Finset.sum_const_zero]

/-- Counting a set containing all nonzero columns bounds a matrix rank. -/
theorem matrix_rank_le_supported_columns
    {m n : Type*} [Fintype m] [Fintype n] (C : Matrix m n ℂ)
    (P : n → Prop) [DecidablePred P] (hzero : ∀ j, ¬ P j → C.col j = 0) :
    C.rank ≤ Fintype.card {j // P j} := by
  classical
  let f : {j // P j} → m → ℂ := fun j => C.col j.1
  have hspan : Submodule.span ℂ (Set.range C.col) ≤
      Submodule.span ℂ (Set.range f) := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    by_cases hj : P j
    · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    · rw [hzero j hj]
      exact Submodule.zero_mem _
  rw [Matrix.rank_eq_finrank_span_cols]
  exact (Submodule.finrank_mono hspan).trans (finrank_range_le_card f)

/-- The rank of an actual finite PSD bipartite matrix is at most the product
of the ranks of its two actual partial traces. No density normalization,
full-rank hypothesis or support inclusion is assumed. -/
theorem psd_rank_le_marginal_rank_product
    (R : Matrix (a × b) (a × b) ℂ) (hR : R.PosSemidef) :
    R.rank ≤ (partialTraceRight R).rank * (partialTraceLeft R).rank := by
  classical
  let A := partialTraceRight R
  let B := partialTraceLeft R
  have hA : A.PosSemidef := partialTraceRight_posSemidef hR
  have hB : B.PosSemidef := partialTraceLeft_posSemidef hR
  let U := hA.isHermitian.eigenvectorUnitary
  let V := hB.isHermitian.eigenvectorUnitary
  let K : Matrix (a × b) (a × b) ℂ :=
    (U : Matrix a a ℂ) ⊗ₖ (V : Matrix b b ℂ)
  have hKi : IsUnit K := by
    apply IsUnit.of_mul_eq_one ((star U : Matrix a a ℂ) ⊗ₖ (star V : Matrix b b ℂ))
    dsimp [K]
    rw [← Matrix.mul_kronecker_mul]
    simp only [← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_kronecker_one]
  have hRank : (R * K).rank = R.rank :=
    Matrix.rank_mul_eq_left_of_isUnit_det K R ((Matrix.isUnit_iff_isUnit_det K).mp hKi)
  let good : a × b → Prop := fun ij =>
    hA.isHermitian.eigenvalues ij.1 ≠ 0 ∧ hB.isHermitian.eigenvalues ij.2 ≠ 0
  have hcol : ∀ ij, ¬ good ij → (R * K).col ij = 0 := by
    intro ij hn
    have hz : hA.isHermitian.eigenvalues ij.1 = 0 ∨
        hB.isHermitian.eigenvalues ij.2 = 0 := by
      dsimp [good] at hn
      tauto
    have hKcol : K.col ij = tensorVector
        ((U : Matrix a a ℂ).col ij.1) ((V : Matrix b b ℂ).col ij.2) := by
      ext kl
      rfl
    have hRK : (R * K).col ij = R *ᵥ K.col ij := rfl
    rw [hRK, hKcol]
    rcases hz with hz | hz
    · apply partialTraceRight_kernel_lift hR
      change A *ᵥ (hA.isHermitian.eigenvectorUnitary : Matrix a a ℂ).col ij.1 = 0
      rw [hA.isHermitian.eigenvectorUnitary_col_eq,
        hA.isHermitian.mulVec_eigenvectorBasis, hz, zero_smul]
    · apply partialTraceLeft_kernel_lift hR
      change B *ᵥ (hB.isHermitian.eigenvectorUnitary : Matrix b b ℂ).col ij.2 = 0
      rw [hB.isHermitian.eigenvectorUnitary_col_eq,
        hB.isHermitian.mulVec_eigenvectorBasis, hz, zero_smul]
  have hbound := matrix_rank_le_supported_columns (m := a × b) (n := a × b) (R * K) good hcol
  have hcard : Fintype.card {ij // good ij} =
      Fintype.card {i // hA.isHermitian.eigenvalues i ≠ 0} *
      Fintype.card {j // hB.isHermitian.eigenvalues j ≠ 0} := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr (Equiv.subtypeProdEquivProd
      (p := fun i : a => hA.isHermitian.eigenvalues i ≠ 0)
      (q := fun j : b => hB.isHermitian.eigenvalues j ≠ 0))
  rw [hRank, hcard, ← hA.isHermitian.rank_eq_card_non_zero_eigs,
    ← hB.isHermitian.rank_eq_card_non_zero_eigs] at hbound
  exact hbound

/-- Rank subadditivity for actual finite matrices. -/
theorem matrix_rank_add_le {m n : Type*} [Fintype m] [Fintype n]
    (P Q : Matrix m n ℂ) : (P + Q).rank ≤ P.rank + Q.rank := by
  rw [Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le P.mulVecLin Q.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- All actual pure-target optimizers have an explicit residual-rank bound,
with the target's actual Schmidt rank in the complementary rank constraint. -/
theorem every_optimizer_rank_bound
    (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : A.trace = 1) (hB : B.trace = 1) (X : Matrix a b ℂ)
    (M : Matrix (a × b) (a × b) ℂ) (hM : Compatible A B M)
    (hopt : ∀ N, Compatible A B N →
      expectation N (targetVector X) ≤ expectation M (targetVector X)) :
    ∃ r s : ℕ,
      r ≤ Fintype.card a ∧ s ≤ Fintype.card b ∧
      r + s + X.rank ≤ Fintype.card a + Fintype.card b ∧
      M.rank ≤ 1 + r * s := by
  obtain ⟨w, R, hdec, hw, hR, heq, hker, hz, hsum⟩ :=
    actual_state_optimizer_residual_decomposition A B hA hB X M hM hopt
  refine ⟨(residualA A w).rank, (residualB B w).rank,
    Matrix.rank_le_card_width _, Matrix.rank_le_card_width _, hsum, ?_⟩
  have hres := psd_rank_le_marginal_rank_product R hR.1
  rw [hR.2.1, hR.2.2] at hres
  have hcore : (outer w).rank ≤ 1 := Matrix.rank_vecMulVec_le w (star w)
  rw [hdec]
  exact (matrix_rank_add_le (outer w) R).trans (Nat.add_le_add hcore hres)

/-- The square full-Schmidt bound for every actual optimizing state, in a
form avoiding subtraction and natural-number truncation. -/
theorem every_full_schmidt_optimizer_rank_bound {d : ℕ}
    (A B X : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.trace = 1) (hB : B.trace = 1) (hX : IsUnit X.det)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : Compatible A B M)
    (hopt : ∀ N, Compatible A B N →
      expectation N (targetVector X) ≤ expectation M (targetVector X)) :
    M.rank ≤ 1 + d^2 / 4 := by
  obtain ⟨r, s, hr, hs, hsum, hMbound⟩ := every_optimizer_rank_bound
    A B hA hB X M hM hopt
  have hXrank : X.rank = d := by
    simpa only [Fintype.card_fin] using
      Matrix.rank_of_isUnit X ((Matrix.isUnit_iff_isUnit_det X).mpr hX)
  rw [Fintype.card_fin, hXrank] at hsum
  have hrs : r + s ≤ d := by omega
  have hprod : 4 * (r * s) ≤ d^2 := by
    have hz : (r : ℤ) + (s : ℤ) ≤ (d : ℤ) := by exact_mod_cast hrs
    have hr0 : (0 : ℤ) ≤ r := by positivity
    have hs0 : (0 : ℤ) ≤ s := by positivity
    have hd0 : (0 : ℤ) ≤ d := by positivity
    have hh : 4 * ((r : ℤ) * (s : ℤ)) ≤ (d : ℤ)^2 := by
      nlinarith [sq_nonneg ((r : ℤ) - (s : ℤ))]
    exact_mod_cast hh
  omega

end MilneContinuation

#print axioms MilneContinuation.partialTraceRight_kernel_lift
#print axioms MilneContinuation.partialTraceLeft_kernel_lift
#print axioms MilneContinuation.psd_rank_le_marginal_rank_product
#print axioms MilneContinuation.every_optimizer_rank_bound
#print axioms MilneContinuation.every_full_schmidt_optimizer_rank_bound
