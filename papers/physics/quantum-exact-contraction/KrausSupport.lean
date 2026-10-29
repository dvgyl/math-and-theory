import KrausSaturation
import GeneralKraus
import GeneralContraction
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin

open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey

namespace KrausSupport
noncomputable section

variable {A B C I : Type}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]

omit [Fintype C] [DecidableEq C] in
/-- A rectangular matrix factor exists exactly when the first kernel is included
in the second. This uses an actual linear extension from the range. -/
theorem exists_leftFactor_of_ker_le [Fintype C] [DecidableEq C] (W : Matrix B I ℂ) (U : Matrix C I ℂ)
    (h : LinearMap.ker W.toLin' ≤ LinearMap.ker U.toLin') :
    ∃ L : Matrix C B ℂ, L * W = U := by
  let f : LinearMap.range W.toLin' →ₗ[ℂ] (C → ℂ) :=
    ((LinearMap.ker W.toLin').liftQ U.toLin' h).comp
      W.toLin'.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g,hg⟩ := f.exists_extend
  have hcomp : g.comp W.toLin' = U.toLin' := by
    apply LinearMap.ext
    intro x
    have hh := LinearMap.congr_fun hg ⟨W.toLin' x, LinearMap.mem_range_self _ x⟩
    change g (W.toLin' x) =
      ((LinearMap.ker W.toLin').liftQ U.toLin' h)
        (W.toLin'.quotKerEquivRange.symm ⟨W.toLin' x, _⟩) at hh
    rw [LinearMap.quotKerEquivRange_symm_apply_image] at hh
    simpa using hh
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have hh := congrArg LinearMap.toMatrix' hcomp
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using hh

/-- The input slice with output vector v at input coordinate a. -/
def fiber (a : A) (v : B → ℂ) : A × B → ℂ :=
  fun p => if p.1 = a then v p.2 else 0

/-- Kraus operators regarded as columns in input tensor output coordinates. -/
def krausVectors (K : I → Matrix B A ℂ) : Matrix (A × B) I ℂ :=
  fun p i => K i p.2 p.1

def productColumns (v : B → ℂ) : Matrix (A × B) A ℂ :=
  fun p a => fiber a v p

omit [Fintype A] [Fintype B] [DecidableEq B] in
/-- Membership of all product slices in the Kraus span gives a single coefficient
matrix whose product is the full product block. -/
theorem product_factor_of_range [Fintype A] [Fintype B] [DecidableEq B] (W : Matrix (A × B) I ℂ) (v : B → ℂ)
    (h : ∀ a, fiber a v ∈ LinearMap.range W.toLin') :
    ∃ T : Matrix I A ℂ, W * T = productColumns v := by
  choose c hc using h
  refine ⟨fun i a => c a i, ?_⟩
  ext p a
  exact congrFun (hc a) p


/-- Recover a rectangular Kraus family from its columns. -/
def unvector (W : Matrix (A × B) I ℂ) (i : I) : Matrix B A ℂ :=
  fun b a => W (a,b) i

def choiApply (J : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ) : Matrix B B ℂ :=
  fun b c => ∑ a, ∑ d, J (a,b) (d,c) * X a d

omit [DecidableEq A] [Fintype B] [DecidableEq B] [DecidableEq I] in
theorem krausMap_eq_choiApply [DecidableEq A] [Fintype B] [DecidableEq B] [DecidableEq I] (W : Matrix (A × B) I ℂ) (X : Matrix A A ℂ) :
    GeneralKraus.krausMap (unvector W) X = choiApply (W * Wᴴ) X := by
  ext b c
  simp only [GeneralKraus.krausMap_apply, Matrix.mul_assoc]
  simp only [choiApply, unvector, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem choiApply_sub [DecidableEq A] [Fintype B] [DecidableEq B] (J L : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ) :
    choiApply (J-L) X = choiApply J X - choiApply L X := by
  ext b c
  simp [choiApply, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem choiApply_real_smul [DecidableEq A] [Fintype B] [DecidableEq B] (J : Matrix (A × B) (A × B) ℂ) (X : Matrix A A ℂ)
    (t : ℝ) : choiApply (t • J) X = t • choiApply J X := by
  ext b c
  simp [choiApply, Complex.real_smul, Finset.mul_sum, mul_assoc]

def rankOne (v : B → ℂ) : Matrix B B ℂ := fun b c => v b * star (v c)

omit [DecidableEq B] in
theorem rankOne_posSemidef [DecidableEq B] (v : B → ℂ) : (rankOne v).PosSemidef := by
  let V : Matrix B Unit ℂ := fun b _ => v b
  have h : V * Vᴴ = rankOne v := by
    ext b c
    simp [V, rankOne, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← h]
  exact Matrix.posSemidef_self_mul_conjTranspose V

omit [Fintype B] [DecidableEq B] in
theorem choiApply_productColumns [Fintype B] [DecidableEq B] (v : B → ℂ) (X : Matrix A A ℂ) :
    choiApply (productColumns v * (productColumns v)ᴴ) X = X.trace • rankOne v := by
  ext b c
  simp [choiApply, productColumns, fiber, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.trace, rankOne, Finset.sum_mul, Finset.mul_sum, mul_assoc, apply_ite,
    mul_comm, mul_left_comm]


/-- The range of a Gram matrix is exactly the range of its rectangular factor. -/
theorem range_self_mul_conjTranspose (W : Matrix B I ℂ) :
    LinearMap.range (W * Wᴴ).toLin' = LinearMap.range W.toLin' := by
  have hker : LinearMap.ker (W * Wᴴ).toLin' ≤ LinearMap.ker Wᴴ.toLin' := by
    intro x hx
    change (W * Wᴴ) *ᵥ x = 0 at hx
    change Wᴴ *ᵥ x = 0
    have hz : star x ⬝ᵥ ((Wᴴ)ᴴ * Wᴴ) *ᵥ x = 0 := by
      simp only [Matrix.conjTranspose_conjTranspose, hx, dotProduct_zero]
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec,
      vecMul_conjTranspose, star_star, dotProduct_star_self_eq_zero] at hz
    exact hz
  obtain ⟨L,hL⟩ := exists_leftFactor_of_ker_le (W * Wᴴ) Wᴴ hker
  have hW : (W * Wᴴ) * Lᴴ = W := by
    have h := congrArg Matrix.conjTranspose hL
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using h
  apply le_antisymm
  · rintro x ⟨y,hy⟩
    refine ⟨Wᴴ *ᵥ y, ?_⟩
    simpa only [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using hy
  · rintro x ⟨y,hy⟩
    refine ⟨Lᴴ *ᵥ y, ?_⟩
    simpa only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hW] using hy

omit [DecidableEq B] in
/-- A nonzero vector has a positive-trace rank-one matrix. -/
theorem rankOne_trace_pos [DecidableEq B] (v : B → ℂ) (hv : v ≠ 0) :
    0 < (rankOne v).trace.re := by
  have ht : (rankOne v).trace.re = ∑ b, Complex.normSq (v b) := by
    simp [rankOne, Matrix.trace, Complex.mul_conj]
  rw [ht]
  obtain ⟨b,hb⟩ : ∃ b, v b ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    ext b
    exact h b
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg (v i))
    ⟨b, Finset.mem_univ b, Complex.normSq_pos.mpr hb⟩

omit [DecidableEq B] in
/-- The rectangular product factor gives a positive scalar whose residual Choi
Gram matrix is PSD. No Choi-to-CP equivalence is assumed. -/
theorem exists_positive_gram_remainder [DecidableEq B] (W : Matrix (A × B) I ℂ)
    (v : B → ℂ) (T : Matrix I A ℂ) (hT : W * T = productColumns v) :
    ∃ t : ℝ, 0 < t ∧
      (W * Wᴴ - t • (productColumns v * (productColumns v)ᴴ)).PosSemidef := by
  let Q := T * Tᴴ
  have hQ : Q.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose T
  have htr : 0 ≤ Q.trace.re := by
    rw [← traceNorm_eq_trace_of_posSemidef _ hQ]
    exact traceNorm_nonneg _ hQ.1
  let c : ℝ := 1 + Q.trace.re
  have hc : 0 < c := by dsimp [c]; linarith
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  have hdom : (c • (1 : Matrix I I ℂ) - Q).PosSemidef := by
    have hh := (Matrix.PosSemidef.one : (1 : Matrix I I ℂ).PosSemidef).add
      (KrausSaturation.posSemidef_trace_domination Q hQ)
    have heq : (1 : Matrix I I ℂ) + (Q.trace.re • (1 : Matrix I I ℂ) - Q) =
        c • (1 : Matrix I I ℂ) - Q := by
      simp [c, add_smul, one_smul, add_sub_assoc]
    rwa [heq] at hh
  have hres : ((1 : Matrix I I ℂ) - c⁻¹ • Q).PosSemidef := by
    have hh := posSemidef_real_smul _ hdom c⁻¹ (le_of_lt (inv_pos.mpr hc))
    simpa only [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul] using hh
  have heq : W * ((1 : Matrix I I ℂ) - c⁻¹ • Q) * Wᴴ =
      W * Wᴴ - c⁻¹ • (productColumns v * (productColumns v)ᴴ) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [Q, Matrix.mul_assoc, ← hT, Matrix.conjTranspose_mul]
  rw [← heq]
  exact hres.mul_mul_conjTranspose_same W


/-- Every PSD Gram matrix here yields an actual finite Kraus family by taking its
PSD square root and unvectorizing its columns. -/
theorem exists_kraus_of_positive_gram (J : Matrix (A × B) (A × B) ℂ)
    (hJ : J.PosSemidef) :
    ∃ L : (A × B) → Matrix B A ℂ,
      ∀ X, GeneralKraus.krausMap L X = choiApply J X := by
  refine ⟨unvector hJ.sqrt, ?_⟩
  intro X
  rw [krausMap_eq_choiApply, hJ.posSemidef_sqrt.1.eq, hJ.sqrt_mul_self]

/-- Product slices in the actual Kraus span force a nonzero positive replacer
minorant. Complete positivity of the residual is proved using an explicit finite
Kraus family, at every finite reference dimension. -/
theorem hasPositiveReplacer_of_product_range (N : QuantumChannel A B)
    (K : I → Matrix B A ℂ) (hK : N.map = GeneralKraus.krausMap K)
    (v : B → ℂ) (hv : v ≠ 0)
    (hprod : ∀ a, fiber a v ∈ LinearMap.range (krausVectors K).toLin') :
    GeneralContraction.HasPositiveReplacer N := by
  obtain ⟨T,hT⟩ := product_factor_of_range (krausVectors K) v hprod
  obtain ⟨t,ht,hJ⟩ := exists_positive_gram_remainder (krausVectors K) v T hT
  obtain ⟨L,hL⟩ := exists_kraus_of_positive_gram _ hJ
  have hmap : ∀ X, GeneralKraus.krausMap L X =
      N.map X - X.trace • (t • rankOne v) := by
    intro X
    rw [hL, choiApply_sub, choiApply_real_smul, choiApply_productColumns,
      ← krausMap_eq_choiApply, hK]
    change GeneralKraus.krausMap K X - t • (X.trace • rankOne v) =
      GeneralKraus.krausMap K X - X.trace • (t • rankOne v)
    rw [smul_comm t X.trace]
  refine ⟨t • rankOne v, posSemidef_real_smul _ (rankOne_posSemidef v) t ht.le, ?_, ?_⟩
  · rw [Matrix.trace_smul]
    simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using mul_pos ht (rankOne_trace_pos v hv)
  · intro R _ _ X hX
    have hcp := GeneralKraus.completely_positive L X hX
    have heq : amplify (GeneralKraus.krausMap L) X =
        amplify N.map X - Matrix.kronecker (partialTraceMatrix X) (t • rankOne v) := by
      ext r s
      change (GeneralKraus.krausMap L (fun a b => X (r.1,a) (s.1,b))) r.2 s.2 = _
      rw [hmap]
      rfl
    rwa [heq] at hcp

/-- Failure of a positive replacer minorant excludes every nonzero full input
product slice from the actual Kraus span. -/
theorem product_slice_zero_of_no_replacer (N : QuantumChannel A B)
    (K : I → Matrix B A ℂ) (hK : N.map = GeneralKraus.krausMap K)
    (hN : ¬ GeneralContraction.HasPositiveReplacer N)
    (v : B → ℂ)
    (hprod : ∀ a, fiber a v ∈ LinearMap.range (krausVectors K).toLin') : v = 0 := by
  by_contra hv
  exact hN (hasPositiveReplacer_of_product_range N K hK v hv hprod)

end
end KrausSupport
