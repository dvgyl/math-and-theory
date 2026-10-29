module
public import ConditionalHockey
public import GeneralKraus
public import KrausSupport
public import Mathlib.LinearAlgebra.Matrix.ToLin


@[expose] public section

/-!
# Finite Bell preparations and the common-range reduction

The finite family below uses real monomial unitaries.  Its members need not be
orthogonal as Hilbert--Schmidt vectors: the proof uses their common maximally
mixed marginal and the fact that differences of their adjoints isolate every
matrix unit.
-/

open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey

namespace BellSupport

noncomputable section

variable {A B K : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype K] [DecidableEq K]

def swapMatrix (a b : A) : Matrix A A ℂ :=
  fun r c => if Equiv.swap a b r = c then 1 else 0

omit [Fintype A] in
theorem swapMatrix_adjoint [Fintype A] (a b : A) : (swapMatrix a b)ᴴ = swapMatrix a b := by
  ext r c
  by_cases h : Equiv.swap a b r = c
  · have hc : Equiv.swap a b c = r := Equiv.swap_apply_eq_iff.mpr h.symm
    simp [swapMatrix, Matrix.conjTranspose_apply, h, hc]
  · have hc : Equiv.swap a b c ≠ r :=
      fun hc => h (Equiv.swap_apply_eq_iff.mp hc).symm
    simp [swapMatrix, Matrix.conjTranspose_apply, h, hc]

theorem swapMatrix_sq (a b : A) : swapMatrix a b * swapMatrix a b = 1 := by
  ext r c
  rw [Matrix.mul_apply, Finset.sum_eq_single (Equiv.swap a b r)]
  · simp [swapMatrix, Equiv.swap_apply_self, Matrix.one_apply]
  · intro j hj hne
    simp [swapMatrix, Ne.symm hne]
  · intro h
    exact (h (Finset.mem_univ _)).elim

def phaseSign (a : A) (e : Bool) (r : A) : ℂ :=
  if e then if r = a then -1 else 1 else 1

omit [Fintype A] in
@[simp] theorem phaseSign_star [Fintype A] (a r : A) (e : Bool) :
    star (phaseSign a e r) = phaseSign a e r := by
  cases e <;> by_cases h : r = a <;> simp [phaseSign, h]

omit [Fintype A] in
@[simp] theorem phaseSign_sq [Fintype A] (a r : A) (e : Bool) :
    phaseSign a e r * phaseSign a e r = 1 := by
  cases e <;> by_cases h : r = a <;> simp [phaseSign, h]

def phaseMatrix (a : A) (e : Bool) : Matrix A A ℂ :=
  Matrix.diagonal (phaseSign a e)

theorem phaseMatrix_adjoint (a : A) (e : Bool) :
    (phaseMatrix a e)ᴴ = phaseMatrix a e := by
  ext r c
  by_cases h : r = c
  · subst c
    simp [phaseMatrix, Matrix.conjTranspose_apply]
  · simp [phaseMatrix, Matrix.conjTranspose_apply, Matrix.diagonal, h, Ne.symm h]

theorem phaseMatrix_sq (a : A) (e : Bool) :
    phaseMatrix a e * phaseMatrix a e = 1 := by
  rw [phaseMatrix, Matrix.diagonal_mul_diagonal]
  simp only [phaseSign_sq]
  exact Matrix.diagonal_one

/-- The label `(a,b,e)` selects `swap(a,b)` followed by an optional phase flip at `a`. -/
def bellUnitary (a b : A) (e : Bool) : Matrix A A ℂ :=
  swapMatrix a b * phaseMatrix a e

theorem bellUnitary_adjoint (a b : A) (e : Bool) :
    (bellUnitary a b e)ᴴ = phaseMatrix a e * swapMatrix a b := by
  rw [bellUnitary, Matrix.conjTranspose_mul, phaseMatrix_adjoint, swapMatrix_adjoint]

theorem bellUnitary_adjoint_mul (a b : A) (e : Bool) :
    (bellUnitary a b e)ᴴ * bellUnitary a b e = 1 := by
  rw [bellUnitary_adjoint, bellUnitary]
  calc
    (phaseMatrix a e * swapMatrix a b) * (swapMatrix a b * phaseMatrix a e) =
        phaseMatrix a e * (swapMatrix a b * swapMatrix a b) * phaseMatrix a e := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by rw [swapMatrix_sq, Matrix.mul_one, phaseMatrix_sq]

theorem bellUnitary_mul_adjoint (a b : A) (e : Bool) :
    bellUnitary a b e * (bellUnitary a b e)ᴴ = 1 := by
  rw [bellUnitary_adjoint, bellUnitary]
  calc
    (swapMatrix a b * phaseMatrix a e) * (phaseMatrix a e * swapMatrix a b) =
        swapMatrix a b * (phaseMatrix a e * phaseMatrix a e) * swapMatrix a b := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by rw [phaseMatrix_sq, Matrix.mul_one, swapMatrix_sq]

/-- Explicit tensoring of a reference matrix with the identity on the output. -/
def liftReference (U : Matrix A A ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun p q => if p.2 = q.2 then U p.1 q.1 else 0

omit [DecidableEq A] in
theorem liftReference_mul [DecidableEq A] (U V : Matrix A A ℂ) :
    liftReference (B := B) (U * V) = liftReference U * liftReference V := by
  ext ⟨a,b⟩ ⟨c,d⟩
  by_cases h : b = d
  · subst d
    simp [liftReference, Matrix.mul_apply, Fintype.sum_prod_type]
  · simp [liftReference, Matrix.mul_apply, Fintype.sum_prod_type, h]

omit [Fintype A] [Fintype B] in
theorem liftReference_one [Fintype A] [Fintype B] : liftReference (B := B) (1 : Matrix A A ℂ) = 1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  by_cases h : b = d <;> by_cases hac : a = c <;>
    simp [liftReference, Matrix.one_apply, h, hac, Prod.mk.injEq]

omit [Fintype A] [DecidableEq A] [Fintype B] in
theorem liftReference_adjoint [Fintype A] [DecidableEq A] [Fintype B] (U : Matrix A A ℂ) :
    (liftReference (B := B) U)ᴴ = liftReference Uᴴ := by
  ext p q
  by_cases h : p.2 = q.2
  · simp only [liftReference, Matrix.conjTranspose_apply, if_pos h, if_pos h.symm]
  · simp only [liftReference, Matrix.conjTranspose_apply, if_neg h, if_neg (Ne.symm h),
      map_zero, star_zero]

omit [DecidableEq A] in
theorem liftReference_mulVec [DecidableEq A] (U : Matrix A A ℂ) (v : A × B → ℂ) (a : A) (b : B) :
    (liftReference U *ᵥ v) (a,b) = ∑ c, U a c * v (c,b) := by
  simp [liftReference, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem bellUnitary_adjoint_action (a b r : A) (e : Bool) (v : A × B → ℂ) (s : B) :
    (liftReference (bellUnitary a b e)ᴴ *ᵥ v) (r,s) =
      phaseSign a e r * v (Equiv.swap a b r,s) := by
  rw [liftReference_mulVec, bellUnitary_adjoint]
  simp [phaseMatrix, Matrix.diagonal_mul, swapMatrix]

/-- A single reference coordinate carrying an arbitrary output vector. -/
def fiber (a : A) (v : B → ℂ) : A × B → ℂ :=
  fun p => if p.1 = a then v p.2 else 0

theorem adjoint_difference_fiber (a b : A) (v : A × B → ℂ) :
    (1 / 2 : ℂ) •
        (liftReference (bellUnitary a b false)ᴴ *ᵥ v -
         liftReference (bellUnitary a b true)ᴴ *ᵥ v) =
      fiber a (fun c => v (b,c)) := by
  funext p
  rcases p with ⟨r,s⟩
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, bellUnitary_adjoint_action]
  by_cases h : r = a
  · subst r
    simp [phaseSign, fiber, Equiv.swap_apply_left]
    ring
  · simp [phaseSign, fiber, h]

omit [DecidableEq K] in
theorem pullback_mem_range [DecidableEq K] (W : Matrix (A × B) K ℂ) (v : A × B → ℂ)
    (a b : A) (e : Bool)
    (hv : v ∈ LinearMap.range ((liftReference (bellUnitary a b e)) * W).mulVecLin) :
    liftReference (bellUnitary a b e)ᴴ *ᵥ v ∈ LinearMap.range W.mulVecLin := by
  rcases hv with ⟨x,hx⟩
  refine ⟨x, ?_⟩
  change W *ᵥ x = liftReference (bellUnitary a b e)ᴴ *ᵥ v
  change (liftReference (bellUnitary a b e) * W) *ᵥ x = v at hx
  rw [← hx, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← liftReference_mul,
    bellUnitary_adjoint_mul, liftReference_one, Matrix.one_mul]

/-- A zero product block in the original range forces a zero intersection of all
the finitely many rotated ranges. -/
theorem common_rotated_range_zero (W : Matrix (A × B) K ℂ)
    (hproduct : ∀ v : B → ℂ,
      (∀ a, fiber a v ∈ LinearMap.range W.mulVecLin) → v = 0)
    (v : A × B → ℂ)
    (hv : ∀ (a b : A) (e : Bool),
      v ∈ LinearMap.range ((liftReference (bellUnitary a b e)) * W).mulVecLin) :
    v = 0 := by
  have hf : ∀ a b : A, fiber a (fun c => v (b,c)) ∈ LinearMap.range W.mulVecLin := by
    intro a b
    have h0 := pullback_mem_range W v a b false (hv a b false)
    have h1 := pullback_mem_range W v a b true (hv a b true)
    have h := (LinearMap.range W.mulVecLin).smul_mem (1 / 2 : ℂ)
      ((LinearMap.range W.mulVecLin).sub_mem h0 h1)
    rwa [adjoint_difference_fiber] at h
  have hr : ∀ b : A, (fun c => v (b,c)) = 0 := fun b => hproduct _ (fun a => hf a b)
  funext p
  exact congrFun (hr p.1) p.2

/-- The actual rank-one positive matrix of a complex vector. -/
def outer (v : B → ℂ) : Matrix B B ℂ := fun r c => v r * star (v c)

omit [DecidableEq B] in
theorem outer_posSemidef [DecidableEq B] (v : B → ℂ) : (outer v).PosSemidef := by
  change (KrausSupport.rankOne v).PosSemidef
  exact KrausSupport.rankOne_posSemidef v

omit [DecidableEq A] in
theorem partialTrace_outer_matrix [DecidableEq A] (U : Matrix A A ℂ) :
    partialTraceMatrix (outer (fun p : A × A => U p.1 p.2)) = U * Uᴴ := by
  ext r s
  simp [partialTraceMatrix, outer, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- A normalized Bell preparation, specified as an actual density matrix. -/
def bellMatrix (U : Matrix A A ℂ) : Matrix (A × A) (A × A) ℂ :=
  ((Fintype.card A : ℝ)⁻¹) • outer (fun p : A × A => U p.1 p.2)

theorem bellMatrix_posSemidef (U : Matrix A A ℂ) : (bellMatrix U).PosSemidef := by
  exact posSemidef_real_smul _ (outer_posSemidef _) _ (inv_nonneg.mpr (by positivity))

theorem bellMatrix_marginal (U : Matrix A A ℂ) (hU : U * Uᴴ = 1) :
    partialTraceMatrix (bellMatrix U) = (Fintype.card A : ℝ)⁻¹ • (1 : Matrix A A ℂ) := by
  rw [bellMatrix, partialTraceMatrix_smul, partialTrace_outer_matrix, hU]

theorem bellMatrix_trace [Nonempty A] (U : Matrix A A ℂ) (hU : U * Uᴴ = 1) :
    (bellMatrix U).trace = 1 := by
  rw [← partialTraceMatrix_trace, bellMatrix_marginal U hU, Matrix.trace_smul,
    Matrix.trace_one]
  have hc : (Fintype.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simpa only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast] using
    inv_mul_cancel₀ hc

def bellDensity [Nonempty A] (a b : A) (e : Bool) : Density (A × A) where
  mat := bellMatrix (bellUnitary a b e)
  positive := bellMatrix_posSemidef _
  normalized := bellMatrix_trace _ (bellUnitary_mul_adjoint a b e)

theorem bellDensity_common_marginal [Nonempty A] (a b c d : A) (e f : Bool) :
    partialTraceMatrix (bellDensity a b e).mat =
      partialTraceMatrix (bellDensity c d f).mat := by
  change partialTraceMatrix (bellMatrix (bellUnitary a b e)) =
    partialTraceMatrix (bellMatrix (bellUnitary c d f))
  rw [bellMatrix_marginal _ (bellUnitary_mul_adjoint a b e),
    bellMatrix_marginal _ (bellUnitary_mul_adjoint c d f)]

/-- The normalized Bell vector corresponding to a unitary matrix. -/
def bellKet (U : Matrix A A ℂ) : A × A → ℂ :=
  fun p => (Real.sqrt (Fintype.card A : ℝ) : ℂ)⁻¹ * U p.1 p.2

omit [DecidableEq A] in
theorem bellKet_outer [DecidableEq A] (U : Matrix A A ℂ) : outer (bellKet U) = bellMatrix U := by
  have hs : (Real.sqrt (Fintype.card A : ℝ) : ℂ) *
      (Real.sqrt (Fintype.card A : ℝ) : ℂ) = (Fintype.card A : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (show (0 : ℝ) ≤ Fintype.card A by positivity)
  ext p q
  simp only [outer, bellKet, bellMatrix, Matrix.smul_apply, Complex.real_smul,
    Complex.star_def, map_mul, map_inv₀, Complex.conj_ofReal,
    Complex.ofReal_inv, Complex.ofReal_natCast]
  calc
    (↑(Real.sqrt ↑(Fintype.card A)))⁻¹ * U p.1 p.2 *
        ((↑(Real.sqrt ↑(Fintype.card A)))⁻¹ * star (U q.1 q.2)) =
      ((↑(Real.sqrt ↑(Fintype.card A)))⁻¹ *
        (↑(Real.sqrt ↑(Fintype.card A)))⁻¹) * (U p.1 p.2 * star (U q.1 q.2)) := by ring
    _ = (Fintype.card A : ℂ)⁻¹ * (U p.1 p.2 * star (U q.1 q.2)) := by
      rw [← mul_inv, hs]

theorem bellKet_normalized [Nonempty A] (U : Matrix A A ℂ) (hU : U * Uᴴ = 1) :
    ∑ p, bellKet U p * star (bellKet U p) = 1 := by
  change (outer (bellKet U)).trace = 1
  rw [bellKet_outer, bellMatrix_trace U hU]

omit [DecidableEq A] [Fintype K] [DecidableEq K] in
theorem rotatedKraus_apply [DecidableEq A] [Fintype K] [DecidableEq K] (L : K → Matrix B A ℂ) (U : Matrix A A ℂ)
    (p : A × B) (i : K) :
    (liftReference (B := B) U * KrausSupport.krausVectors L) p i =
      ∑ a, U p.1 a * L i p.2 a := by
  simp [liftReference, KrausSupport.krausVectors, Matrix.mul_apply,
    Fintype.sum_prod_type]

/-- Applying a Kraus channel to an actual Bell preparation produces the rotated
Kraus Gram matrix, with its required normalization. -/
theorem amplified_bell_gram (L : K → Matrix B A ℂ) (U : Matrix A A ℂ) :
    amplify (GeneralKraus.krausMap L) (bellMatrix U) =
      (Fintype.card A : ℝ)⁻¹ •
        ((liftReference (B := B) U * KrausSupport.krausVectors L) *
          (liftReference (B := B) U * KrausSupport.krausVectors L)ᴴ) := by
  rw [bellMatrix, amplify_real_smul]
  congr 1
  ext p q
  let Xpq : Matrix A A ℂ := fun a b => U p.1 a * star (U q.1 b)
  change GeneralKraus.krausMap L Xpq p.2 q.2 = _
  rw [GeneralKraus.krausMap_apply]
  conv_rhs => rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, rotatedKraus_apply]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [Xpq, outer,
    Complex.star_def, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem bell_output_range_le_rotated (L : K → Matrix B A ℂ) (U : Matrix A A ℂ) :
    LinearMap.range (amplify (GeneralKraus.krausMap L) (bellMatrix U)).mulVecLin ≤
      LinearMap.range (liftReference (B := B) U * KrausSupport.krausVectors L).mulVecLin := by
  intro v hv
  rcases hv with ⟨x, hx⟩
  let V := liftReference (B := B) U * KrausSupport.krausVectors L
  refine ⟨(Fintype.card A : ℝ)⁻¹ • (Vᴴ *ᵥ x), ?_⟩
  change V *ᵥ ((Fintype.card A : ℝ)⁻¹ • (Vᴴ *ᵥ x)) = v
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec]
  change ((Fintype.card A : ℝ)⁻¹ • (V * Vᴴ)) *ᵥ x = v
  rw [← amplified_bell_gram L U]
  exact hx

/-- If a CPTP map has no positive replacer minorant, then this explicit finite
family of actual output states has zero common support. -/
theorem bell_output_common_range_zero [Nonempty A] (N : QuantumChannel A B)
    (L : K → Matrix B A ℂ) (hL : N.map = GeneralKraus.krausMap L)
    (hN : ¬ GeneralContraction.HasPositiveReplacer N) (v : A × B → ℂ)
    (hv : ∀ (a b : A) (e : Bool),
      v ∈ LinearMap.range (amplify N.map (bellDensity a b e).mat).mulVecLin) :
    v = 0 := by
  have hproduct : ∀ w : B → ℂ,
      (∀ a, fiber a w ∈ LinearMap.range (KrausSupport.krausVectors L).mulVecLin) → w = 0 := by
    intro w hw
    apply KrausSupport.product_slice_zero_of_no_replacer N L hL hN w
    change ∀ a, fiber a w ∈ (KrausSupport.krausVectors L).mulVecLin.range
    exact hw
  apply common_rotated_range_zero (KrausSupport.krausVectors L) hproduct v
  intro a b e
  apply bell_output_range_le_rotated L (bellUnitary a b e)
  simpa only [bellDensity, hL] using hv a b e

end
end BellSupport
