/- Reused from the existing Milne formalization in the user workspace.
   Provenance and original SHA256 are recorded in QuantumPrior/PROVENANCE.json.
   Only local import module prefixes were adapted; proof statements and bodies are unchanged. -/
import QuantumPrior.MilneCorrelation

/-!
# A rank-independent matrix inequality for two-qubit Bloch data

All positivity assumptions below concern the actual complex 4 by 4 density
matrix `blochState a b T`. The proof conjugates its full transpose by an
explicit local spin matrix; no inverse and no full-rank premise occurs.

For a canonical state (b = 0), the result is
  2 (T T^t - a a^t) + (1 + |a|^2 - ||T||_F^2) I >= 0.
In the radial direction a = c n, |n| = 1, this yields
  ||T||_F^2 <= 1 - c^2 + 2 |T^t n|^2.
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

/-- Positive matrices have nonnegative real trace product, including singular
matrices. The factorization is supplied by Mathlib's PSD theorem. -/
theorem geometry_trace_product_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  obtain ⟨X, rfl⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hA
  have h := psd_trace_nonneg (hB.mul_mul_conjTranspose_same X)
  rw [Matrix.trace_mul_cycle Xᴴ X B, Matrix.trace_mul_cycle B Xᴴ X]
  exact h

/-- `(n.sigma sigma_y) tensor sigma_y`, with n not necessarily normalized. -/
def geometryFlipMatrix (n : V3) : CMatrix := fun i j =>
  (spin n * pauli 1) i.1 j.1 * pauli 1 i.2 j.2

/-- The full transpose followed by local conjugation. -/
def geometryFlip (n : V3) (M : CMatrix) : CMatrix :=
  geometryFlipMatrix n * M.transpose * (geometryFlipMatrix n)ᴴ

theorem geometryFlip_psd (n : V3) {M : CMatrix} (hM : M.PosSemidef) :
    (geometryFlip n M).PosSemidef := by
  exact hM.transpose.mul_mul_conjTranspose_same (geometryFlipMatrix n)

/-- Exact Pauli polynomial identity. Normalizing n is unnecessary. -/
theorem geometry_spinflip_identity (a b n : V3) (T : T3) :
    4 * (Matrix.trace
      (blochState a b T * geometryFlip n (blochState a b T))).re =
    vSq n * (1 + vSq a - vSq b - tSq T) -
      2 * (vDot a n)^2 + 2 * vSq (ttVec T n) := by
  simp [geometryFlip, geometryFlipMatrix, blochState, spin, pauli, pauliZ,
    onAlice, onBob, vSq, vDot, tSq, ttVec,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Complex.star_def,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, pow_two]
  ring

/-- Homogeneous geometric inequality for every actual positive two-qubit
Bloch matrix. This is valid at every state rank and every marginal rank. -/
theorem geometry_directional (a b n : V3) (T : T3)
    (hM : (blochState a b T).PosSemidef) :
    0 ≤ vSq n * (1 + vSq a - vSq b - tSq T) -
      2 * (vDot a n)^2 + 2 * vSq (ttVec T n) := by
  rw [← geometry_spinflip_identity]
  exact mul_nonneg (by norm_num) (geometry_trace_product_nonneg hM (geometryFlip_psd n hM))

/-- A unit-direction version for an arbitrary state. -/
theorem geometry_unit_direction (a b n : V3) (T : T3)
    (hM : (blochState a b T).PosSemidef) (hn : vSq n = 1) :
    tSq T ≤ 1 + vSq a - vSq b - 2 * (vDot a n)^2 +
      2 * vSq (ttVec T n) := by
  have h := geometry_directional a b n T hM
  rw [hn] at h
  linarith

/-- The real symmetric matrix of the homogeneous geometric quadratic form. -/
def geometryMatrix (a b : V3) (T : T3) : T3 := fun i j =>
  (if i = j then 1 + vSq a - vSq b - tSq T else 0) +
    2 * ((∑ k, T i k * T j k) - a i * a j)

theorem geometryMatrix_form (a b n : V3) (T : T3) :
    dotProduct n (geometryMatrix a b T *ᵥ n) =
      vSq n * (1 + vSq a - vSq b - tSq T) -
        2 * (vDot a n)^2 + 2 * vSq (ttVec T n) := by
  simp [dotProduct, Matrix.mulVec, geometryMatrix, vSq, vDot, tSq, ttVec,
    Fin.sum_univ_three, pow_two]
  ring

/-- The full 3 by 3 positive-semidefinite inequality. -/
theorem geometry_matrix_psd (a b : V3) (T : T3)
    (hM : (blochState a b T).PosSemidef) :
    (geometryMatrix a b T).PosSemidef := by
  refine ⟨?_, ?_⟩
  · change (geometryMatrix a b T)ᴴ = geometryMatrix a b T
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, geometryMatrix]
    have hh : (∑ k, T j k * T i k) = ∑ k, T i k * T j k := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    have he : (j = i) = (i = j) := propext eq_comm
    simp only [hh, he]
    ring
  · intro n
    simpa only [star_trivial, geometryMatrix_form] using geometry_directional a b n T hM

/-- The radial skew bound for a canonical state with centre c n. -/
theorem geometry_radial (c : ℝ) (n : V3) (T : T3)
    (hn : vSq n = 1)
    (hM : (blochState (c • n) 0 T).PosSemidef) :
    tSq T ≤ 1 - c^2 + 2 * vSq (ttVec T n) := by
  have h := geometry_unit_direction (c • n) 0 n T hM hn
  have hs : vSq (c • n) = c^2 := by
    calc
      vSq (c • n) = c^2 * vSq n := by
        simp [vSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
      _ = c^2 := by rw [hn]; ring
  have hd : vDot (c • n) n = c := by
    simp only [vDot, Pi.smul_apply, smul_eq_mul]
    calc
      ∑ i, c * n i * n i = c * vSq n := by
        simp [vSq, Finset.mul_sum, pow_two, mul_assoc]
      _ = c := by rw [hn]; ring
  have hz : vSq (0 : V3) = 0 := by simp [vSq]
  rw [hs, hd, hz] at h
  linarith

#print axioms geometry_directional
#print axioms geometry_matrix_psd
#print axioms geometry_radial

end Milne
