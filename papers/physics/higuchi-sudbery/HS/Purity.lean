import HS.Definitions
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open scoped BigOperators ComplexConjugate

set_option autoImplicit false

namespace HS

/-- For each qubit, the indices in its zero slice, with the other bits in order. -/
def zeroSlice : Fin 4 → Fin 8 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 1, 2, 3, 8, 9, 10, 11],
    ![0, 1, 4, 5, 8, 9, 12, 13],
    ![0, 2, 4, 6, 8, 10, 12, 14]]

/-- The corresponding indices in the one slice. -/
def oneSlice : Fin 4 → Fin 8 → Fin 16 :=
  ![![8, 9, 10, 11, 12, 13, 14, 15],
    ![4, 5, 6, 7, 12, 13, 14, 15],
    ![2, 3, 6, 7, 10, 11, 14, 15],
    ![1, 3, 5, 7, 9, 11, 13, 15]]

/-- Half of the four-qubit spin-flip bilinear form. -/
def spinFlipH {R : Type*} [CommRing R] (z : Fin 16 → R) : R :=
  z 0 * z 15 - z 1 * z 14 - z 2 * z 13 + z 3 * z 12 -
    z 4 * z 11 + z 5 * z 10 + z 6 * z 9 - z 7 * z 8

def formalNorm {R : Type*} [CommRing R] (z w : Fin 16 → R) : R :=
  ∑ i, z i * w i

def formalBlochD {R : Type*} [CommRing R] (s : Fin 4) (z w : Fin 16 → R) : R :=
  (∑ i, z (zeroSlice s i) * w (zeroSlice s i)) -
    ∑ i, z (oneSlice s i) * w (oneSlice s i)

def formalBlochC {R : Type*} [CommRing R] (s : Fin 4) (z w : Fin 16 → R) : R :=
  ∑ i, z (zeroSlice s i) * w (oneSlice s i)

def formalBlochC' {R : Type*} [CommRing R] (s : Fin 4) (z w : Fin 16 → R) : R :=
  ∑ i, z (oneSlice s i) * w (zeroSlice s i)

def formalPuritySum {R : Type*} [CommRing R] (z w : Fin 16 → R) : R :=
  ∑ cut : Fin 3,
    Matrix.trace ((flatten cut z * (flatten cut w).transpose) *
      (flatten cut z * (flatten cut w).transpose))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The quartic identity behind the four-qubit purity lower bound.
The variables and their formal conjugates are independent in this identity. -/
theorem formal_purity_identity {R : Type*} [CommRing R] (z w : Fin 16 → R) :
    2 * formalPuritySum z w =
      2 * formalNorm z w ^ 2 +
        (∑ s : Fin 4, (formalBlochD s z w ^ 2 +
          4 * formalBlochC s z w * formalBlochC' s z w)) +
        4 * spinFlipH z * spinFlipH w := by
  simp [formalPuritySum, formalNorm, formalBlochD, formalBlochC, formalBlochC',
    spinFlipH, zeroSlice, oneSlice, flatten, flattenIndex, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
  ring

def blochD (s : Fin 4) (z : Fin 16 → ℂ) : ℝ :=
  (∑ i, Complex.normSq (z (zeroSlice s i))) -
    ∑ i, Complex.normSq (z (oneSlice s i))

def blochC (s : Fin 4) (z : Fin 16 → ℂ) : ℂ :=
  ∑ i, z (zeroSlice s i) * conj (z (oneSlice s i))

theorem formalNorm_conj (z : Fin 16 → ℂ) :
    formalNorm z (fun i => conj (z i)) = (stateNormSq z : ℂ) := by
  simp [formalNorm, stateNormSq, Complex.mul_conj]

theorem formalBlochD_conj (s : Fin 4) (z : Fin 16 → ℂ) :
    formalBlochD s z (fun i => conj (z i)) = (blochD s z : ℂ) := by
  simp [formalBlochD, blochD, Complex.mul_conj]

theorem formalBlochC_conj (s : Fin 4) (z : Fin 16 → ℂ) :
    formalBlochC s z (fun i => conj (z i)) = blochC s z := rfl

theorem formalBlochC'_conj (s : Fin 4) (z : Fin 16 → ℂ) :
    formalBlochC' s z (fun i => conj (z i)) = conj (blochC s z) := by
  simp [formalBlochC', blochC, map_sum, mul_comm]

theorem spinFlipH_conj (z : Fin 16 → ℂ) :
    spinFlipH (fun i => conj (z i)) = conj (spinFlipH z) := by
  simp [spinFlipH]

theorem formalPuritySum_conj_re (z : Fin 16 → ℂ) :
    (formalPuritySum z (fun i => conj (z i))).re = puritySum z := by
  have hflat (cut : Fin 3) :
      (flatten cut (fun i => conj (z i))).transpose = (flatten cut z).conjTranspose := by
    ext i j : 2
    rfl
  simp [formalPuritySum, puritySum, reduced, hflat]

/-- Exact sum-of-squares expression for the excess balanced purity. -/
theorem purity_identity (z : Fin 16 → ℂ) :
    2 * puritySum z = 2 * stateNormSq z ^ 2 +
      (∑ s : Fin 4, (blochD s z ^ 2 + 4 * Complex.normSq (blochC s z))) +
      4 * Complex.normSq (spinFlipH z) := by
  have h := formal_purity_identity z (fun i => conj (z i))
  have hcomplex : 2 * formalPuritySum z (fun i => conj (z i)) =
      ((2 * stateNormSq z ^ 2 +
        (∑ s : Fin 4, (blochD s z ^ 2 + 4 * Complex.normSq (blochC s z))) +
        4 * Complex.normSq (spinFlipH z) : ℝ) : ℂ) := by
    rw [h]
    simp [formalNorm_conj, formalBlochD_conj, formalBlochC_conj,
      formalBlochC'_conj, spinFlipH_conj, mul_assoc, Complex.mul_conj]
  have hr := congrArg Complex.re hcomplex
  simpa [pow_two, Complex.mul_re, formalPuritySum_conj_re] using hr

/-- Every unnormalized four-qubit vector obeys the sharp balanced purity bound. -/
theorem puritySum_lower (z : Fin 16 → ℂ) : stateNormSq z ^ 2 ≤ puritySum z := by
  have hs : 0 ≤ ∑ s : Fin 4, (blochD s z ^ 2 + 4 * Complex.normSq (blochC s z)) := by
    exact Finset.sum_nonneg fun s _ =>
      add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  have hh := Complex.normSq_nonneg (spinFlipH z)
  linarith [purity_identity z]

theorem puritySum_lower_normalized (z : Fin 16 → ℂ) (hn : stateNormSq z = 1) :
    1 ≤ puritySum z := by
  simpa [hn] using puritySum_lower z

end HS
