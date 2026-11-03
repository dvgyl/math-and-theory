import UnilateralCHSH
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NoncommRing

/-!
Actual complex two-qubit matrices used for the new positivity certificate.
The Fano representation and spin flip are defined explicitly.  Positivity
below means Mathlib's matrix positive semidefiniteness, not a substitute
scalar condition.  No hypothesis asserting the desired Gram bound is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 16000

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace UnilateralCHSH.Quantum

abbrev Q := Fin 2
abbrev QQ := Q × Q
abbrev State := Matrix QQ QQ ℂ
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

def pauli : Fin 3 → Matrix Q Q ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

def onAlice (F : Matrix Q Q ℂ) : State :=
  fun i j => if i.2 = j.2 then F i.1 j.1 else 0

def onBob (F : Matrix Q Q ℂ) : State :=
  fun i j => if i.1 = j.1 then F i.2 j.2 else 0

def blochState (a b : Vec) (T : Mat3) : State := fun i j =>
  (1/4:ℂ) * ((if i = j then 1 else 0) +
    (∑ k, (a k : ℂ) * onAlice (pauli k) i j) +
    (∑ k, (b k : ℂ) * onBob (pauli k) i j) +
    ∑ k, ∑ l, (T k l : ℂ) * pauli k i.1 j.1 * pauli l i.2 j.2)

def canonical (c : Vec) (D : Mat3) : State := blochState 0 c D

def spinFlipMatrix : State := fun i j => pauli 1 i.1 j.1 * pauli 1 i.2 j.2

def spinFlip (ρ : State) : State := spinFlipMatrix * ρᵀ * spinFlipMatrixᴴ

def complexSpin (z : Fin 3 → ℂ) : Matrix Q Q ℂ :=
  !![z 2, z 0 - Complex.I*z 1; z 0 + Complex.I*z 1, -z 2]

def spinPair (n v : Vec) : State :=
  onAlice (complexSpin (fun i => (n i : ℂ) + Complex.I*(v i : ℂ)))

def covariance (D : Mat3) : Mat3 := matProduct D D.transpose

def purityMargin (c : Vec) (D : Mat3) : ℝ :=
  (traceThree (covariance D) - normSq c - 1)/2

theorem psd_diag_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (i : ι) : 0 ≤ (M i i).re := by
  have hs : star (Pi.single i (1:ℂ) : ι → ℂ) = (Pi.single i (1:ℂ) : ι → ℂ) := by
    ext j
    by_cases h : j = i <;> simp [Pi.star_apply, Pi.single_apply, h]
  simpa [hs] using hM.re_dotProduct_nonneg (Pi.single i 1)

theorem psd_trace_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.PosSemidef) : 0 ≤ (Matrix.trace M).re := by
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => psd_diag_nonneg hM i

theorem trace_product_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A*B)).re := by
  have h := hA.mul_mul_conjTranspose_same hB.sqrt
  rw [hB.posSemidef_sqrt.1.eq] at h
  have ht : Matrix.trace (hB.sqrt * A * hB.sqrt) = Matrix.trace (A*B) := by
    rw [Matrix.trace_mul_cycle, hB.sqrt_mul_self]
    exact Matrix.trace_mul_comm B A
  rw [← ht]
  exact psd_trace_nonneg h

theorem spinFlip_psd {ρ : State} (hρ : ρ.PosSemidef) : (spinFlip ρ).PosSemidef :=
  hρ.transpose.mul_mul_conjTranspose_same spinFlipMatrix

theorem spin_pair_trace_nonneg {ρ : State} (hρ : ρ.PosSemidef) (n v : Vec) :
    0 ≤ (Matrix.trace (ρ * ((spinPair n v)ᴴ * spinFlip ρ * spinPair n v))).re :=
  trace_product_nonneg hρ ((spinFlip_psd hρ).conjTranspose_mul_mul_same (spinPair n v))

theorem canonical_trace (c : Vec) (D : Mat3) : Matrix.trace (canonical c D) = 1 := by
  apply Complex.ext <;>
    simp [canonical, blochState, onAlice, onBob, pauli,
      Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  all_goals ring

theorem canonical_spinflip_gram_identity (c n v : Vec) (D : Mat3) :
    2 * (Matrix.trace (canonical c D *
      ((spinPair n v)ᴴ * spinFlip (canonical c D) * spinPair n v))).re =
      quad (shift (covariance D) (-normSq c)) n +
      quad (shift (covariance D) (-normSq c)) v +
      2*dot v (matVec (crossMatrix (matVec D c)) n) -
      purityMargin c D * (normSq n + normSq v) := by
  simp [canonical, blochState, spinFlip, spinFlipMatrix, spinPair, complexSpin,
    onAlice, onBob, pauli, covariance, purityMargin, traceThree, shift,
    quad, matVec, matProduct, crossMatrix, normSq, dot,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

theorem physical_spinflip_gram_bound (c n v : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef) :
    purityMargin c D * (normSq n + normSq v) ≤
      quad (shift (covariance D) (-normSq c)) n +
      quad (shift (covariance D) (-normSq c)) v +
      2*dot v (matVec (crossMatrix (matVec D c)) n) := by
  have h := spin_pair_trace_nonneg hρ n v
  have he := canonical_spinflip_gram_identity c n v D
  linarith

end UnilateralCHSH.Quantum
