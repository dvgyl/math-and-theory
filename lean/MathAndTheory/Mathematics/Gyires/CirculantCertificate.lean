module

public import MathAndTheory.Mathematics.Gyires.PermanentPermutation
public import MathAndTheory.Mathematics.Gyires.DimensionConstant
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.Gyires

namespace CirculantCertificate

variable {n : ℕ}

def circulant {R : Type*} (w : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => w (j - i)

theorem circulant_normal (w : Fin n → ℝ) :
    circulant w * (circulant w).transpose =
      (circulant w).transpose * circulant w := by
  change (Matrix.circulant w).transpose * Matrix.circulant w =
    Matrix.circulant w * (Matrix.circulant w).transpose
  rw [Matrix.Fin.transpose_circulant]
  exact Matrix.Fin.circulant_mul_comm _ _

theorem circulant_affine [NeZero n] (e : Fin n ≃+ Fin n) (b : Fin n)
    (w : Fin n → ℝ) :
    circulant (fun i => w (e i + b)) =
      (circulant w).submatrix e.toEquiv (e.toEquiv.trans (Equiv.addRight b)) := by
  ext i j
  change w (e (j - i) + b) = w ((e j + b) - e i)
  rw [map_sub]
  congr 1
  abel

theorem strong_deficit_affine [NeZero n] (e : Fin n ≃+ Fin n) (b : Fin n)
    (w : Fin n → ℝ) :
    (n ^ n : ℕ) * (circulant (fun i => w (e i + b))).permanent ^ 2 -
        (n.factorial : ℕ) * (circulant (fun i => w (e i + b)) *
          (circulant (fun i => w (e i + b))).transpose).permanent =
      (n ^ n : ℕ) * (circulant w).permanent ^ 2 -
        (n.factorial : ℕ) * (circulant w * (circulant w).transpose).permanent := by
  rw [circulant_affine]
  rw [submatrix_perm_mul_transpose]
  simp only [permanent_submatrix_perm]

def gapWeights {R : Type*} [AddCommMonoid R]
    (σ : Equiv.Perm (Fin n)) (z : Fin n → R) (i : Fin n) : R :=
  ∑ j ∈ Finset.Iic (σ.symm i), z j

noncomputable def gapMatrix (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℤ) :=
  circulant (gapWeights σ MvPolynomial.X)

noncomputable def strongPolynomial (σ : Equiv.Perm (Fin n)) :
    MvPolynomial (Fin n) ℤ :=
  (n ^ n : ℕ) * (gapMatrix σ).permanent ^ 2 -
    (n.factorial : ℕ) * (gapMatrix σ * (gapMatrix σ).transpose).permanent

theorem map_permanent {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (A : Matrix (Fin n) (Fin n) R) :
    f A.permanent = (A.map f).permanent := by
  simp only [Matrix.permanent, map_sum, map_prod, Matrix.map_apply]

theorem eval_gapMatrix (σ : Equiv.Perm (Fin n)) (z : Fin n → ℝ) :
    (gapMatrix σ).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) z) =
      circulant (gapWeights σ z) := by
  ext i j
  simp [gapMatrix, circulant, gapWeights]

theorem eval_strongPolynomial (σ : Equiv.Perm (Fin n)) (z : Fin n → ℝ) :
    MvPolynomial.eval₂Hom (Int.castRingHom ℝ) z (strongPolynomial σ) =
      (n ^ n : ℕ) * (circulant (gapWeights σ z)).permanent ^ 2 -
        (n.factorial : ℕ) *
          (circulant (gapWeights σ z) * (circulant (gapWeights σ z)).transpose).permanent := by
  simp only [strongPolynomial, map_sub, map_mul, map_pow, map_natCast,
    map_permanent, Matrix.map_mul, Matrix.transpose_map,
    eval_gapMatrix]

theorem eval_nonneg_of_coeff_nonneg (P : MvPolynomial (Fin n) ℤ)
    (hP : ∀ d ∈ P.support, 0 ≤ P.coeff d)
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ MvPolynomial.eval₂Hom (Int.castRingHom ℝ) z P := by
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  apply Finset.sum_nonneg
  intro d hd
  apply mul_nonneg
  · change (0 : ℝ) ≤ (P.coeff d : ℤ)
    exact_mod_cast hP d hd
  · exact Finset.prod_nonneg (fun i _ => pow_nonneg (hz i) _)

theorem strong_gap_of_coeff_nonneg (σ : Equiv.Perm (Fin n))
    (hP : ∀ d ∈ (strongPolynomial σ).support, 0 ≤ (strongPolynomial σ).coeff d)
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (n.factorial : ℕ) *
        (circulant (gapWeights σ z) * (circulant (gapWeights σ z)).transpose).permanent ≤
      (n ^ n : ℕ) * (circulant (gapWeights σ z)).permanent ^ 2 := by
  have h := eval_nonneg_of_coeff_nonneg (strongPolynomial σ) hP z hz
  rw [eval_strongPolynomial] at h
  exact sub_nonneg.mp h

theorem exists_gapWeights (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ σ : Equiv.Perm (Fin n), ∃ z : Fin n → ℝ,
      (∀ i, 0 ≤ z i) ∧ gapWeights σ z = w := by
  classical
  let σ := Tuple.sort w
  have hmono : Monotone (w ∘ σ) := Tuple.monotone_sort w
  let f : Fin (n + 1) → ℝ := Fin.cases 0 (w ∘ σ)
  let z : Fin n → ℝ := fun i => f i.succ - f i.castSucc
  have hz : ∀ i, 0 ≤ z i := by
    intro i
    cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [z, f] using hw (σ 0)
      · change 0 ≤ w (σ j.succ) - w (σ j.castSucc)
        exact sub_nonneg.mpr (hmono (by change j.val ≤ j.val + 1; omega))
  refine ⟨σ, z, hz, ?_⟩
  funext i
  dsimp only [gapWeights, z]
  rw [Fin.sum_Iic_sub]
  simp [f]

theorem strong_circulant_of_coeff_nonneg
    (hP : ∀ σ : Equiv.Perm (Fin n),
      ∀ d ∈ (strongPolynomial σ).support, 0 ≤ (strongPolynomial σ).coeff d)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    dimensionConstant n * (circulant w * (circulant w).transpose).permanent ≤
      (circulant w).permanent ^ 2 := by
  obtain ⟨σ, z, hz, heq⟩ := exists_gapWeights w hw
  have h := strong_gap_of_coeff_nonneg σ (hP σ) z hz
  rw [heq] at h
  have hn : (0 : ℝ) < (n : ℝ) ^ n := by
    cases n with
    | zero => norm_num
    | succ k => positivity
  rw [dimensionConstant, div_mul_eq_mul_div, div_le_iff₀ hn]
  simpa only [Nat.cast_pow, mul_comm] using h

theorem gyires_circulant_of_coeff_nonneg
    (hP : ∀ σ : Equiv.Perm (Fin n),
      ∀ d ∈ (strongPolynomial σ).support, 0 ≤ (strongPolynomial σ).coeff d)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    dimensionConstant n *
      ((circulant w * (circulant w).transpose).permanent +
        ((circulant w).transpose * circulant w).permanent +
        2 * (circulant w * circulant w).permanent) ≤
      4 * (circulant w).permanent ^ 2 := by
  have h := strong_circulant_of_coeff_nonneg hP w hw
  exact GyiresCirculant5.gyires_of_strong _ _ (dimensionConstant_nonneg n) h
    (by rw [← circulant_normal]; exact h)

end CirculantCertificate

end MathAndTheory.Gyires
