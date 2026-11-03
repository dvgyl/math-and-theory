import EllipsoidCounterexample

namespace EllipsoidCounterexample

noncomputable section

open Matrix Complex
open scoped ComplexConjugate

/-!
The finer witness in this second counterexample has the same negative chirality
and a strictly smaller ellipsoid. Thus chirality-preserving containment does not
rescue the sufficiency direction of the proposed equivalence.
-/

def correlationMatrix (A : M4) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => blochCoefficients A i.succ j.succ

lemma W_correlationMatrix (p : ℝ) : correlationMatrix (W p) =
    !![1, 0, 0; 0, 1, 0; 0, 0, 2 * p - 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [correlationMatrix, W_blochCoefficients]

lemma W_correlation_det (p : ℝ) : Matrix.det (correlationMatrix (W p)) = 2 * p - 1 := by
  rw [W_correlationMatrix]
  simp [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail]

def shapeMatrix (A : M4) : Matrix (Fin 3) (Fin 3) ℝ :=
  correlationMatrix A * (correlationMatrix A).transpose

theorem exact_shape_matrices :
    shapeMatrix (W (1 / 4)) = !![1, 0, 0; 0, 1, 0; 0, 0, 1 / 4] ∧
    shapeMatrix (W (3 / 4)) = !![1, 0, 0; 0, 1, 0; 0, 0, 1 / 4] := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [shapeMatrix, W_correlationMatrix, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail]

theorem same_negative_chirality :
    Matrix.det (correlationMatrix (W (1 / 4))) = -(1 / 2) ∧
    Matrix.det (correlationMatrix (W (1 / 3))) = -(1 / 3) := by
  norm_num [W_correlation_det]

theorem third_classD : ClassD (W (1 / 3)) := by
  refine ⟨W_witness (by norm_num) (by norm_num),
    partialTranspose_witness (by norm_num) (by norm_num), ?_, ?_⟩ <;>
    norm_num [det_W, det_partialTranspose_W, Complex.div_re, Complex.div_im]

theorem same_chirality_subtraction :
    W (1 / 4) = (3 / 4 : ℂ) • W (1 / 3) + (1 / 4 : ℂ) • Pplus := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [W, Pplus]

lemma third_expect_decomposition (ρ : M4) :
    expect (W (1 / 4)) ρ = 3 * expect (W (1 / 3)) ρ / 4 + expect Pplus ρ / 4 := by
  simp [expect, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    W, Pplus, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

theorem third_finer : Finer (W (1 / 3)) (W (1 / 4)) := by
  intro ρ hρ h
  have hpos : 0 ≤ expect Pplus ρ := by
    rw [Pplus_expect]
    exact div_nonneg (hρ.1.2 symmetricVector) (by norm_num)
  have heq := third_expect_decomposition ρ
  linarith

def separatingStateThird : M4 :=
  !![0, 0, 0, 0;
     0, 1 / 2, -(3 / 8), 0;
     0, -(3 / 8), 1 / 2, 0;
     0, 0, 0, 0]

lemma separatingStateThird_hermitian : Hermitian separatingStateThird := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [separatingStateThird, Complex.div_re, Complex.div_im]

lemma separatingStateThird_quad (z : V4) :
    quad separatingStateThird z =
      Complex.normSq (z 1 + z 2) / 16 + 7 * Complex.normSq (z 1 - z 2) / 16 := by
  simp [quad, separatingStateThird, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem separatingStateThird_state : State separatingStateThird := by
  refine ⟨⟨separatingStateThird_hermitian, ?_⟩, ?_⟩
  · intro z
    rw [separatingStateThird_quad]
    exact add_nonneg (div_nonneg (Complex.normSq_nonneg _) (by norm_num))
      (div_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) (by norm_num))
  · norm_num [traceOne, Matrix.trace, separatingStateThird, Fin.sum_univ_succ]

theorem third_separating_expectations :
    expect (W (1 / 4)) separatingStateThird = 0 ∧
    expect (W (1 / 3)) separatingStateThird = -(1 / 24) := by
  norm_num [expect_W, separatingStateThird, Complex.div_re, Complex.div_im,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem third_strict_fineness : StrictlyFiner (W (1 / 3)) (W (1 / 4)) := by
  refine ⟨third_finer, separatingStateThird, separatingStateThird_state, ?_, ?_⟩
  · rw [third_separating_expectations.2]
    norm_num
  · rw [third_separating_expectations.1]

def scaleZ (r : ℝ) (u : V3) : V3 := ![u 0, u 1, r * u 2]

theorem third_ellipsoid_subset :
    canonicalEllipsoid (W (1 / 3)) ⊆ canonicalEllipsoid (W (1 / 4)) := by
  rintro x ⟨u, hu, rfl⟩
  refine ⟨scaleZ (2 / 3) u, ?_, ?_⟩
  · change sqNorm (scaleZ (2 / 3) u) ≤ 1
    change sqNorm u ≤ 1 at hu
    simp [scaleZ, sqNorm, Fin.sum_univ_succ] at hu ⊢
    nlinarith [sq_nonneg (u 2)]
  · rw [W_canonicalMap, W_canonicalMap]
    ext i
    fin_cases i <;> norm_num [scaleZ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem north_point_in_outer :
    (![0, 0, 1 / 2] : V3) ∈ canonicalEllipsoid (W (1 / 4)) := by
  refine ⟨![0, 0, -1], ?_, ?_⟩
  · norm_num [unitBall, sqNorm, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  · rw [W_canonicalMap]
    ext i
    fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem north_point_not_in_inner :
    (![0, 0, 1 / 2] : V3) ∉ canonicalEllipsoid (W (1 / 3)) := by
  rintro ⟨u, hu, heq⟩
  have h2 := congrFun heq 2
  simp [W_canonicalMap, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at h2
  have hu2 : u 2 = -(3 / 2) := by linarith
  change sqNorm u ≤ 1 at hu
  simp [sqNorm, Fin.sum_univ_succ, hu2] at hu
  nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]

theorem third_ellipsoid_proper :
    canonicalEllipsoid (W (1 / 3)) ⊂ canonicalEllipsoid (W (1 / 4)) := by
  refine ⟨third_ellipsoid_subset, ?_⟩
  intro h
  exact north_point_not_in_inner (h north_point_in_outer)

theorem same_chirality_counterexample :
    ClassD (W (1 / 4)) ∧ ClassD (W (1 / 3)) ∧
    Canonical (W (1 / 4)) ∧ Canonical (W (1 / 3)) ∧
    Matrix.det (correlationMatrix (W (1 / 4))) < 0 ∧
    Matrix.det (correlationMatrix (W (1 / 3))) < 0 ∧
    canonicalEllipsoid (W (1 / 3)) ⊂ canonicalEllipsoid (W (1 / 4)) ∧
    StrictlyFiner (W (1 / 3)) (W (1 / 4)) := by
  refine ⟨both_classD.1, third_classD, W_canonical _, W_canonical _, ?_, ?_,
    third_ellipsoid_proper, third_strict_fineness⟩
  · rw [same_negative_chirality.1]
    norm_num
  · rw [same_negative_chirality.2]
    norm_num

#print axioms same_chirality_counterexample

end
end EllipsoidCounterexample
