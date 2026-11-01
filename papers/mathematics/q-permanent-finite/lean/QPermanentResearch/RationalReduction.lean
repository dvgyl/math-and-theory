import QPermanentResearch.WedgeNorm
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.ContinuousOn

/-!
Rational positive definite realizations of negative endpoint witnesses.
Rational approximation is performed on Gram vectors, which preserves positive
semidefiniteness.  A rational positive diagonal shift then gives positive
definiteness without assuming openness of the positive definite cone.
-/

open Filter Set Topology
open scoped BigOperators
namespace QPermanentResearch
noncomputable section

def rationalMatrixCast {m n : ℕ} (Q : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin n) ℝ := fun i j => (Q i j : ℝ)

theorem rationalMatrixCast_denseRange {m n : ℕ} :
    DenseRange (rationalMatrixCast (m := m) (n := n)) := by
  exact DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => Rat.denseRange_cast))

theorem rationalMatrixCast_gram {n d : ℕ} (Q : Matrix (Fin n) (Fin d) ℚ) :
    rationalMatrixCast (Q * Q.transpose) =
      rationalMatrixCast Q * (rationalMatrixCast Q).transpose := by
  ext i j
  simp [rationalMatrixCast, Matrix.mul_apply, Matrix.transpose_apply]

theorem rationalMatrixCast_add_diagonal {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℚ) (η : ℚ) :
    rationalMatrixCast (Q + Matrix.diagonal (fun _ => η)) =
      diagonalRegularization (rationalMatrixCast Q) (η : ℝ) := by
  ext i j
  by_cases hij : i = j <;>
    simp [rationalMatrixCast, diagonalRegularization, Matrix.diagonal_apply, hij]

theorem continuous_gram {n d : ℕ} :
    Continuous (fun V : Matrix (Fin n) (Fin d) ℝ => V * V.transpose) := by
  fun_prop

theorem exists_rational_gram_negative_endpoint {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ)
    (hneg : qPermanentDerivative (V * V.transpose) 1 < 0) :
    ∃ Q : Matrix (Fin n) (Fin d) ℚ,
      qPermanentDerivative (rationalMatrixCast Q * (rationalMatrixCast Q).transpose) 1 < 0 := by
  have hc : Continuous (fun W : Matrix (Fin n) (Fin d) ℝ =>
      qPermanentDerivative (W * W.transpose) 1) :=
    (continuous_qPermanentDerivative_matrix 1).comp continuous_gram
  exact rationalMatrixCast_denseRange.exists_mem_open
    (isOpen_lt hc continuous_const) ⟨V, hneg⟩

theorem exists_rational_posdef_regularization {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hneg : qPermanentDerivative A 1 < 0)
    {bound : ℝ} (hbound : 0 < bound) :
    ∃ η : ℚ, 0 < η ∧ (η : ℝ) < bound ∧
      (diagonalRegularization A (η : ℝ)).PosDef ∧
      qPermanentDerivative (diagonalRegularization A (η : ℝ)) 1 < 0 := by
  have hc : Continuous (fun η : ℝ =>
      qPermanentDerivative (diagonalRegularization A η) 1) :=
    (continuous_qPermanentDerivative_matrix 1).comp
      (continuous_diagonalRegularization A)
  have hev : ∀ᶠ η in 𝓝 (0 : ℝ),
      qPermanentDerivative (diagonalRegularization A η) 1 < 0 :=
    hc.continuousAt.eventually_lt continuousAt_const (by simpa using hneg)
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨η, hη, hηmin⟩ := exists_rat_btwn (lt_min hε hbound)
  have hηε : (η : ℝ) < ε := lt_of_lt_of_le hηmin (min_le_left _ _)
  have hηbound : (η : ℝ) < bound := lt_of_lt_of_le hηmin (min_le_right _ _)
  refine ⟨η, ?_, hηbound, diagonalRegularization_posDef hA hη, ?_⟩
  · exact_mod_cast hη
  · apply hb
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hη] using hηε

/-- The matrix, as well as both interior parameters, may be chosen rational. -/
theorem gram_endpoint_to_rational_posDef_interior {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ)
    (hneg : qPermanentDerivative (V * V.transpose) 1 < 0) :
    ∃ B : Matrix (Fin n) (Fin n) ℚ, (rationalMatrixCast B).PosDef ∧
      ∃ q₁ q₂ : ℚ, 0 < q₁ ∧ q₁ < q₂ ∧ q₂ < 1 ∧
        qPermanent (rationalMatrixCast B) (q₂ : ℝ) <
          qPermanent (rationalMatrixCast B) (q₁ : ℝ) := by
  obtain ⟨Q, hQ⟩ := exists_rational_gram_negative_endpoint V hneg
  have hPSD : (rationalMatrixCast Q * (rationalMatrixCast Q).transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (rationalMatrixCast Q)
  obtain ⟨η, _, _, hPD, hD⟩ := exists_rational_posdef_regularization _ hPSD hQ
    (bound := 1) (by norm_num)
  refine ⟨Q * Q.transpose + Matrix.diagonal (fun _ => η), ?_, ?_⟩
  · simpa only [rationalMatrixCast_add_diagonal, rationalMatrixCast_gram] using hPD
  · apply exists_rational_interior_decrease
    simpa only [rationalMatrixCast_add_diagonal, rationalMatrixCast_gram] using hD

/-- No rank condition is needed for rational realization of an endpoint witness. -/
theorem posSemidef_endpoint_to_rational_posDef_interior {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hneg : qPermanentDerivative A 1 < 0) :
    ∃ B : Matrix (Fin n) (Fin n) ℚ, (rationalMatrixCast B).PosDef ∧
      ∃ q₁ q₂ : ℚ, 0 < q₁ ∧ q₁ < q₂ ∧ q₂ < 1 ∧
        qPermanent (rationalMatrixCast B) (q₂ : ℝ) <
          qPermanent (rationalMatrixCast B) (q₁ : ℝ) := by
  obtain ⟨U, hU⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hA
  have hGram : A = U.transpose * (U.transpose).transpose := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose] using hU
  apply gram_endpoint_to_rational_posDef_interior U.transpose
  simpa only [← hGram] using hneg

/-- The proved Fischer identity transports a finite strict coefficient
inequality all the way to rational positive definite interior witnesses. -/
theorem fischer_certificate_to_rational_posDef_interior {n : ℕ}
    (V : Matrix (Fin n) (Fin 3) ℝ)
    (h : (n.choose 2 : ℝ) * productFischerNorm V < wedgeFischerNorm V) :
    ∃ B : Matrix (Fin n) (Fin n) ℚ, (rationalMatrixCast B).PosDef ∧
      ∃ q₁ q₂ : ℚ, 0 < q₁ ∧ q₁ < q₂ ∧ q₂ < 1 ∧
        qPermanent (rationalMatrixCast B) (q₂ : ℝ) <
          qPermanent (rationalMatrixCast B) (q₁ : ℝ) := by
  exact gram_endpoint_to_rational_posDef_interior V
    ((endpointDerivative_neg_iff_fischer V).mpr h)

#print axioms posSemidef_endpoint_to_rational_posDef_interior
#print axioms fischer_certificate_to_rational_posDef_interior

end
end QPermanentResearch
