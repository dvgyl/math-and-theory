import QPermanentResearch.Algebra
import QPermanentResearch.EndpointReduction

namespace QPermanentResearch

theorem positive_smul_posDef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c) : (c • A).PosDef := by
  refine ⟨?_, ?_⟩
  · change Matrix.conjTranspose (c • A) = c • A
    rw [Matrix.conjTranspose_smul, hA.1]
    simp
  · intro x hx
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul]
    exact mul_pos hc (hA.2 x hx)

noncomputable def normalizedRegularization {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / (1 + η)) • diagonalRegularization A η

theorem normalizedRegularization_posDef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {η : ℝ} (hη : 0 < η) : (normalizedRegularization A η).PosDef := by
  apply positive_smul_posDef (diagonalRegularization_posDef hA hη)
  positivity

theorem normalizedRegularization_diag {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hdiag : ∀ i, A i i = 1)
    {η : ℝ} (hη : 0 < η) (i : Fin n) :
    normalizedRegularization A η i i = 1 := by
  have hden : 1 + η ≠ 0 := by linarith
  simp [normalizedRegularization, diagonalRegularization, hdiag, hden]

theorem normalizedRegularization_endpoint_negative {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {η : ℝ} (hη : 0 < η)
    (hneg : qPermanentDerivative (diagonalRegularization A η) 1 < 0) :
    qPermanentDerivative (normalizedRegularization A η) 1 < 0 := by
  rw [normalizedRegularization, qPermanentDerivative_smul]
  apply mul_neg_of_pos_of_neg _ hneg
  apply pow_pos
  positivity

/-- Every real PSD correlation endpoint witness yields a PD correlation
    witness with a decrease at rational parameters strictly between zero and
    one. The regularization and normalization are proved from actual matrix
    positivity and the actual permutation polynomial. -/
theorem correlation_endpoint_to_posDef_interior {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hdiag : ∀ i, A i i = 1)
    (hneg : qPermanentDerivative A 1 < 0) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ,
      B.PosDef ∧ (∀ i, B i i = 1) ∧
      ∃ q₁ q₂ : ℚ, 0 < q₁ ∧ q₁ < q₂ ∧ q₂ < 1 ∧
        qPermanent B (q₂ : ℝ) < qPermanent B (q₁ : ℝ) := by
  obtain ⟨η, hη, _, _, hD⟩ := exists_posdef_regularization A hA hneg
    (bound := 1) (by norm_num)
  refine ⟨normalizedRegularization A η,
    normalizedRegularization_posDef hA hη,
    normalizedRegularization_diag A hdiag hη, ?_⟩
  exact exists_rational_interior_decrease _
    (normalizedRegularization_endpoint_negative A hη hD)

end QPermanentResearch
