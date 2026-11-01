import QPermanentResearch.Algebra
import QPermanentResearch.Complement
import QPermanentResearch.Fischer
import QPermanentResearch.EndpointReduction
import Mathlib.Tactic

/-!
The endpoint derivative of a real rank-three Gram matrix, expressed in
factorial-weighted coefficient norms.  All sums refer to the actual
permutation definition of the q-permanent.  The complement reindexing is
based on Kitamura's Apache-2.0 proof package (revision 4200da4fc1a132d69c23fb877795b5b72089544b);
the three-coordinate Cauchy--Binet and real wedge-norm extension are new here.
-/

open scoped BigOperators
namespace QPermanentResearch
noncomputable section

def rowWedgeCoordinate {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ)
    (i j : Fin n) (a b : Fin d) : ℝ :=
  V i a * V j b - V i b * V j a

/-- Coordinates are the ordered coordinate pairs (0,1), (0,2), (1,2). -/
def rowWedge3 {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (i j : Fin n) : Fin 3 → ℝ :=
  ![rowWedgeCoordinate V i j 0 1,
    rowWedgeCoordinate V i j 0 2,
    rowWedgeCoordinate V i j 1 2]

theorem rankThreeGram_minor {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (i j k l : Fin n) :
    (V * V.transpose) i k * (V * V.transpose) j l -
        (V * V.transpose) i l * (V * V.transpose) j k =
      ∑ c : Fin 3, rowWedge3 V i j c * rowWedge3 V k l c := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    rowWedge3, rowWedgeCoordinate]
  ring

def complementColorCoefficient {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ)
    (i j : Fin n) (α : Fin d → Fin (n - 2 + 1)) : ℝ :=
  if hij : i ≠ j then colorCoefficient (complementMatrix V i j hij) α else 0

theorem remainingGram_matching_coefficients {n d : ℕ}
    (U W : Matrix (Fin n) (Fin d) ℝ)
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l) :
    (∑ σ : Equiv.Perm (Fin n), if σ i = k ∧ σ j = l then
      remainingProduct (U * W.transpose) σ i j else 0) =
      ∑ α : Fin d → Fin (n - 2 + 1), colorWeight α *
        complementColorCoefficient W k l α *
        complementColorCoefficient U i j α := by
  have h := remainingGram_matching_sum U W i j k l hij hkl
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [h, ← qPermanent_one_eq_permanent, gram_permanent_coefficients]
  simp [complementColorCoefficient, hij, hkl]

def componentPairContribution {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (c : Fin 3) (i j : Fin n) (σ : Equiv.Perm (Fin n)) : ℝ :=
  if σ i < σ j then rowWedge3 V i j c * rowWedge3 V (σ i) (σ j) c *
    remainingProduct (V * V.transpose) σ i j else 0

def componentPairSum {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ) (c : Fin 3) : ℝ :=
  ∑ p ∈ rowPairs n, ∑ σ : Equiv.Perm (Fin n),
    componentPairContribution V c p.1 p.2 σ

theorem rankThree_pairMinorContribution {n : ℕ}
    (V : Matrix (Fin n) (Fin 3) ℝ) (i j : Fin n) (σ : Equiv.Perm (Fin n)) :
    pairMinorContribution (V * V.transpose) i j σ =
      ∑ c : Fin 3, componentPairContribution V c i j σ := by
  classical
  unfold pairMinorContribution componentPairContribution
  by_cases h : σ i < σ j
  · simp only [if_pos h, rankThreeGram_minor, Finset.sum_mul]
  · simp only [if_neg h, Finset.sum_const_zero]

theorem pairMinorGram_components {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ) :
    pairMinorSum (V * V.transpose) = ∑ c : Fin 3, componentPairSum V c := by
  classical
  unfold pairMinorSum componentPairSum
  simp_rw [rankThree_pairMinorContribution]
  conv_lhs => arg 2; ext p; rw [Finset.sum_comm]
  exact Finset.sum_comm

theorem imagePair_component_sum {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (c : Fin 3) (i j : Fin n) (σ : Equiv.Perm (Fin n)) :
    (∑ q ∈ rowPairs n, if σ i = q.1 ∧ σ j = q.2 then
      rowWedge3 V q.1 q.2 c * remainingProduct (V * V.transpose) σ i j else 0) =
      if σ i < σ j then
        rowWedge3 V (σ i) (σ j) c * remainingProduct (V * V.transpose) σ i j
      else 0 := by
  classical
  by_cases h : σ i < σ j
  · rw [if_pos h]
    refine (Finset.sum_eq_single (σ i, σ j) ?_ ?_).trans ?_
    · intro q _ hq
      have hm : ¬ (σ i = q.1 ∧ σ j = q.2) := by
        intro hm; exact hq (Prod.ext hm.1.symm hm.2.symm)
      simp [hm]
    · intro hm; exact (hm (by simp [rowPairs, h])).elim
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro q hq
    have hm : ¬ (σ i = q.1 ∧ σ j = q.2) := by
      intro hm
      exact h (by simpa [hm.1, hm.2] using (Finset.mem_filter.mp hq).2)
    simp [hm]

theorem componentPairSum_pairs {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (c : Fin 3) :
    componentPairSum V c =
      ∑ p ∈ rowPairs n, rowWedge3 V p.1 p.2 c *
        ∑ q ∈ rowPairs n, rowWedge3 V q.1 q.2 c *
          ∑ σ : Equiv.Perm (Fin n), if σ p.1 = q.1 ∧ σ p.2 = q.2 then
            remainingProduct (V * V.transpose) σ p.1 p.2 else 0 := by
  classical
  unfold componentPairSum componentPairContribution
  apply Finset.sum_congr rfl
  intro p _
  have hfactor : ∀ σ : Equiv.Perm (Fin n),
      (if σ p.1 < σ p.2 then rowWedge3 V p.1 p.2 c *
        rowWedge3 V (σ p.1) (σ p.2) c *
          remainingProduct (V * V.transpose) σ p.1 p.2 else 0) =
      rowWedge3 V p.1 p.2 c * (if σ p.1 < σ p.2 then
        rowWedge3 V (σ p.1) (σ p.2) c *
          remainingProduct (V * V.transpose) σ p.1 p.2 else 0) := by
    intro σ; split_ifs <;> ring
  simp_rw [hfactor]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [← imagePair_component_sum V c]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

def wedgeCoefficient {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (c : Fin 3) (α : Fin 3 → Fin (n - 2 + 1)) : ℝ :=
  ∑ p ∈ rowPairs n, rowWedge3 V p.1 p.2 c *
    complementColorCoefficient V p.1 p.2 α

theorem componentPairSum_coefficients {n : ℕ}
    (V : Matrix (Fin n) (Fin 3) ℝ) (c : Fin 3) :
    componentPairSum V c =
      ∑ α : Fin 3 → Fin (n - 2 + 1),
        colorWeight α * (wedgeCoefficient V c α)^2 := by
  classical
  have hexpand : componentPairSum V c =
      ∑ p ∈ rowPairs n, ∑ q ∈ rowPairs n, ∑ α : Fin 3 → Fin (n - 2 + 1),
        colorWeight α *
          (rowWedge3 V p.1 p.2 c * complementColorCoefficient V p.1 p.2 α) *
          (rowWedge3 V q.1 q.2 c * complementColorCoefficient V q.1 q.2 α) := by
    rw [componentPairSum_pairs]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [remainingGram_matching_coefficients V V p.1 p.2 q.1 q.2
      (Finset.mem_filter.mp hp).2.ne (Finset.mem_filter.mp hq).2.ne]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    ring
  rw [hexpand]
  conv_lhs => arg 2; ext p; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [wedgeCoefficient, pow_two, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  simp_rw [Finset.mul_sum, ← mul_assoc]
  exact Finset.sum_comm

/-- The pair-minor contribution is the sum of the three Fischer wedge norms. -/
theorem pairMinorGram_wedge_squares {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ) :
    pairMinorSum (V * V.transpose) =
      ∑ c : Fin 3, ∑ α : Fin 3 → Fin (n - 2 + 1),
        colorWeight α * (wedgeCoefficient V c α)^2 := by
  rw [pairMinorGram_components]
  exact Finset.sum_congr rfl (fun c _ => componentPairSum_coefficients V c)

def productFischerNorm {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ) : ℝ :=
  ∑ α : Fin d → Fin (n + 1), colorWeight α * (colorCoefficient V α)^2

def wedgeFischerNorm {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ) : ℝ :=
  ∑ c : Fin 3, ∑ α : Fin 3 → Fin (n - 2 + 1),
    colorWeight α * (wedgeCoefficient V c α)^2

/-- A rank-three coefficient certificate computes the actual q-permanent derivative. -/
theorem endpointDerivative_fischer {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ) :
    2 * qPermanentDerivative (V * V.transpose) 1 =
      (n.choose 2 : ℝ) * productFischerNorm V - wedgeFischerNorm V := by
  rw [endpointDerivative_choose_pairMinorSum, gram_permanent_squares,
    pairMinorGram_wedge_squares]
  rfl

/-- The exact coefficient inequality is equivalent to a negative endpoint derivative. -/
theorem endpointDerivative_neg_iff_fischer {n : ℕ}
    (V : Matrix (Fin n) (Fin 3) ℝ) :
    qPermanentDerivative (V * V.transpose) 1 < 0 ↔
      (n.choose 2 : ℝ) * productFischerNorm V < wedgeFischerNorm V := by
  have h := endpointDerivative_fischer V
  constructor <;> intro hneg <;> linarith

/-- A verified finite coefficient inequality gives a real positive definite
matrix and two rational parameters strictly inside the conjectured interval. -/
theorem fischer_certificate_to_posDef_interior {n : ℕ}
    (V : Matrix (Fin n) (Fin 3) ℝ)
    (h : (n.choose 2 : ℝ) * productFischerNorm V < wedgeFischerNorm V) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef ∧
      ∃ q₁ q₂ : ℚ, 0 < q₁ ∧ q₁ < q₂ ∧ q₂ < 1 ∧
        qPermanent B (q₂ : ℝ) < qPermanent B (q₁ : ℝ) := by
  have hPSD : (V * V.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose V
  exact posSemidef_endpoint_to_posDef_interior (V * V.transpose) hPSD
    ((endpointDerivative_neg_iff_fischer V).mpr h)

#print axioms endpointDerivative_fischer
#print axioms fischer_certificate_to_posDef_interior

end
end QPermanentResearch
