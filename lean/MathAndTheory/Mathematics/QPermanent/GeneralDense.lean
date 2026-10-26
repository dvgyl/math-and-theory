module
public import MathAndTheory.Mathematics.QPermanent.GeneralNormalization
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Order.Filter.Finite
public import Mathlib.Tactic.FunProp

@[expose] public section

namespace MathAndTheory.QPermanent

open scoped BigOperators Matrix
open Filter Topology

noncomputable section

def allOnesMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1

theorem allOnesMatrix_posSemidef (n : ℕ) : (allOnesMatrix n).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp [allOnesMatrix, Matrix.conjTranspose_apply]
  intro x
  have h : star x ⬝ᵥ (allOnesMatrix n *ᵥ x) = (∑ i : Fin n, x i) ^ 2 := by
    simp only [allOnesMatrix, Matrix.mulVec, dotProduct, Pi.star_apply,
      star_trivial, one_mul]
    rw [pow_two, Finset.sum_mul]
  rw [h]
  exact sq_nonneg _

theorem continuous_qPermanentDerivative_perturb {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    Continuous (fun ε : ℝ => qPermanentDerivative (A + ε • allOnesMatrix n) r) := by
  unfold qPermanentDerivative
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, allOnesMatrix, mul_one]
  fun_prop

/-- A small positive all-ones perturbation removes zero entries and preserves
both strict positivity and a strict negative derivative. -/
theorem exists_dense_posDef_of_negative_derivative {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (hA : A.PosDef) (hderiv : deriv (qPermanent A) r < 0) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ,
      B.PosDef ∧ (∀ i j, B i j ≠ 0) ∧ deriv (qPermanent B) r < 0 := by
  have hentry : ∀ᶠ ε : ℝ in 𝓝 0, ∀ i j, A i j ≠ 0 → A i j + ε ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : A i j = 0
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hij))
    · have h := ((continuous_const.add continuous_id :
          Continuous (fun ε : ℝ => A i j + ε)).continuousAt).eventually_ne
          (by simpa using hij : A i j + (0 : ℝ) ≠ 0)
      exact h.mono (fun _ h _ => h)
  have hd0 : qPermanentDerivative (A + (0 : ℝ) • allOnesMatrix n) r < 0 := by
    simpa [qPermanent_deriv] using hderiv
  have hneg : ∀ᶠ ε : ℝ in 𝓝 0,
      qPermanentDerivative (A + ε • allOnesMatrix n) r < 0 :=
    (continuous_qPermanentDerivative_perturb A r).tendsto 0 |>.eventually (gt_mem_nhds hd0)
  have hboth : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∀ i j, A i j ≠ 0 → A i j + ε ≠ 0) ∧
        qPermanentDerivative (A + ε • allOnesMatrix n) r < 0 :=
    (hentry.and hneg).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, ⟨he, hd⟩, hε⟩ := (hboth.and self_mem_nhdsWithin).exists
  refine ⟨A + ε • allOnesMatrix n,
    hA.add_posSemidef ((allOnesMatrix_posSemidef n).smul hε.le), ?_, ?_⟩
  · intro i j
    by_cases hij : A i j = 0
    · simpa [allOnesMatrix, hij] using hε.ne'
    · simpa [allOnesMatrix] using he i j hij
  · rwa [qPermanent_deriv]

/-- The matrices in the general theorem can simultaneously have unit diagonal
and no zero entries. -/
theorem exists_dense_correlation_negative_qPermanent_derivative (r : ℝ) (hr : 1 < r) :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef ∧ (∀ i, A i i = 1) ∧ (∀ i j, A i j ≠ 0) ∧
        deriv (qPermanent A) r < 0 := by
  obtain ⟨n, A, hA, hderiv⟩ := exists_posDef_negative_qPermanent_derivative r hr
  obtain ⟨B, hB, hentries, hd⟩ := exists_dense_posDef_of_negative_derivative A r hA hderiv
  let s := normalizingFactors B
  have hs : ∀ i, 0 < s i := normalizingFactors_pos B hB
  refine ⟨n, diagonalScale s B, diagonalScale_posDef s B (fun i => (hs i).ne') hB,
    normalized_diagonal B hB, ?_, ?_⟩
  · intro i j
    exact mul_ne_zero (mul_ne_zero (hs i).ne' (hentries i j)) (hs j).ne'
  · rw [deriv_qPermanent_diagonalScale]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos (Finset.prod_pos (fun i _ => hs i))) hd

end

end MathAndTheory.QPermanent
