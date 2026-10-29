module
public import PositiveRateMatrices
public import HermitianShift

@[expose] public section

/-!
The positive spectral factorization derived from arbitrary positive cycle
rates. This discharges the matrix/spectrum hypotheses; it does not assume
them. A current-uncertainty proof is still needed for the final bound.
-/

open scoped BigOperators
open Equiv Polynomial

namespace UnicyclicDeterminant

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positive_rate_spectral_factorization (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (u v : ι → ℝ)
    (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j)
    (hUV : (∏ j, u j) ≠ ∏ j, v j) (i : ι) :
    ∃ theta : ι → ℝ,
      (∀ j, 0 < theta j) ∧
      (-(rateMatrix σ u v 0)).charpoly +
          C (((∏ j, Real.sqrt (u j)) - ∏ j, Real.sqrt (v j))^2) =
        ∏ j, (X + C (theta j)) ∧
      (((∏ j, Real.sqrt (u j)) - ∏ j, Real.sqrt (v j))^2) = ∏ j, theta j ∧
      (-(rateMatrix σ u v 0)).charpoly.coeff 0 = 0 := by
  have hH := rateGram_posDef σ hc hn u v hu hv hUV i
  let theta := hH.isHermitian.eigenvalues
  have htheta : ∀ j, 0 < theta j := fun j => hH.eigenvalues_pos j
  have hshift (s : ℝ) :
      (s • (1 : Matrix ι ι ℝ) + rateGram σ u v).det =
        (s • (1 : Matrix ι ι ℝ) + rateMatrix σ u v 0).det +
          (((∏ j, Real.sqrt (u j)) - ∏ j, Real.sqrt (v j))^2) := by
    rw [rateMatrix_add_scalar σ u v s]
    exact rateGram_shifted_determinant σ hc hn u v hu hv i s
  have hfactor := UnicyclicSpectral.polynomial_factorization_of_det_shift
    (rateMatrix σ u v 0) (rateGram σ u v) hH.isHermitian
    (((∏ j, Real.sqrt (u j)) - ∏ j, Real.sqrt (v j))^2) hshift
  have hp0 : (-(rateMatrix σ u v 0)).charpoly.eval 0 = 0 := by
    rw [UnicyclicSpectral.charpoly_neg_eval]
    simp only [zero_smul, zero_add]
    exact rateMatrix_det_zero σ u v (fun j => (hu j).le) (fun j => (hv j).le) i
  have hd : (((∏ j, Real.sqrt (u j)) - ∏ j, Real.sqrt (v j))^2) = ∏ j, theta j := by
    have hh := congrArg (fun p : Polynomial ℝ => p.eval 0) hfactor
    simpa only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_prod,
      Polynomial.eval_X, hp0, zero_add, theta] using hh
  refine ⟨theta, htheta, hfactor, hd, ?_⟩
  rwa [Polynomial.coeff_zero_eq_eval_zero]

theorem fin_ring_positive_spectral_factorization (n : ℕ) (hn : 3 ≤ n)
    (u v : Fin n → ℝ) (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j)
    (hUV : (∏ j, u j) ≠ ∏ j, v j) :
    ∃ theta : Fin n → ℝ,
      (∀ j, 0 < theta j) ∧
      (-(rateMatrix (finRotate n) u v 0)).charpoly +
          C (((∏ j, Real.sqrt (u j)) - ∏ j, Real.sqrt (v j))^2) =
        ∏ j, (X + C (theta j)) ∧
      (((∏ j, Real.sqrt (u j)) - ∏ j, Real.sqrt (v j))^2) = ∏ j, theta j ∧
      (-(rateMatrix (finRotate n) u v 0)).charpoly.coeff 0 = 0 := by
  exact positive_rate_spectral_factorization (finRotate n)
    (finRotate_isCycleOn n (by omega)) (by simpa using hn) u v hu hv hUV ⟨0, by omega⟩

#print axioms positive_rate_spectral_factorization
#print axioms fin_ring_positive_spectral_factorization

end

end UnicyclicDeterminant
