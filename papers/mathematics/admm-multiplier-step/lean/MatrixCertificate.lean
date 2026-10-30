import GapAlgebra
import StandardRows

open scoped BigOperators

namespace ADMMNearSharp

open ADMMBarrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic energy is continuous on finite vector histories. -/
theorem continuous_quad {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun w : Fin n → E => quad P w) := by
  unfold quad
  fun_prop

/-- An exact matrix certificate, with the actual ADMM rows, yields the
unconditional energy/coercivity/decrease interface used by the convergence
theorem. The concrete interval modules discharge every matrix hypothesis. -/
noncomputable def certificateOfMatrices (d : ℕ) (τ : ℝ)
    (P T : Matrix (Fin (2*(d+1))) (Fin (2*(d+1))) ℝ)
    (D : Matrix (Fin (2*(d+1))) (Fin (2*(d+2))) ℝ)
    (lamF lamG : Matrix (Fin (d+2)) (Fin (d+2)) ℝ)
    (hP : (P - StandardRows.coerc d).PosSemidef) (hT : T.PosSemidef)
    (hlamF : ∀ i j, 0 ≤ lamF i j) (hlamG : ∀ i j, 0 ≤ lamG i j)
    (hflowF : ∀ i, (∑ j, lamF i j) = ∑ j, lamF j i)
    (hflowG : ∀ i, (∑ j, lamG i j) = ∑ j, lamG j i)
    (hid : (StandardRows.S0 d).transpose * P * StandardRows.S0 d -
      (StandardRows.S1 d).transpose * P * StandardRows.S1 d - StandardRows.diss d -
      (qsum (StandardRows.xRows d) (StandardRows.aRows d τ) lamF +
       qsum (StandardRows.zRows d) (StandardRows.bRows d τ) lamG) =
      D.transpose * T * D) : MemoryCertificate d τ E where
  energy Z V := quad P (StandardRows.interleave Z V)
  continuous_energy := (continuous_quad P).comp StandardRows.continuous_interleave
  energy_zero := by simp [quad]
  lower Z V := by
    have h := quad_nonneg hP (StandardRows.interleave Z V)
    rw [quad_sub, StandardRows.quad_coerc] at h
    linarith
  descent Z V F G hF hG := by
    have h := matrix_descent P T (StandardRows.S0 d) (StandardRows.S1 d) D
      (StandardRows.diss d) (StandardRows.xRows d) (StandardRows.aRows d τ)
      (StandardRows.zRows d) (StandardRows.bRows d τ) lamF lamG hT
      hlamF hlamG hflowF hflowG hid (StandardRows.interleave Z V) F G
      (by simpa only [StandardRows.linComb_xRows, StandardRows.linComb_aRows] using hF)
      (by simpa only [StandardRows.linComb_zRows, StandardRows.linComb_bRows] using hG)
    simpa only [StandardRows.linComb_S0, StandardRows.linComb_S1,
      StandardRows.quad_diss, add_assoc] using h

#print axioms certificateOfMatrices

end ADMMNearSharp
