import CoreDefs

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace PPTCone

variable {A B : Type*} [Fintype A] [Fintype B]

theorem trace_mul_pure (K : Matrix (A × B) (A × B) ℂ) (v : A × B → ℂ) :
    Matrix.trace (K * pure v) = star v ⬝ᵥ (K *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pure,
    dotProduct, Matrix.mulVec, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem trace_partialTranspose (K R : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace (K * partialTranspose R) = Matrix.trace (partialTranspose K * R) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, partialTranspose,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ b, ∑ c, ∑ d, K (a,b) (c,d) * R (c,b) (a,d)) =
        ∑ c, ∑ b, ∑ d, K (a,b) (c,d) * R (c,b) (a,d) := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, K (a,b) (c,d) * R (c,b) (a,d) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ b, K (a,b) (c,d) * R (c,b) (a,d) := Finset.sum_comm

theorem sn2_trace_nonneg (K R : Matrix (A × B) (A × B) ℂ)
    (hK : K.PosSemidef) (hR : IsSN2 R) : 0 ≤ Matrix.trace (K * R) := by
  obtain ⟨n, v, hv, rfl⟩ := hR
  rw [Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_nonneg
  intro i hi
  rw [trace_mul_pure]
  exact hK.2 (v i)

theorem sn2_eq_zero_of_trace_zero (K R : Matrix (A × B) (A × B) ℂ)
    (hK : K.PosSemidef) (hR : IsSN2 R)
    (hker : ∀ v, HasSR2 v → K *ᵥ v = 0 → v = 0)
    (hzero : Matrix.trace (K * R) = 0) : R = 0 := by
  obtain ⟨n, v, hv, rfl⟩ := hR
  rw [Matrix.mul_sum, Matrix.trace_sum] at hzero
  have hi : ∀ i : Fin n, Matrix.trace (K * pure (v i)) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
      rw [trace_mul_pure]
      exact hK.2 (v j))).mp hzero i (Finset.mem_univ i)
  have hvzero : ∀ i, v i = 0 := by
    intro i
    apply hker (v i) (hv i)
    apply (hK.dotProduct_mulVec_zero_iff (v i)).mp
    simpa only [trace_mul_pure] using hi i
  simp only [hvzero, pure_zero, Finset.sum_const_zero]

/-- A positive, partial-transpose-invariant separator whose kernel has no
nonzero Schmidt-rank-at-most-two vector excludes every nonzero matrix on its
zero face from the cone SN₂ + partialTranspose(SN₂). -/
theorem not_isDSP2_of_separator (P K : Matrix (A × B) (A × B) ℂ)
    (hK : K.PosSemidef) (hpt : partialTranspose K = K)
    (hzero : Matrix.trace (K * P) = 0) (hne : P ≠ 0)
    (hker : ∀ v, HasSR2 v → K *ᵥ v = 0 → v = 0) : ¬ IsDSP2 P := by
  rintro ⟨Q, R, hQ, hR, heq⟩
  have hsum : Matrix.trace (K * Q) + Matrix.trace (K * R) = 0 := by
    simpa only [heq, Matrix.mul_add, Matrix.trace_add, trace_partialTranspose, hpt]
      using hzero
  have hQ0 : Matrix.trace (K * Q) = 0 :=
    (add_eq_zero_iff_of_nonneg (sn2_trace_nonneg K Q hK hQ)
      (sn2_trace_nonneg K R hK hR)).mp hsum |>.1
  have hR0 : Matrix.trace (K * R) = 0 :=
    (add_eq_zero_iff_of_nonneg (sn2_trace_nonneg K Q hK hQ)
      (sn2_trace_nonneg K R hK hR)).mp hsum |>.2
  have hQzero := sn2_eq_zero_of_trace_zero K Q hK hQ hker hQ0
  have hRzero := sn2_eq_zero_of_trace_zero K R hK hR hker hR0
  apply hne
  simpa only [hQzero, hRzero, partialTranspose_zero, add_zero] using heq

end PPTCone
