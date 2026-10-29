import KovacecJordan

/-! The actual topological frontier of the explicit polygon. -/
noncomputable section
namespace KovacecJordan
open Set Complex

private theorem dist_left (z : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    dist z (z - (r : ℂ)) = r := by
  rw [dist_eq_norm]
  have heq : z - (z - (r : ℂ)) = (r : ℂ) := by ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

private theorem dist_right (z : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    dist z (z + (r : ℂ)) = r := by
  rw [dist_eq_norm]
  have heq : z - (z + (r : ℂ)) = -(r : ℂ) := by ring
  rw [heq, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

private theorem dist_down (z : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    dist z (z - (r : ℂ) * Complex.I) = r := by
  rw [dist_eq_norm]
  have heq : z - (z - (r : ℂ) * Complex.I) = (r : ℂ) * Complex.I := by ring
  rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]

private theorem dist_up (z : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    dist z (z + (r : ℂ) * Complex.I) = r := by
  rw [dist_eq_norm]
  have heq : z - (z + (r : ℂ) * Complex.I) = -((r : ℂ) * Complex.I) := by ring
  rw [heq, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]

theorem J_subset_frontier_C : J ⊆ frontier C := by
  intro z hz
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure hz.1, ?_⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases hz.2 with hy | hy | hx | hx
  · refine ⟨z - ((ε/2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · change z - ((ε/2 : ℝ) : ℂ) * Complex.I ∉ C
      intro hC
      have h := hC.1
      simp at h
      linarith
    · rw [dist_down z (ε/2) (by positivity)]
      linarith
  · refine ⟨z + ((ε/2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · change z + ((ε/2 : ℝ) : ℂ) * Complex.I ∉ C
      intro hC
      have h := hC.2.1
      simp at h
      linarith
    · rw [dist_up z (ε/2) (by positivity)]
      linarith
  · refine ⟨z - ((ε/2 : ℝ) : ℂ), ?_, ?_⟩
    · change z - ((ε/2 : ℝ) : ℂ) ∉ C
      intro hC
      have h := hC.2.2.1
      simp at h
      linarith
    · rw [dist_left z (ε/2) (by positivity)]
      linarith
  · refine ⟨z + ((ε/2 : ℝ) : ℂ), ?_, ?_⟩
    · change z + ((ε/2 : ℝ) : ℂ) ∉ C
      intro hC
      have h := hC.2.2.2
      simp at h
      linarith
    · rw [dist_right z (ε/2) (by positivity)]
      linarith

theorem frontier_C_subset_J : frontier C ⊆ J := by
  intro z hz
  change z ∈ closure C ∧ z ∉ interior C at hz
  have hC : z ∈ C := isClosed_C.closure_eq ▸ hz.1
  refine ⟨hC, ?_⟩
  by_contra h
  push_neg at h
  rcases h with ⟨hy0ne, hy2ne, hxlne, hxrne⟩
  have hO : z ∈ O :=
    ⟨lt_of_le_of_ne hC.1 (Ne.symm hy0ne), lt_of_le_of_ne hC.2.1 hy2ne,
      lt_of_le_of_ne hC.2.2.1 (Ne.symm hxlne), lt_of_le_of_ne hC.2.2.2 hxrne⟩
  exact hz.2 (O_subset_interior_C hO)

theorem frontier_C_eq_J : frontier C = J :=
  Set.Subset.antisymm frontier_C_subset_J J_subset_frontier_C

#print axioms frontier_C_eq_J
end KovacecJordan
