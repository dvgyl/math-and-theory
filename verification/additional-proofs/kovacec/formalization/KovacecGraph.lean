import KovacecCertificate
import KovacecJordan
import KovacecBoundary
import RayComponent
import RayExterior

noncomputable section
namespace KovacecGraph
open Set Complex KovacecCertificate KovacecJordan KovacecExterior

set_option maxHeartbeats 4000000

/-- The transposition-segment graph defined in this package. -/
def sourceGraph : Set ℂ := {z | ∃ σ τ : Equiv.Perm (Fin 3),
  (∃ i j : Fin 3, i ≠ j ∧ τ = σ * Equiv.swap i j) ∧
  z ∈ segment ℝ (sigmaPoint σ) (sigmaPoint τ)}

theorem graph_eq_sourceGraph : graph = sourceGraph := by
  ext z
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨perm (e k).1, perm (e k).2, ?_, ?_⟩
    · exact (edge_exhaustive _ _).mpr ⟨k, Or.inl ⟨rfl, rfl⟩⟩
    · simpa only [sigmaPoint_perm] using hk
  · rintro ⟨σ, τ, hadj, hz⟩
    rcases (edge_exhaustive σ τ).mp hadj with ⟨k, h | h⟩
    · rcases h with ⟨hσ, hτ⟩
      rw [← hσ, ← hτ, sigmaPoint_perm, sigmaPoint_perm] at hz
      exact ⟨k, hz⟩
    · rcases h with ⟨hτ, hσ⟩
      rw [← hσ, ← hτ, sigmaPoint_perm, sigmaPoint_perm] at hz
      exact ⟨k, by rwa [segment_symm]⟩

theorem graph_subset_C : graph ⊆ C := by
  rintro z ⟨k, x, y, hx, hy, hxy, rfl⟩
  fin_cases k <;>
    simp only [Set.mem_setOf_eq, C, L, R, v, e] <;>
    norm_num [Complex.smul_re, Complex.smul_im] <;>
    split_ifs <;> (repeat' constructor) <;> linarith

theorem C_re_bounds {z : ℂ} (hz : z ∈ C) : 0 ≤ z.re ∧ z.re ≤ 6 := by
  rcases hz with ⟨hy0, hy2, hL, hR⟩
  dsimp [L] at hL
  dsimp [R] at hR
  split_ifs at hL hR <;> constructor <;> linarith

theorem C_bounded : Bornology.IsBounded C := by
  apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 8)).subset
  intro z hz
  have hx := C_re_bounds hz
  have hy : |z.im| ≤ 2 := abs_le.mpr ⟨hz.1, hz.2.1⟩
  have hb := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg hx.1] at hb
  change dist z 0 ≤ 8
  rw [dist_zero_right]
  linarith

lemma mem_graph_from_weights (k : Fin 9) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x+y=1)
    {z : ℂ} (hz : x • v (e k).1 + y • v (e k).2 = z) : z ∈ graph :=
  ⟨k, x, y, hx, hy, hxy, hz⟩

theorem J_subset_graph : J ⊆ graph := by
  rintro z ⟨hz, hb⟩
  have hx := C_re_bounds hz
  rcases hz with ⟨hy0, hy2, hL, hR⟩
  rcases hb with hb | hb | hb | hb
  · have hlow : 2 ≤ z.re := by
      norm_num [hb, L] at hL
      linarith
    apply mem_graph_from_weights 6 ((6-z.re)/4) ((z.re-2)/4)
      (by linarith) (by linarith) (by ring)
    apply Complex.ext <;> norm_num [e, v, Complex.smul_re, Complex.smul_im] <;> linarith
  · have hzero : z.re = 0 := by
      simp [hb, L, R] at hL hR
      linarith
    apply mem_graph_from_weights 4 1 0 (by norm_num) (by norm_num) (by norm_num)
    apply Complex.ext <;> norm_num [e, v, Complex.smul_re, Complex.smul_im] <;> linarith
  · by_cases hy1 : z.im ≤ -1
    · have hr : z.re = -2*z.im-2 := by simpa [L, hy1] using hb
      apply mem_graph_from_weights 7 (-z.im-1) (z.im+2)
        (by linarith) (by linarith) (by ring)
      apply Complex.ext <;> norm_num [e, v, Complex.smul_re, Complex.smul_im] <;> linarith
    · by_cases hyz : z.im ≤ 0
      · have hr : z.re = z.im+1 := by simpa [L, hy1, hyz] using hb
        apply mem_graph_from_weights 3 ((1-z.im)/2) ((z.im+1)/2)
          (by linarith) (by linarith) (by ring)
        apply Complex.ext <;> norm_num [e, v, Complex.smul_re, Complex.smul_im] <;> linarith
      · have hr : z.re = 1-z.im/2 := by simpa [L, hy1, hyz] using hb
        apply mem_graph_from_weights 8 ((2-z.im)/4) ((z.im+2)/4)
          (by linarith) (by linarith) (by ring)
        apply Complex.ext <;> norm_num [e, v, Complex.smul_re, Complex.smul_im] <;> linarith
  · by_cases hy1 : z.im ≤ 1
    · have hr : z.re = (10-4*z.im)/3 := by simpa [R, hy1] using hb
      apply mem_graph_from_weights 1 ((z.im+2)/3) ((1-z.im)/3)
        (by linarith) (by linarith) (by ring)
      apply Complex.ext <;> norm_num [e, v, Complex.smul_re, Complex.smul_im] <;> linarith
    · have hr : z.re = 4-2*z.im := by simpa [R, hy1] using hb
      apply mem_graph_from_weights 5 (z.im-1) (2-z.im)
        (by linarith) (by linarith) (by ring)
      apply Complex.ext <;> norm_num [e, v, Complex.smul_re, Complex.smul_im] <;> linarith

theorem p_not_mem_C : p ∉ C := by
  rintro ⟨h1,h2,h3,h4⟩
  norm_num [p, L] at h3

/-- Every exterior point has an entire straight unit-speed ray outside C. -/
theorem outside_has_escape {z : ℂ} (hz : z ∉ C) :
    ∃ d : ℂ, ‖d‖ = 1 ∧ ∀ t : ℝ, 0 ≤ t → z + t • d ∉ C := by
  by_cases hbot : z.im < -2
  · refine ⟨-Complex.I, by simp, ?_⟩
    intro t ht hc
    have hl : -2 ≤ (z + t • -Complex.I).im := hc.1
    simp [Complex.smul_im] at hl
    linarith
  by_cases htop : 2 < z.im
  · refine ⟨Complex.I, by simp, ?_⟩
    intro t ht hc
    have hu : (z + t • Complex.I).im ≤ 2 := hc.2.1
    simp [Complex.smul_im] at hu
    linarith
  by_cases hleft : z.re < L z.im
  · refine ⟨-1, by simp, ?_⟩
    intro t ht hc
    have hl : L (z + t • (-1 : ℂ)).im ≤ (z + t • (-1 : ℂ)).re := hc.2.2.1
    simp [Complex.smul_re, Complex.smul_im] at hl
    linarith
  have hright : R z.im < z.re := by
    by_contra h
    exact hz ⟨le_of_not_gt hbot, le_of_not_gt htop,
      le_of_not_gt hleft, le_of_not_gt h⟩
  refine ⟨1, by simp, ?_⟩
  intro t ht hc
  have hr : (z + t • (1 : ℂ)).re ≤ R (z + t • (1 : ℂ)).im := hc.2.2.2
  simp [Complex.smul_re, Complex.smul_im] at hr
  linarith

theorem compl_C_subset_rayExterior : Cᶜ ⊆ RayExterior graph := by
  intro z hz M hM
  obtain ⟨d, hd, he⟩ := outside_has_escape hz
  refine ⟨z + M • d, dist_along_unit z d hd M hM.le, ?_⟩
  apply Set.disjoint_left.mpr
  rintro w ⟨x, y, hx, hy, hxy, rfl⟩ hw
  have hh : x • z + y • (z + M • d) = z + (y*M) • d := by
    rw [smul_add, smul_smul, ← add_assoc, ← add_smul, hxy, one_smul]
  apply he (y*M) (mul_nonneg hy hM.le)
  rw [← hh]
  exact graph_subset_C hw

theorem rayExterior_graph_eq : RayExterior graph = Cᶜ := by
  apply Set.Subset.antisymm
  · apply rayExterior_subset_compl isClosed_C C_bounded
    rw [frontier_C_eq_J]
    exact J_subset_graph
  · exact compl_C_subset_rayExterior

theorem rayExterior_source_eq : RayExterior sourceGraph = Cᶜ := by
  rw [← graph_eq_sourceGraph]
  exact rayExterior_graph_eq

theorem frontier_source_eq_J : frontier (RayExterior sourceGraph) = J := by
  rw [rayExterior_source_eq, frontier_compl, frontier_C_eq_J]

theorem two_mem_interior_C : (2 : ℂ) ∈ interior C := by
  apply O_subset_interior_C
  norm_num [O, L, R]

theorem p_not_mem_closure_bounded_component (x : ℂ)
    (hb : Bornology.IsBounded (connectedComponentIn Jᶜ x)) :
    p ∉ closure (connectedComponentIn Jᶜ x) := by
  intro hp
  apply p_not_mem_C
  apply KovacecComponent.bounded_component_closure_subset isClosed_C
    (fun z hz => outside_has_escape hz) x
  · simpa only [frontier_C_eq_J] using hb
  · simpa only [frontier_C_eq_J] using hp

theorem exists_bounded_J_component : ∃ x : ℂ, x ∉ J ∧
    (connectedComponentIn Jᶜ x).Nonempty ∧
    Bornology.IsBounded (connectedComponentIn Jᶜ x) := by
  simpa only [frontier_C_eq_J] using
    KovacecComponent.exists_bounded_component isClosed_C C_bounded
      (show (interior C).Nonempty from ⟨2, two_mem_interior_C⟩)

#print axioms graph_eq_sourceGraph
#print axioms graph_subset_C
#print axioms J_subset_graph
#print axioms C_bounded
#print axioms p_not_mem_C
#print axioms rayExterior_source_eq
#print axioms p_not_mem_closure_bounded_component
#print axioms exists_bounded_J_component
end KovacecGraph
