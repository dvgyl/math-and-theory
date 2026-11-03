import FilterAlgebra
import GlobalFinite

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace UnilateralCHSH.Reduction
noncomputable section

def canonicalMaximum (T : Matrix (Fin 3) (Fin 3) ℝ) (c : Vec) : ℝ :=
  Global.maximumValue (matProduct T T.transpose) (crossMatrix (matVec T c))
    (normSq c) (traceThree (matProduct T T.transpose))

theorem canonicalMaximum_nonneg (T : Matrix (Fin 3) (Fin 3) ℝ) (c : Vec) :
    0 ≤ canonicalMaximum T c := by
  let n : Vec := ![1,0,0]
  have hn : normSq n=1 := by norm_num [n, normSq, dot, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have ho : dot n 0=0 := by simp [dot]
  have hv : normSq (0:Vec)≤1 := by norm_num [normSq, dot]
  have hc := exact_bivector_filter_construction T c n 0 hn ho hv
  dsimp only at hc
  have hp := filteredPlaneValue_nonneg T c (fun i => -cross n 0 i) n
    (Real.sqrt (1-normSq (fun i => -cross n 0 i))) hn
  rw [hc] at hp
  have hm := Global.feasible_value_le_maximum (matProduct T T.transpose) (crossMatrix (matVec T c))
    (normSq c) (traceThree (matProduct T T.transpose)) (n,0) ⟨hn, ho, hv⟩
  exact le_trans hp hm

theorem filter_upper_bound_nondegenerate (T : Matrix (Fin 3) (Fin 3) ℝ)
    (c u n : Vec) (r : ℝ) (hn : normSq n=1) (hu : normSq u≤1)
    (hr : r^2+normSq u=1) (hne : r ≠ -1) (hq : (dot n u)^2<1) :
    filteredPlaneValue T c u n r ≤ canonicalMaximum T c := by
  let h := Real.sqrt (1-(dot n u)^2)
  let N : Vec := fun i => (1/h)*normal n u r i
  let V : Vec := fun i => (1/h)*cross n u i
  have hf : normSq N=1 ∧ dot N V=0 ∧ normSq V≤1 :=
    normalized_pair_feasible n u r hn hu hr hne hq
  have heq := exact_normalized_filter_reduction T c u n r hn hr hne hq
  change filteredPlaneValue T c u n r = (1-(dot n u)^2)*
    reducedObjective (matProduct T T.transpose) (crossMatrix (matVec T c))
      (normSq c) (traceThree (matProduct T T.transpose)) N V at heq
  have hfac : 0 < 1-(dot n u)^2 := sub_pos.mpr hq
  have hnonneg : 0 ≤ reducedObjective (matProduct T T.transpose) (crossMatrix (matVec T c))
      (normSq c) (traceThree (matProduct T T.transpose)) N V := by
    apply nonneg_of_mul_nonneg_left _ hfac
    rw [mul_comm, ← heq]
    exact filteredPlaneValue_nonneg T c u n r hn
  have hscale : filteredPlaneValue T c u n r ≤
      reducedObjective (matProduct T T.transpose) (crossMatrix (matVec T c))
        (normSq c) (traceThree (matProduct T T.transpose)) N V := by
    rw [heq]
    exact mul_le_of_le_one_left hnonneg (by nlinarith [sq_nonneg (dot n u)])
  have hm := Global.feasible_value_le_maximum (matProduct T T.transpose) (crossMatrix (matVec T c))
    (normSq c) (traceThree (matProduct T T.transpose)) (N,V) hf
  exact le_trans hscale hm

theorem parallel_rank_one_plane_zero (T : Matrix (Fin 3) (Fin 3) ℝ)
    (c u n : Vec) (hu : normSq u=1) (hq : (dot n u)^2=1) :
    filteredPlaneValue T c u n 0=0 := by
  have hc (x : Vec) (b : ℝ) : planeColumnValue n (filteredColumn u x 0 b)=0 := by
    have hnorm : normSq (filteredColumn u x 0 b)=normSq u*(dot u x+b)^2 := by
      simp [normSq, dot, filteredColumn, spatial]
      ring
    have hdot : dot n (filteredColumn u x 0 b)=dot n u*(dot u x+b) := by
      simp [dot, filteredColumn, spatial]
      ring
    rw [planeColumnValue, hnorm, hdot, mul_pow, hu, hq]
    ring
  unfold filteredPlaneValue
  rw [hc, hc, hc]
  ring

theorem every_filter_plane_le_canonicalMaximum (T : Matrix (Fin 3) (Fin 3) ℝ)
    (c u n : Vec) (hn : normSq n=1) (hu : normSq u≤1) :
    filteredPlaneValue T c u n (Real.sqrt (1-normSq u)) ≤ canonicalMaximum T c := by
  have hsq : (dot n u)^2≤1 := le_trans (dot_sq_le_norm n u hn) hu
  by_cases hq : (dot n u)^2<1
  · have hr : Real.sqrt (1-normSq u)^2+normSq u=1 := by
      rw [Real.sq_sqrt (sub_nonneg.mpr hu)]
      ring
    have hne : Real.sqrt (1-normSq u) ≠ -1 := by
      have hp := Real.sqrt_nonneg (1-normSq u)
      intro he
      linarith
    exact filter_upper_bound_nondegenerate T c u n _ hn hu hr hne hq
  · have hqeq : (dot n u)^2=1 := by linarith
    have hueq : normSq u=1 := by
      have h := dot_sq_le_norm n u hn
      linarith
    rw [hueq]
    norm_num only [sub_self, Real.sqrt_zero]
    rw [parallel_rank_one_plane_zero T c u n hueq hqeq]
    exact canonicalMaximum_nonneg T c

theorem canonicalMaximum_attained_by_filter (T : Matrix (Fin 3) (Fin 3) ℝ) (c : Vec) :
    ∃ u n : Vec, normSq u≤1 ∧ normSq n=1 ∧
      filteredPlaneValue T c u n (Real.sqrt (1-normSq u))=canonicalMaximum T c := by
  let p := Global.maximizer (matProduct T T.transpose) (crossMatrix (matVec T c))
    (normSq c) (traceThree (matProduct T T.transpose))
  have hp : p ∈ Global.feasible :=
    (Global.maximizer_spec (matProduct T T.transpose) (crossMatrix (matVec T c))
      (normSq c) (traceThree (matProduct T T.transpose))).1
  let u : Vec := fun i => -cross p.1 p.2 i
  have hu : normSq u≤1 := by
    rw [tangent_cross_norm p.1 p.2 hp.1 hp.2.1]
    exact hp.2.2
  refine ⟨u, p.1, hu, hp.1, ?_⟩
  exact exact_bivector_filter_construction T c p.1 p.2 hp.1 hp.2.1 hp.2.2

def filterPlaneValues (T : Matrix (Fin 3) (Fin 3) ℝ) (c : Vec) : Set ℝ :=
  {b | ∃ u n : Vec, normSq u≤1 ∧ normSq n=1 ∧
    filteredPlaneValue T c u n (Real.sqrt (1-normSq u))=b}

theorem exact_real_filter_maximum (T : Matrix (Fin 3) (Fin 3) ℝ) (c : Vec) :
    IsGreatest (filterPlaneValues T c) (canonicalMaximum T c) := by
  constructor
  · exact canonicalMaximum_attained_by_filter T c
  · rintro b ⟨u, n, hu, hn, heq⟩
    rw [← heq]
    exact every_filter_plane_le_canonicalMaximum T c u n hn hu


theorem scaled_maximum_equality (q b z : ℝ) (hb : 0 < b)
    (heq : b = (1-q^2)*z) (hz : z ≤ b) (hq : q^2 ≤ 1) : q=0 := by
  have hfac : 0 ≤ 1-q^2 := by linarith
  have hle := mul_le_mul_of_nonneg_left hz hfac
  rw [← heq] at hle
  have hs : q^2 ≤ 0 := by
    by_contra h
    have hp := mul_pos (lt_of_not_ge h) hb
    nlinarith
  nlinarith [sq_nonneg q]

theorem positive_optimum_normal_orthogonal (T : Matrix (Fin 3) (Fin 3) ℝ)
    (c u n : Vec) (hn : normSq n=1) (hu : normSq u≤1)
    (hpositive : 0 < canonicalMaximum T c)
    (hoptimal : filteredPlaneValue T c u n (Real.sqrt (1-normSq u))=canonicalMaximum T c) :
    dot n u=0 := by
  have hsq : (dot n u)^2≤1 := le_trans (dot_sq_le_norm n u hn) hu
  by_cases hq : (dot n u)^2<1
  · let r := Real.sqrt (1-normSq u)
    have hr : r^2+normSq u=1 := by
      dsimp only [r]
      rw [Real.sq_sqrt (sub_nonneg.mpr hu)]
      ring
    have hne : r ≠ -1 := by
      have hp := Real.sqrt_nonneg (1-normSq u)
      intro he
      dsimp only [r] at he
      linarith
    let h := Real.sqrt (1-(dot n u)^2)
    let N : Vec := fun i => (1/h)*normal n u r i
    let V : Vec := fun i => (1/h)*cross n u i
    have hf : normSq N=1 ∧ dot N V=0 ∧ normSq V≤1 :=
      normalized_pair_feasible n u r hn hu hr hne hq
    have heq := exact_normalized_filter_reduction T c u n r hn hr hne hq
    change filteredPlaneValue T c u n r = (1-(dot n u)^2)*
      reducedObjective (matProduct T T.transpose) (crossMatrix (matVec T c))
        (normSq c) (traceThree (matProduct T T.transpose)) N V at heq
    have hm := Global.feasible_value_le_maximum (matProduct T T.transpose)
      (crossMatrix (matVec T c)) (normSq c) (traceThree (matProduct T T.transpose)) (N,V) hf
    dsimp only [Global.objective] at hm
    apply scaled_maximum_equality (dot n u) (canonicalMaximum T c) _ hpositive _ hm hsq
    rw [← heq]
    exact hoptimal.symm
  · have hqeq : (dot n u)^2=1 := by linarith
    have hueq : normSq u=1 := by
      have h := dot_sq_le_norm n u hn
      linarith
    rw [hueq] at hoptimal
    norm_num only [sub_self, Real.sqrt_zero] at hoptimal
    rw [parallel_rank_one_plane_zero T c u n hueq hqeq] at hoptimal
    linarith

theorem tangent_filter_reduced_value (T : Matrix (Fin 3) (Fin 3) ℝ)
    (c u n : Vec) (hn : normSq n=1) (hu : normSq u≤1) (horth : dot n u=0) :
    filteredPlaneValue T c u n (Real.sqrt (1-normSq u)) =
      reducedObjective (matProduct T T.transpose) (crossMatrix (matVec T c))
        (normSq c) (traceThree (matProduct T T.transpose)) n (cross n u) := by
  have hr : Real.sqrt (1-normSq u)^2+normSq u=1 := by
    rw [Real.sq_sqrt (sub_nonneg.mpr hu)]
    ring
  have hne : Real.sqrt (1-normSq u) ≠ -1 := by
    have hp := Real.sqrt_nonneg (1-normSq u)
    intro he
    linarith
  have hq : (dot n u)^2<1 := by rw [horth]; norm_num
  have heq := exact_normalized_filter_reduction T c u n _ hn hr hne hq
  simpa [horth, normal] using heq

theorem positive_filter_optimality_iff (T : Matrix (Fin 3) (Fin 3) ℝ)
    (c u n : Vec) (hn : normSq n=1) (hu : normSq u≤1)
    (hpositive : 0 < canonicalMaximum T c) :
    filteredPlaneValue T c u n (Real.sqrt (1-normSq u))=canonicalMaximum T c ↔
      dot n u=0 ∧ reducedObjective (matProduct T T.transpose) (crossMatrix (matVec T c))
        (normSq c) (traceThree (matProduct T T.transpose)) n (cross n u)=canonicalMaximum T c := by
  constructor
  · intro hopt
    have horth := positive_optimum_normal_orthogonal T c u n hn hu hpositive hopt
    exact ⟨horth, by rwa [tangent_filter_reduced_value T c u n hn hu horth] at hopt⟩
  · rintro ⟨horth, hopt⟩
    rwa [tangent_filter_reduced_value T c u n hn hu horth]

end
end UnilateralCHSH.Reduction
