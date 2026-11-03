import UnilateralCHSH

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace UnilateralCHSH.Reduction
noncomputable section

def normal (n u : Vec) (r : ℝ) : Vec :=
  fun i => n i-dot n u/(1+r)*u i

theorem normal_dot (n u x : Vec) (r : ℝ) :
    dot (normal n u r) x = dot n x-dot n u/(1+r)*dot u x := by
  simp only [normal, dot, div_eq_mul_inv]
  ring

theorem normal_norm_expansion (n u : Vec) (r : ℝ) :
    normSq (normal n u r) = normSq n-2*(dot n u/(1+r))*dot n u+
      (dot n u/(1+r))^2*normSq u := by
  simp only [normSq, dot, normal, div_eq_mul_inv]
  ring

theorem normal_scalar_coefficient (r a : ℝ) (hr : r^2+a=1) (hne : r ≠ -1) :
    2/(1+r)-a/(1+r)^2 = 1 := by
  have ha : a=1-r^2 := by linarith
  have hd : 1+r ≠ 0 := by intro h; apply hne; linarith
  rw [ha]
  field_simp
  ring

theorem normal_norm (n u : Vec) (r : ℝ)
    (hn : normSq n=1) (hr : r^2+normSq u=1) (hne : r ≠ -1) :
    normSq (normal n u r) = 1-(dot n u)^2 := by
  have hc := normal_scalar_coefficient r (normSq u) hr hne
  have hd : 1+r ≠ 0 := by intro h; apply hne; linarith
  rw [normal_norm_expansion, hn]
  calc
    _ = 1-(dot n u)^2*(2/(1+r)-normSq u/(1+r)^2) := by field_simp [hd]; ring
    _ = _ := by rw [hc]; ring

theorem normal_dot_u (n u : Vec) (r : ℝ)
    (hr : r^2+normSq u=1) (hne : r ≠ -1) :
    dot (normal n u r) u = r*dot n u := by
  rw [normal_dot]
  change dot n u-dot n u/(1+r)*normSq u = _
  have hc := boost_scalar_fixed r (normSq u) hne hr
  calc
    _ = dot n u*(1-normSq u/(1+r)) := by ring
    _ = _ := by
      have hm := congrArg (fun z : ℝ => z*dot n u) hc
      dsimp only at hm
      nlinarith [hm]

theorem normal_dot_n (n u : Vec) (r : ℝ) (hn : normSq n=1) :
    dot (normal n u r) n = 1-(dot n u)^2/(1+r) := by
  rw [normal_dot, dot_symm u n]
  change normSq n-dot n u/(1+r)*dot n u = _
  rw [hn]
  ring

theorem cross_norm (n u : Vec) (hn : normSq n=1) :
    normSq (cross n u) = normSq u-(dot n u)^2 := by
  rw [cross_normSq, hn]
  ring

theorem normal_orth_cross (n u : Vec) (r : ℝ) :
    dot (normal n u r) (cross n u) = 0 := by
  rw [normal_dot, cross_orthogonal_left, cross_orthogonal_right]
  ring

theorem dot_sq_le_norm (n u : Vec) (hn : normSq n=1) :
    (dot n u)^2 ≤ normSq u := by
  have hp := normSq_nonneg (cross n u)
  rw [cross_norm n u hn] at hp
  linarith

theorem cross_dot_cross (x y z w : Vec) :
    dot (cross x y) (cross z w) = dot x z*dot y w-dot x w*dot y z := by
  simp [cross, dot]
  ring

theorem normal_cross_linear (d n u : Vec) (r : ℝ)
    (hn : normSq n=1) (hr : r^2+normSq u=1) (hne : r ≠ -1) :
    dot (cross n u) (cross d (normal n u r)) =
      r*dot n u*dot n d-(1-(dot n u)^2/(1+r))*dot u d := by
  rw [cross_dot_cross, dot_symm u (normal n u r), dot_symm n (normal n u r),
      normal_dot_u n u r hr hne, normal_dot_n n u r hn]
  ring

theorem normal_quad (A : Matrix (Fin 3) (Fin 3) ℝ) (n u : Vec) (r : ℝ) :
    quad A (normal n u r) = quad A n+(dot n u/(1+r))^2*quad A u-
      dot n u/(1+r)*(dot n (matVec A u)+dot u (matVec A n)) := by
  simp only [quad, dot, matVec, normal, div_eq_mul_inv]
  ring

theorem normalized_pair_feasible (n u : Vec) (r : ℝ)
    (hn : normSq n=1) (hu : normSq u ≤ 1)
    (hr : r^2+normSq u=1) (hne : r ≠ -1) (hq : (dot n u)^2 < 1) :
    let h := Real.sqrt (1-(dot n u)^2)
    let N : Vec := fun i => (1/h)*normal n u r i
    let V : Vec := fun i => (1/h)*cross n u i
    normSq N=1 ∧ dot N V=0 ∧ normSq V≤1 := by
  dsimp only
  have hpos : 0 < 1-(dot n u)^2 := sub_pos.mpr hq
  have hs := Real.sq_sqrt (le_of_lt hpos)
  have hnonzero : Real.sqrt (1-(dot n u)^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  rw [normSq_scale, normSq_scale, dot_scale_both, normal_norm n u r hn hr hne,
      normal_orth_cross, cross_norm n u hn]
  constructor
  · rw [one_div_pow, hs]
    field_simp
  constructor
  · ring
  · rw [one_div_pow, hs]
    have heq : (1/(1-(dot n u)^2))*(normSq u-(dot n u)^2) =
        (normSq u-(dot n u)^2)/(1-(dot n u)^2) := by ring
    rw [heq]
    apply (div_le_one hpos).mpr
    linarith

theorem spatial_dot (u n x : Vec) (r : ℝ) :
    dot (spatial u r n) x = r*dot n x+dot n u/(1+r)*dot u x := by
  simp only [spatial, dot, div_eq_mul_inv]
  ring

theorem spatial_quad (A : Matrix (Fin 3) (Fin 3) ℝ) (n u : Vec) (r : ℝ) :
    quad A (spatial u r n) = r^2*quad A n+(dot n u/(1+r))^2*quad A u+
      r*dot n u/(1+r)*(dot n (matVec A u)+dot u (matVec A n)) := by
  simp only [quad, dot, matVec, spatial, div_eq_mul_inv]
  ring

theorem reduction_quadratic_identity (A : Matrix (Fin 3) (Fin 3) ℝ)
    (n u : Vec) (r : ℝ) (hn : normSq n=1) (hr : r^2+normSq u=1) (hne : r ≠ -1) :
    r^2*traceThree A+quad A u-quad A (spatial u r n) =
      (1-(dot n u)^2)*traceThree A-quad A (normal n u r)-quad A (cross n u) := by
  have hd : 1+r ≠ 0 := by intro h; apply hne; linarith
  have hu : normSq u=1-r^2 := by linarith
  rw [spatial_quad, normal_quad, cross_quad_identity, hn, hu]
  field_simp
  ring

theorem reduction_linear_identity (d n u : Vec) (r : ℝ)
    (hn : normSq n=1) (hr : r^2+normSq u=1) (hne : r ≠ -1) :
    dot u d-dot n u*dot (spatial u r n) d =
      -dot (cross n u) (matVec (crossMatrix d) (normal n u r)) := by
  rw [spatial_dot, crossMatrix_apply, normal_cross_linear d n u r hn hr hne]
  ring

theorem filtered_projection (u n x : Vec) (r b : ℝ) :
    dot n (filteredColumn u x r b) = dot (spatial u r n) x+dot n u*b := by
  simp only [dot, filteredColumn, spatial, div_eq_mul_inv]
  ring

theorem filtered_column_norm (u x : Vec) (r b : ℝ)
    (hr : r^2+normSq u=1) (hne : r ≠ -1) :
    normSq (filteredColumn u x r b) =
      r^2*normSq x+(dot u x)^2+2*b*dot u x+normSq u*b^2 := by
  rw [normSq, filtered_gram_identity u x x r b b hne hr]
  have h : normSq u=1-r^2 := by linarith
  rw [h]
  unfold normSq
  ring

theorem general_filtered_plane_expansion (T : Matrix (Fin 3) (Fin 3) ℝ)
    (c u n : Vec) (r : ℝ) (hr : r^2+normSq u=1) (hne : r ≠ -1) :
    filteredPlaneValue T c u n r =
      r^2*traceThree (matProduct T T.transpose)+quad (matProduct T T.transpose) u-
      quad (matProduct T T.transpose) (spatial u r n)+
      2*(dot u (matVec T c)-dot n u*dot (spatial u r n) (matVec T c))+
      normSq c*(normSq u-(dot n u)^2) := by
  unfold filteredPlaneValue planeColumnValue
  rw [filtered_column_norm u (column T 0) r (c 0) hr hne,
      filtered_column_norm u (column T 1) r (c 1) hr hne,
      filtered_column_norm u (column T 2) r (c 2) hr hne,
      filtered_projection, filtered_projection, filtered_projection,
      covariance_trace, covariance_quad, covariance_quad, covariance_linear, covariance_linear]
  simp only [normSq, dot]
  ring

theorem unnormalized_filter_reduction (T : Matrix (Fin 3) (Fin 3) ℝ)
    (c u n : Vec) (r : ℝ) (hn : normSq n=1)
    (hr : r^2+normSq u=1) (hne : r ≠ -1) :
    filteredPlaneValue T c u n r =
      (1-(dot n u)^2)*traceThree (matProduct T T.transpose)-
      quad (matProduct T T.transpose) (normal n u r)-quad (matProduct T T.transpose) (cross n u)+
      normSq c*normSq (cross n u)-
      2*dot (cross n u) (matVec (crossMatrix (matVec T c)) (normal n u r)) := by
  rw [general_filtered_plane_expansion T c u n r hr hne,
      reduction_quadratic_identity (matProduct T T.transpose) n u r hn hr hne,
      reduction_linear_identity (matVec T c) n u r hn hr hne,
      cross_norm n u hn]
  ring

theorem reduced_scaled (A C : Matrix (Fin 3) (Fin 3) ℝ)
    (s t a : ℝ) (n v : Vec) :
    reducedObjective A C s t (fun i => a*n i) (fun i => a*v i) =
      t-a^2*quad A n-a^2*quad (shift A (-s)) v-2*a^2*dot v (matVec C n) := by
  unfold reducedObjective
  rw [matVec_scale, matVec_scale, matVec_scale, dot_scale_both, dot_scale_both, dot_scale_both]
  unfold quad
  ring

theorem reduced_normalized (A C : Matrix (Fin 3) (Fin 3) ℝ)
    (s t h : ℝ) (n v : Vec) (hh : h ≠ 0) :
    h^2*reducedObjective A C s t (fun i => (1/h)*n i) (fun i => (1/h)*v i) =
      h^2*t-quad A n-quad A v+s*normSq v-2*dot v (matVec C n) := by
  rw [reduced_scaled, quad_shift]
  field_simp
  ring

theorem exact_normalized_filter_reduction (T : Matrix (Fin 3) (Fin 3) ℝ)
    (c u n : Vec) (r : ℝ) (hn : normSq n=1)
    (hr : r^2+normSq u=1) (hne : r ≠ -1) (hq : (dot n u)^2 < 1) :
    let h := Real.sqrt (1-(dot n u)^2)
    let N : Vec := fun i => (1/h)*normal n u r i
    let V : Vec := fun i => (1/h)*cross n u i
    filteredPlaneValue T c u n r =
      (1-(dot n u)^2)*reducedObjective (matProduct T T.transpose)
        (crossMatrix (matVec T c)) (normSq c) (traceThree (matProduct T T.transpose)) N V := by
  dsimp only
  have hpos : 0 < 1-(dot n u)^2 := sub_pos.mpr hq
  have hs := Real.sq_sqrt (le_of_lt hpos)
  have hnonzero : Real.sqrt (1-(dot n u)^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hnorm := reduced_normalized (matProduct T T.transpose) (crossMatrix (matVec T c))
    (normSq c) (traceThree (matProduct T T.transpose)) (Real.sqrt (1-(dot n u)^2))
    (normal n u r) (cross n u) hnonzero
  rw [hs] at hnorm
  rw [unnormalized_filter_reduction T c u n r hn hr hne]
  exact hnorm.symm

theorem planeColumnValue_nonneg (n z : Vec) (hn : normSq n=1) :
    0 ≤ planeColumnValue n z := sub_nonneg.mpr (dot_sq_le_norm n z hn)

theorem filteredPlaneValue_nonneg (T : Matrix (Fin 3) (Fin 3) ℝ)
    (c u n : Vec) (r : ℝ) (hn : normSq n=1) : 0 ≤ filteredPlaneValue T c u n r := by
  unfold filteredPlaneValue
  exact add_nonneg (add_nonneg (planeColumnValue_nonneg n _ hn)
    (planeColumnValue_nonneg n _ hn)) (planeColumnValue_nonneg n _ hn)

end
end UnilateralCHSH.Reduction
