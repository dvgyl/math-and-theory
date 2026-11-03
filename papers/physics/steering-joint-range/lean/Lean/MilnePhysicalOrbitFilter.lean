import MilneComplexFiltering
import MilnePhysicalOrbit
import MilneQubitBall

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

/-- Coordinates of a trace-two Hermitian qubit effect. -/
def traceTwoVector (A : Matrix Q Q ℂ) : V3 :=
  ![(A 0 1).re, -(A 0 1).im, ((A 0 0).re-(A 1 1).re)/2]

theorem traceTwo_reconstruction (A : Matrix Q Q ℂ) (hA : A.IsHermitian)
    (ht : Matrix.trace A = 2) : A = 1+spin (traceTwoVector A) := by
  have hd0 := hermitian_diag_im hA (0 : Q)
  have hd1 := hermitian_diag_im hA (1 : Q)
  have hr : (A 0 0).re+(A 1 1).re = 2 := by
    have h := congrArg Complex.re ht
    simpa [Matrix.trace,Matrix.diag,Fin.sum_univ_two] using h
  have h01 := hA.apply (0 : Q) (1 : Q)
  have h01r : (A 1 0).re = (A 0 1).re := by
    simpa [Complex.star_def] using congrArg Complex.re h01
  have h01i : (A 1 0).im = -(A 0 1).im := by
    have h := congrArg Complex.im h01
    simp only [Complex.star_def,Complex.conj_im] at h
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [traceTwoVector,spin,Matrix.one_apply,Complex.mul_re,Complex.mul_im,
      hd0,hd1,h01r,h01i]
  all_goals linarith

/-- Every normalized complex local filter has a physical Bloch-ball effect. -/
theorem complex_filter_effect_coordinates (F : Matrix Q Q ℂ)
    (hTr : Matrix.trace (Fᴴ*F) = 2) :
    ∃ b : V3, vSq b ≤ 1 ∧ Fᴴ*F = 1+spin b := by
  let b := traceTwoVector (Fᴴ*F)
  have hE : (Fᴴ*F).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self F
  have he : Fᴴ*F = 1+spin b := traceTwo_reconstruction _ hE.1 hTr
  have hQ : ((1/2:ℂ) • (Fᴴ*F)).PosSemidef := by
    simpa using psd_real_smul hE (1/2) (by norm_num)
  have hqEq : (1/2:ℂ) • (Fᴴ*F) = qubitState b := by rw [he]; rfl
  rw [hqEq] at hQ
  have h := blochSq_psd_le hQ
  rw [qubitState_blochSq,qubitState_trace] at h
  norm_num at h
  exact ⟨b,h,he⟩

theorem canonical_complex_filtered_alice (c b : V3) (S : T3)
    (F : Matrix Q Q ℂ) (hF : Fᴴ*F = 1+spin b) :
    partialA (complexFiltered (blochState c 0 S) F) = qubitState (c+tVec S b) := by
  rw [complexFiltered,partialA_bob_cycle,hF]
  exact canonical_bobWeighted_fano c b S

/-- The real quadratic objective equals the actual Pauli correlation norm
after any normalized complex local filter, including singular filters. -/
theorem canonical_complex_filter_correlation (c b : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef)
    (F : Matrix Q Q ℂ) (hF : Fᴴ*F = 1+spin b) :
    correlationSq (complexFiltered (blochState c 0 S) F) =
      orbitQuadratic (tSq S) (ttVec S c) (orbitK c S) b := by
  let M := blochState c 0 S
  have hD : Density M := blochState_density c 0 S hM
  have hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ) := blochState_canonical c S
  have hTr : Matrix.trace (Fᴴ*F) = 2 := by rw [hF,qubitBall_trace]
  have hdet : (F*Fᴴ).det = ((1-vSq b:ℝ):ℂ) := by
    rw [Matrix.det_mul,mul_comm,← Matrix.det_mul,hF,qubitBall_det]
  have hd := complexFiltered_det_bloch M hD hB F hTr
  rw [hdet] at hd
  have hb : blochSq (partialB (complexFiltered M F)) = vSq b := by
    simp only [Complex.ofReal_re] at hd
    linarith
  have ha : blochSq (partialA (complexFiltered M F)) = vSq (c+tVec S b) := by
    rw [canonical_complex_filtered_alice c b S F hF,qubitState_blochSq]
  have hc : center M ^ 2 = vSq c := by
    rw [blochState_center_formula,Real.sq_sqrt]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h := complexFiltered_correlation_identity M hD hB F hTr
  rw [hb,ha,hc,blochState_correlationSq] at h
  rw [orbit_physical_quadratic_identity]
  exact h

/-- Every closed-ball point is realized by a positive physical filter.
The open-ball witnesses are invertible; no state-rank assumption is needed. -/
theorem canonical_filter_realizes_ball (c b : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) (hb : vSq b ≤ 1) :
    let F := qubitBallFilter b hb
    Matrix.trace (Fᴴ*F) = 2 ∧
    Density (complexFiltered (blochState c 0 S) F) ∧
    correlationSq (complexFiltered (blochState c 0 S) F) =
      orbitQuadratic (tSq S) (ttVec S c) (orbitK c S) b := by
  let F := qubitBallFilter b hb
  have hF : Fᴴ*F = 1+spin b := by
    rw [(qubitBallFilter_hermitian b hb).eq,qubitBallFilter_squared]
  have hTr : Matrix.trace (Fᴴ*F) = 2 := by rw [hF,qubitBall_trace]
  exact ⟨hTr,complexFiltered_density _ (blochState_density _ _ _ hM)
    (blochState_canonical _ _) F hTr,canonical_complex_filter_correlation c b S hM F hF⟩

/-- Complete criterion for an actual one-sided filtered F3 violation.
The existential quantifier ranges over all normalized complex filters,
including rank-deficient ones; no boundary or quadratic-model premise is
assumed. Positivity of the original 4 by 4 canonical state is the only
physical hypothesis. -/
theorem canonical_complex_filter_violation_iff (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) :
    (∃ F : Matrix Q Q ℂ, Matrix.trace (Fᴴ*F) = 2 ∧
      1 < correlationSq (complexFiltered (blochState c 0 S) F)) ↔
    (orbitK c S).PosDef ∧
      vSq (orbitVertex (ttVec S c) (orbitK c S)) < 1 ∧
      1 < tSq S+vDot (ttVec S c) (orbitVertex (ttVec S c) (orbitK c S)) := by
  rw [← physical_orbit_violation_iff c S hM]
  constructor
  · rintro ⟨F,hTr,hviol⟩
    obtain ⟨b,hb,hF⟩ := complex_filter_effect_coordinates F hTr
    have hcorr := canonical_complex_filter_correlation c b S hM F hF
    have hval : 1 < orbitQuadratic (tSq S) (ttVec S c) (orbitK c S) b := by
      rwa [hcorr] at hviol
    have hlt : vSq b < 1 := by
      by_contra hn
      have he : vSq b = 1 := le_antisymm hb (le_of_not_gt hn)
      have hbound := orbit_physical_boundary c S hM b he
      linarith
    exact ⟨b,hlt,hval⟩
  · rintro ⟨b,hb,hviol⟩
    have h := canonical_filter_realizes_ball c b S hM (le_of_lt hb)
    dsimp only at h
    exact ⟨qubitBallFilter b (le_of_lt hb),h.1,by rwa [h.2.2]⟩

/-- Once the quadratic vertex is inside the Bloch ball and K is positive
definite, its value is the attained exact maximum over all complex filters.
Every maximizing filter has the same positive effect. -/
theorem canonical_complex_filter_optimum (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) (hK : (orbitK c S).PosDef)
    (hin : vSq (orbitVertex (ttVec S c) (orbitK c S)) < 1) :
    let p := orbitVertex (ttVec S c) (orbitK c S)
    let V := tSq S+vDot (ttVec S c) p
    (∃ F : Matrix Q Q ℂ, Matrix.trace (Fᴴ*F) = 2 ∧ F.det ≠ 0 ∧
      correlationSq (complexFiltered (blochState c 0 S) F) = V) ∧
    (∀ F : Matrix Q Q ℂ, Matrix.trace (Fᴴ*F) = 2 →
      correlationSq (complexFiltered (blochState c 0 S) F) ≤ V) ∧
    (∀ F : Matrix Q Q ℂ, Matrix.trace (Fᴴ*F) = 2 →
      correlationSq (complexFiltered (blochState c 0 S) F) = V → Fᴴ*F = 1+spin p) := by
  let p := orbitVertex (ttVec S c) (orbitK c S)
  have hopt := orbit_inverse_optimum (tSq S) (ttVec S c) (orbitK c S) hK
  have hw := canonical_filter_realizes_ball c p S hM (le_of_lt hin)
  dsimp only at hw ⊢
  refine ⟨?_,?_,?_⟩
  · refine ⟨qubitBallFilter p (le_of_lt hin),hw.1,qubitBallFilter_det_ne_zero p hin,?_⟩
    exact hw.2.2.trans hopt.1
  · intro F hTr
    obtain ⟨b,hb,hF⟩ := complex_filter_effect_coordinates F hTr
    rw [canonical_complex_filter_correlation c b S hM F hF]
    exact hopt.2.1 b
  · intro F hTr hval
    obtain ⟨b,hb,hF⟩ := complex_filter_effect_coordinates F hTr
    rw [canonical_complex_filter_correlation c b S hM F hF] at hval
    have he := hopt.2.2 b hval
    rwa [he] at hF

end Milne
