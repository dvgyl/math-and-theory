import MilnePhysicalOrbitFilter
import MilneGeometryRange

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

/-- The actual trace-decreasing single-Kraus condition. -/
def KrausAdmissible (G : Matrix Q Q ℂ) : Prop :=
  (1-Gᴴ*G).PosSemidef

/-- Success probability on any canonical input whose Bob marginal is I/2. -/
def canonicalKrausProbability (G : Matrix Q Q ℂ) : ℝ :=
  (Matrix.trace (Gᴴ*G)).re/2

def scaledKraus (p : ℝ) (F : Matrix Q Q ℂ) : Matrix Q Q ℂ :=
  (Real.sqrt p : ℂ) • F

def normalizedKrausOutput (M : CMatrix) (G : Matrix Q Q ℂ) : CMatrix :=
  ((canonicalKrausProbability G)⁻¹ : ℂ) • complexFiltered M G

theorem scalar_spin_trace (s : ℝ) (v : V3) :
    Matrix.trace ((s:ℂ) • (1 : Matrix Q Q ℂ)+spin v) = (2*s : ℝ) := by
  apply Complex.ext <;>
    simp [Matrix.trace,Matrix.diag,spin,Fin.sum_univ_two,Matrix.one_apply]
  all_goals ring

theorem scalar_spin_blochSq (s : ℝ) (v : V3) :
    blochSq ((s:ℂ) • (1 : Matrix Q Q ℂ)+spin v) = 4*vSq v := by
  simp [blochSq,spin,vSq,Matrix.one_apply,Fin.sum_univ_three,
    Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

theorem scalar_spin_det (s : ℝ) (v : V3) :
    Matrix.det ((s:ℂ) • (1 : Matrix Q Q ℂ)+spin v) = ((s^2-vSq v:ℝ):ℂ) := by
  rw [Matrix.det_fin_two]
  apply Complex.ext <;>
    simp [spin,vSq,Matrix.one_apply,Fin.sum_univ_three,Complex.mul_re,Complex.mul_im,pow_two]
  all_goals ring

/-- Exact positivity test for every Hermitian qubit matrix, including zero
trace and rank-one cases. -/
theorem scalar_spin_psd_iff (s : ℝ) (v : V3) :
    ((s:ℂ) • (1 : Matrix Q Q ℂ)+spin v).PosSemidef ↔
      0 ≤ s ∧ vSq v ≤ s^2 := by
  constructor
  · intro h
    have ht := psd_trace_nonneg h
    have hb := blochSq_psd_le h
    rw [scalar_spin_trace] at ht hb
    rw [scalar_spin_blochSq] at hb
    simp only [Complex.ofReal_re] at ht hb
    exact ⟨by linarith,by nlinarith⟩
  · rintro ⟨hs,hv⟩
    have hH : ((s:ℂ) • (1 : Matrix Q Q ℂ)+spin v).IsHermitian := by
      change (((s:ℂ) • (1 : Matrix Q Q ℂ))+spin v)ᴴ = _
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.conjTranspose_apply,spin,Matrix.one_apply,Complex.star_def]
      all_goals ring
    have hsum : hH.eigenvalues 0+hH.eigenvalues 1 = 2*s := by
      have h := trace_eq_eigenvalue_sum hH
      rw [scalar_spin_trace] at h
      simpa [Fin.sum_univ_two] using h.symm
    have hprod : hH.eigenvalues 0*hH.eigenvalues 1 = s^2-vSq v := by
      have h := hH.det_eq_prod_eigenvalues
      rw [scalar_spin_det] at h
      have h' := congrArg Complex.re h
      simpa [Fin.prod_univ_two,Complex.mul_re,pow_two] using h'.symm
    have h0 : 0 ≤ hH.eigenvalues 0 := by
      by_contra hn
      have hn' : hH.eigenvalues 0 < 0 := lt_of_not_ge hn
      have hp : 0 < hH.eigenvalues 1 := by linarith
      have hm := mul_neg_of_neg_of_pos hn' hp
      linarith
    have h1 : 0 ≤ hH.eigenvalues 1 := by
      by_contra hn
      have hn' : hH.eigenvalues 1 < 0 := lt_of_not_ge hn
      have hp : 0 < hH.eigenvalues 0 := by linarith
      have hm := mul_neg_of_pos_of_neg hp hn'
      linarith
    apply hH.posSemidef_of_eigenvalues_nonneg
    intro i
    fin_cases i
    · exact h0
    · exact h1

theorem real_scaled_effect (F : Matrix Q Q ℂ) (s : ℝ) :
    ((s:ℂ) • F)ᴴ*((s:ℂ) • F) = ((s^2:ℝ):ℂ) • (Fᴴ*F) := by
  simp [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    Complex.star_def,← Complex.ofReal_mul,pow_two]

theorem complexFiltered_real_scaled (M : CMatrix) (F : Matrix Q Q ℂ) (s : ℝ) :
    complexFiltered M ((s:ℂ) • F) = ((s^2:ℝ):ℂ) • complexFiltered M F := by
  unfold complexFiltered
  rw [Matrix.conjTranspose_smul]
  have hs : star (s:ℂ) = (s:ℂ) := by simp
  rw [hs]
  simp only [onBob_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  simp only [pow_two,Complex.ofReal_mul]

theorem scaledKraus_effect (p : ℝ) (hp : 0 ≤ p) (F : Matrix Q Q ℂ) :
    (scaledKraus p F)ᴴ*scaledKraus p F = (p:ℂ) • (Fᴴ*F) := by
  rw [scaledKraus,real_scaled_effect,Real.sq_sqrt hp]

theorem canonicalKrausProbability_nonneg (G : Matrix Q Q ℂ) :
    0 ≤ canonicalKrausProbability G :=
  div_nonneg (psd_trace_nonneg (Matrix.posSemidef_conjTranspose_mul_self G)) (by norm_num)

theorem canonicalKrausProbability_le_one (G : Matrix Q Q ℂ)
    (hG : KrausAdmissible G) : canonicalKrausProbability G ≤ 1 := by
  have h := psd_trace_nonneg hG
  simp [Matrix.trace_sub,Matrix.trace_one,Q,Complex.sub_re] at h
  unfold canonicalKrausProbability
  linarith

theorem canonicalKrausProbability_is_actual (M : CMatrix)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) (G : Matrix Q Q ℂ) :
    (Matrix.trace (complexFiltered M G)).re = canonicalKrausProbability G := by
  rw [← trace_partialB,complexFiltered_bob_marginal M hB G,
    Matrix.trace_smul,Matrix.trace_mul_comm G Gᴴ]
  simp [canonicalKrausProbability,Complex.mul_re]
  ring

theorem scaledKraus_probability (p : ℝ) (hp : 0 ≤ p) (F : Matrix Q Q ℂ)
    (hTr : Matrix.trace (Fᴴ*F) = 2) : canonicalKrausProbability (scaledKraus p F) = p := by
  rw [canonicalKrausProbability,scaledKraus_effect p hp F,Matrix.trace_smul,hTr]
  simp [Complex.mul_re]

theorem scaledKraus_output (M : CMatrix) (p : ℝ) (hp : 0 < p)
    (F : Matrix Q Q ℂ) (hTr : Matrix.trace (Fᴴ*F) = 2) :
    normalizedKrausOutput M (scaledKraus p F) = complexFiltered M F := by
  rw [normalizedKrausOutput,scaledKraus_probability p (le_of_lt hp) F hTr]
  rw [scaledKraus,complexFiltered_real_scaled,Real.sq_sqrt (le_of_lt hp),smul_smul]
  simp [ne_of_gt hp]

/-- Exact Kraus feasibility at a prescribed success probability p and
normalized effect I+b.sigma. The scalar r is its physical Bloch length. -/
theorem scaledKraus_admissible_iff (p : ℝ) (hp : 0 ≤ p)
    (F : Matrix Q Q ℂ) (b : V3) (hF : Fᴴ*F = 1+spin b)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r^2 = vSq b) :
    KrausAdmissible (scaledKraus p F) ↔ p*(1+r) ≤ 1 := by
  have hid : 1-(p:ℂ) • (1+spin b) =
      ((1-p:ℝ):ℂ) • (1 : Matrix Q Q ℂ)+spin ((-p) • b) := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [spin,Matrix.one_apply,Pi.smul_apply,smul_eq_mul,
        Complex.mul_re,Complex.mul_im]
    all_goals ring
  rw [KrausAdmissible,scaledKraus_effect p hp F,hF,hid,scalar_spin_psd_iff,
    vSq_smul,← hr]
  constructor
  · rintro ⟨hp1,hsq⟩
    have hpr := mul_nonneg hp hr0
    nlinarith [sq_nonneg (1-p+p*r)]
  · intro h
    have hpr := mul_nonneg hp hr0
    have hp1 : 0 ≤ 1-p := by nlinarith
    have hdiff : 0 ≤ 1-p-p*r := by nlinarith
    have hsum : 0 ≤ 1-p+p*r := by nlinarith
    exact ⟨hp1,by nlinarith [mul_nonneg hdiff hsum]⟩

/-- Optimal success probability for a fixed normalized filter.  The endpoint
can be achieved as a true Kraus contraction, even when F is singular. -/
theorem fixed_filter_maximal_success (F : Matrix Q Q ℂ) (b : V3)
    (hTr : Matrix.trace (Fᴴ*F) = 2) (hF : Fᴴ*F = 1+spin b)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r^2 = vSq b) :
    let p := 1/(1+r)
    KrausAdmissible (scaledKraus p F) ∧
    canonicalKrausProbability (scaledKraus p F) = p ∧
    ∀ q : ℝ, 0 ≤ q → KrausAdmissible (scaledKraus q F) → q ≤ p := by
  have hd : 0 < 1+r := by linarith
  have hp : 0 ≤ 1/(1+r) := le_of_lt (one_div_pos.mpr hd)
  dsimp only
  refine ⟨?_,scaledKraus_probability _ hp F hTr,?_⟩
  · rw [scaledKraus_admissible_iff _ hp F b hF r hr0 hr]
    rw [one_div_mul_cancel (ne_of_gt hd)]
  · intro q hq hG
    have h := (scaledKraus_admissible_iff q hq F b hF r hr0 hr).mp hG
    exact (le_div_iff₀ hd).mpr h

theorem canonicalKrausProbability_trace (G : Matrix Q Q ℂ) :
    Matrix.trace (Gᴴ*G) = (2*canonicalKrausProbability G : ℝ) := by
  apply Complex.ext
  · simp [canonicalKrausProbability]
    ring
  · have hH := (Matrix.posSemidef_conjTranspose_mul_self G).1
    have h0 := hermitian_diag_im hH (0 : Q)
    have h1 := hermitian_diag_im hH (1 : Q)
    simp [Matrix.trace,Matrix.diag,Fin.sum_univ_two,h0,h1]

def normalizedCanonicalFilter (G : Matrix Q Q ℂ) : Matrix Q Q ℂ :=
  (((Real.sqrt (canonicalKrausProbability G))⁻¹ : ℝ) : ℂ) • G

/-- Every nonzero-probability physical Kraus operation has the normalized
filter representation used in the exact orbit theorem. -/
theorem normalizedCanonicalFilter_trace (G : Matrix Q Q ℂ)
    (hp : 0 < canonicalKrausProbability G) :
    Matrix.trace ((normalizedCanonicalFilter G)ᴴ*normalizedCanonicalFilter G) = 2 := by
  have hs0 : Real.sqrt (canonicalKrausProbability G) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hp)
  have hs2 := Real.sq_sqrt (le_of_lt hp)
  rw [normalizedCanonicalFilter,real_scaled_effect,Matrix.trace_smul,
    canonicalKrausProbability_trace]
  have hreal : ((Real.sqrt (canonicalKrausProbability G))⁻¹)^2 *
      (2*canonicalKrausProbability G) = 2 := by
    field_simp
  simp only [smul_eq_mul]
  exact_mod_cast hreal

theorem scaledKraus_normalization (G : Matrix Q Q ℂ)
    (hp : 0 < canonicalKrausProbability G) :
    scaledKraus (canonicalKrausProbability G) (normalizedCanonicalFilter G) = G := by
  have hs0 : Real.sqrt (canonicalKrausProbability G) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hp)
  simp [scaledKraus,normalizedCanonicalFilter,smul_smul,hs0]

theorem normalizedKrausOutput_eq_normalized_filter (M : CMatrix)
    (G : Matrix Q Q ℂ) (hp : 0 < canonicalKrausProbability G) :
    normalizedKrausOutput M G = complexFiltered M (normalizedCanonicalFilter G) := by
  have h := scaledKraus_output M (canonicalKrausProbability G) hp
    (normalizedCanonicalFilter G) (normalizedCanonicalFilter_trace G hp)
  rwa [scaledKraus_normalization G hp] at h

theorem normalizedKrausOutput_density (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (G : Matrix Q Q ℂ) (hp : 0 < canonicalKrausProbability G) :
    Density (normalizedKrausOutput M G) := by
  rw [normalizedKrausOutput_eq_normalized_filter M G hp]
  exact complexFiltered_density M hM hB _ (normalizedCanonicalFilter_trace G hp)

/-- Equality of normalized effects preserves both marginal purity and the
actual correlation norm. No polar-decomposition premise is required. -/
theorem canonical_complex_same_effect (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F G : Matrix Q Q ℂ) (hF : Matrix.trace (Fᴴ*F) = 2)
    (hG : Matrix.trace (Gᴴ*G) = 2) (hE : Fᴴ*F = Gᴴ*G) :
    blochSq (partialB (complexFiltered M F)) = blochSq (partialB (complexFiltered M G)) ∧
    correlationSq (complexFiltered M F) = correlationSq (complexFiltered M G) := by
  have hA : partialA (complexFiltered M F) = partialA (complexFiltered M G) := by
    rw [complexFiltered,complexFiltered,partialA_bob_cycle,partialA_bob_cycle,hE]
  have hdet : (F*Fᴴ).det = (G*Gᴴ).det := by
    calc
      (F*Fᴴ).det = (Fᴴ*F).det := by simp [Matrix.det_mul,mul_comm]
      _ = (Gᴴ*G).det := congrArg Matrix.det hE
      _ = (G*Gᴴ).det := by simp [Matrix.det_mul,mul_comm]
  have hDF := complexFiltered_det_bloch M hM hB F hF
  have hDG := complexFiltered_det_bloch M hM hB G hG
  have hbs : blochSq (partialB (complexFiltered M F)) =
      blochSq (partialB (complexFiltered M G)) := by rw [hdet] at hDF; linarith
  refine ⟨hbs,?_⟩
  rw [complexFiltered_correlation_identity M hM hB F hF,
    complexFiltered_correlation_identity M hM hB G hG,hbs,hA]

theorem canonical_complex_effect_radius (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (b : V3) (hF : Fᴴ*F = 1+spin b) :
    blochSq (partialB (complexFiltered M F)) = vSq b := by
  have hTr : Matrix.trace (Fᴴ*F) = 2 := by rw [hF,qubitBall_trace]
  have hdet : (F*Fᴴ).det = ((1-vSq b:ℝ):ℂ) := by
    rw [Matrix.det_mul,mul_comm,← Matrix.det_mul,hF,qubitBall_det]
  have h := complexFiltered_det_bloch M hM hB F hTr
  rw [hdet] at h
  simp only [Complex.ofReal_re] at h
  linarith

/-- The sharp joint centre/radius bound applies to every normalized complex
filter, not only to positive or Hermitian filters. -/
theorem canonical_complex_joint_bound (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (b : V3) (hF : Fᴴ*F = 1+spin b) :
    correlationSq (complexFiltered M F) ≤
      steeringQuadratic (center M) (Real.sqrt (vSq b)) := by
  have hTr : Matrix.trace (Fᴴ*F) = 2 := by rw [hF,qubitBall_trace]
  let E := Matrix.posSemidef_conjTranspose_mul_self F
  let P := E.sqrt
  have hP : P.IsHermitian := E.posSemidef_sqrt.1
  have hPP : P*P = Fᴴ*F := E.sqrt_mul_self
  have hTP : Matrix.trace (P*P) = 2 := by rw [hPP,hTr]
  have hTP' : Matrix.trace (Pᴴ*P) = 2 := by rw [hP.eq,hTP]
  have hEP : Fᴴ*F = Pᴴ*P := by rw [hP.eq,hPP]
  have hinv := canonical_complex_same_effect M hM hB F P hTr hTP' hEP
  have hbF := canonical_complex_effect_radius M hM hB F b hF
  have hbP : blochSq (partialB (complexFiltered M P)) = vSq b := by
    rw [← hinv.1,hbF]
  have hbound := filtered_steering_quadratic_bound M hM hB P hP hTP
  have hCP : complexFiltered M P = onBob P*M*onBob P := by
    rw [complexFiltered,hP.eq]
  change correlationSq (onBob P*M*onBob P) ≤ _ at hbound
  rw [← hCP] at hbound
  rw [blochLength,hbP] at hbound
  rw [hinv.2]
  exact hbound

/-- A success probability above one half rules out singular qubit Kraus
operators. No full-rank premise is imposed on the bipartite input. -/
theorem KrausAdmissible_det_ne_zero_of_success_gt_half (G : Matrix Q Q ℂ)
    (hG : KrausAdmissible G) (hp : 1/2 < canonicalKrausProbability G) :
    G.det ≠ 0 := by
  have hprob : 0 < canonicalKrausProbability G := by linarith
  let F := normalizedCanonicalFilter G
  have hTr : Matrix.trace (Fᴴ*F) = 2 := normalizedCanonicalFilter_trace G hprob
  rcases complex_filter_effect_coordinates F hTr with ⟨b,hb,hE⟩
  let r := Real.sqrt (vSq b)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = vSq b := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (b i)))
  have hscaled : KrausAdmissible (scaledKraus (canonicalKrausProbability G) F) := by
    rw [scaledKraus_normalization G hprob]
    exact hG
  have hcap := (scaledKraus_admissible_iff _ (le_of_lt hprob) F b hE r hr0 hr2).mp hscaled
  have hr1 : r < 1 := by
    by_contra hn
    have hm := mul_nonneg (le_of_lt hprob) (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith
  have hb1 : vSq b < 1 := by nlinarith
  intro hdetG
  have hdetF : F.det = 0 := by
    dsimp [F,normalizedCanonicalFilter]
    rw [Matrix.det_smul_of_tower,hdetG,smul_zero]
  have hdetE : (Fᴴ*F).det = 0 := by rw [Matrix.det_mul,hdetF,mul_zero]
  have h := congrArg Matrix.det hE
  rw [hdetE,qubitBall_det] at h
  have hre := congrArg Complex.re h
  simp only [Complex.zero_re,Complex.ofReal_re] at hre
  linarith

end Milne

#print axioms Milne.fixed_filter_maximal_success
#print axioms Milne.scaledKraus_output
#print axioms Milne.canonicalKrausProbability_is_actual

#print axioms Milne.normalizedKrausOutput_density
#print axioms Milne.canonical_complex_joint_bound
#print axioms Milne.KrausAdmissible_det_ne_zero_of_success_gt_half
