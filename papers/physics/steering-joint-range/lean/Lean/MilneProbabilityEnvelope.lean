import MilneKrausProbability
import MilneProbabilityScalar

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

/-- Correlation values obtained from an actual canonical density matrix of
centre length c by an actual contracting complex Kraus operator, with success
probability at least p. Singular Kraus operators are included. -/
def successPhysicalSpectrum (c p : ℝ) : Set ℝ :=
  {x | ∃ (M : CMatrix) (G : Matrix Q Q ℂ), Density M ∧
    partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ) ∧ center M = c ∧
    KrausAdmissible G ∧ 0 < canonicalKrausProbability G ∧
    p ≤ canonicalKrausProbability G ∧
    correlationSq (normalizedKrausOutput M G) = x}

/-- The radius restriction follows from Kraus positivity and the actual
success probability; it is not assumed as an independent physical premise. -/
theorem successPhysicalSpectrum_upper {c p x : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hp0 : 1/2 ≤ p) (hp1 : p ≤ 1)
    (hx : x ∈ successPhysicalSpectrum c p) : x ≤ successEnvelopeSq c p := by
  rcases hx with ⟨M,G,hM,hB,hc,hG,hprob,hp,hx⟩
  let F := normalizedCanonicalFilter G
  have hTr : Matrix.trace (Fᴴ*F) = 2 := normalizedCanonicalFilter_trace G hprob
  rcases complex_filter_effect_coordinates F hTr with ⟨b,hb,hE⟩
  let r := Real.sqrt (vSq b)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = vSq b := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (b i)))
  have hnorm : scaledKraus (canonicalKrausProbability G) F = G :=
    scaledKraus_normalization G hprob
  have hscaled : KrausAdmissible (scaledKraus (canonicalKrausProbability G) F) := by
    rw [hnorm]
    exact hG
  have hcap := (scaledKraus_admissible_iff _ (le_of_lt hprob) F b hE r hr0 hr2).mp hscaled
  have hpcap : p*(1+r) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ 1+r by linarith)
    exact hm.trans hcap
  have hrR := (success_radius_iff (show 0 < p by linarith)).mp hpcap
  have hR := successBudgetRadius_bounds hp0 hp1
  have hbound := canonical_complex_joint_bound M hM hB F b hE
  have hout : normalizedKrausOutput M G = complexFiltered M F :=
    normalizedKrausOutput_eq_normalized_filter M G hprob
  rw [← hout,hx,hc] at hbound
  exact hbound.trans (successOptimalRadius_maximizes hc0 hc1 hR.1 hR.2 hr0 hrR)

theorem endpointFilter_effect {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (endpointFilter r)ᴴ * endpointFilter r = 1+spin ((-r) • geometryEz) := by
  have h0 := Real.sq_sqrt (show 0 ≤ 1-r by linarith)
  have h1 := Real.sq_sqrt (show 0 ≤ 1+r by linarith)
  have h0C : (Real.sqrt (1-r):ℂ)^2 = (1-r:ℂ) := by exact_mod_cast h0
  have h1C : (Real.sqrt (1+r):ℂ)^2 = (1+r:ℂ) := by exact_mod_cast h1
  rw [endpointFilter_psd.1.eq]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [endpointFilter,Matrix.mul_apply,Matrix.diagonal_apply,Fin.sum_univ_two,
      spin,geometryEz,Pi.smul_apply,smul_eq_mul,Matrix.one_apply,
      Complex.mul_re,Complex.mul_im,← pow_two,h0,h1,h0C,h1C]
  all_goals ring

/-- Every radial upper-bound point has an explicit physical Kraus witness
at any permitted success probability p. -/
theorem successPhysicalSpectrum_contains_radial {c p r : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hp : 0 < p)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hcap : p*(1+r) ≤ 1) :
    steeringQuadratic c r ∈ successPhysicalSpectrum c p := by
  let F := endpointFilter r
  let G := scaledKraus p F
  have hTr : Matrix.trace (Fᴴ*F) = 2 := by
    rw [endpointFilter_psd.1.eq]
    exact endpointFilter_trace hr0 hr1
  have he : Fᴴ*F = 1+spin ((-r) • geometryEz) := endpointFilter_effect hr0 hr1
  have hr : r^2 = vSq ((-r) • geometryEz) := by
    rw [vSq_smul,geometryEz_unit]
    ring
  have hG : KrausAdmissible G :=
    (scaledKraus_admissible_iff p (le_of_lt hp) F _ he r hr0 hr).mpr hcap
  have hprob : canonicalKrausProbability G = p :=
    scaledKraus_probability p (le_of_lt hp) F hTr
  refine ⟨obese c,G,obese_density hc0 hc1,obese_partialB hc1,
    obese_center hc0 hc1,hG,?_,?_,?_⟩
  · rw [hprob]
    exact hp
  · rw [hprob]
  · rw [scaledKraus_output (obese c) p hp F hTr]
    have heq : complexFiltered (obese c) F = obeseFiltered c r := by
      rw [complexFiltered,endpointFilter_psd.1.eq]
      rfl
    rw [heq]
    exact obeseFiltered_correlationSq hc1 hr0 hr1

/-- Sharp maximum with a success floor p in [1/2,1]. This statement quantifies
actual complex Kraus contractions and normalized physical output states. -/
theorem successPhysicalSpectrum_isGreatest {c p : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hp0 : 1/2 ≤ p) (hp1 : p ≤ 1) :
    IsGreatest (successPhysicalSpectrum c p) (successEnvelopeSq c p) := by
  have hp : 0 < p := by linarith
  have hR := successBudgetRadius_bounds hp0 hp1
  have hr := successOptimalRadius_bounds hc0 hR.1
  constructor
  · apply successPhysicalSpectrum_contains_radial hc0 hc1 hp hr.1 (hr.2.trans hR.2)
    exact (success_radius_iff hp).mpr hr.2
  · intro x hx
    exact successPhysicalSpectrum_upper hc0 hc1 hp0 hp1 hx

/-- Exact activation frontier for actual probability-constrained Kraus
operations, including p=1/2 and rank-deficient outputs. -/
theorem successPhysicalSpectrum_violation_iff {c p : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hp0 : 1/2 ≤ p) (hp1 : p ≤ 1) :
    (∃ x ∈ successPhysicalSpectrum c p, 1 < x) ↔ c < successCriticalCenter p := by
  have hmax := successPhysicalSpectrum_isGreatest hc0 hc1 hp0 hp1
  rw [← successEnvelope_violation_iff_center hc0 hc1 hp0 hp1]
  constructor
  · rintro ⟨x,hx,hx1⟩
    exact lt_of_lt_of_le hx1 (hmax.2 hx)
  · intro h
    exact ⟨_,hmax.1,h⟩

/-- Reducing the success floor below one half creates no additional
normalized outputs: every qubit normalized effect can already be used
at actual success one half on a canonical input. -/
theorem successPhysicalSpectrum_low_probability {c p : ℝ} (hp : p ≤ 1/2) :
    successPhysicalSpectrum c p = successPhysicalSpectrum c (1/2) := by
  ext x
  constructor
  · rintro ⟨M,G,hM,hB,hc,hG,hprob,hpG,hx⟩
    let F := normalizedCanonicalFilter G
    have hTr : Matrix.trace (Fᴴ*F) = 2 := normalizedCanonicalFilter_trace G hprob
    rcases complex_filter_effect_coordinates F hTr with ⟨b,hb,hE⟩
    let r := Real.sqrt (vSq b)
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r^2 = vSq b := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (b i)))
    have hr1 : r ≤ 1 := by nlinarith
    have hcap : (1/2:ℝ)*(1+r) ≤ 1 := by linarith
    have hG' : KrausAdmissible (scaledKraus (1/2) F) :=
      (scaledKraus_admissible_iff (1/2) (by norm_num) F b hE r hr0 hr2).mpr hcap
    have hp' : canonicalKrausProbability (scaledKraus (1/2) F) = 1/2 :=
      scaledKraus_probability _ (by norm_num) F hTr
    refine ⟨M,scaledKraus (1/2) F,hM,hB,hc,hG',?_,?_,?_⟩
    · rw [hp']; norm_num
    · rw [hp']
    · rw [scaledKraus_output M (1/2) (by norm_num) F hTr,
        ← normalizedKrausOutput_eq_normalized_filter M G hprob]
      exact hx
  · rintro ⟨M,G,hM,hB,hc,hG,hprob,hpG,hx⟩
    exact ⟨M,G,hM,hB,hc,hG,hprob,hp.trans hpG,hx⟩

/-- The loose-budget branch is an attained maximum, including c>=2/3,
where its witnesses use rank-one Kraus operations. -/
theorem looseSuccessPhysicalSpectrum_isGreatest {c p : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hp : p ≤ 1/2) :
    IsGreatest (successPhysicalSpectrum c p) (steeringEnvelopeSq c) := by
  rw [successPhysicalSpectrum_low_probability hp,← successEnvelope_half hc0]
  exact successPhysicalSpectrum_isGreatest hc0 hc1 (by norm_num) (by norm_num)


end Milne

#print axioms Milne.successPhysicalSpectrum_isGreatest
#print axioms Milne.successPhysicalSpectrum_violation_iff

#print axioms Milne.successPhysicalSpectrum_low_probability
#print axioms Milne.looseSuccessPhysicalSpectrum_isGreatest
