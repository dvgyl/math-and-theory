module
public import MilneOptimality
public import MilneFractionSharpness

@[expose] public section

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Milne

/-- The fully entangled fraction, defined by optimizing the actual overlap
over all normalized maximally entangled two-qubit vectors. -/
def fullyEntangledFraction (M : CMatrix) : ℝ :=
  sSup {x : ℝ | ∃ v : QQ → ℂ, MaximallyEntangled v ∧ overlap M v = x}

theorem fullyEntangledFraction_bound (M : CMatrix) (hM : Density M) :
    fullyEntangledFraction M ≤ 1 - steeringCenter M hM / 2 := by
  apply csSup_le
  · exact ⟨overlap M bellPlus, bellPlus, bellPlus_maximallyEntangled, rfl⟩
  · rintro x ⟨v,hv,hx⟩
    rw [← hx]
    exact all_states_entangled_overlap_bound M hM v hv

theorem overlap_le_fullyEntangledFraction (M : CMatrix) (hM : Density M)
    (v : QQ → ℂ) (hv : MaximallyEntangled v) :
    overlap M v ≤ fullyEntangledFraction M := by
  apply le_csSup
  · refine ⟨1 - steeringCenter M hM / 2, ?_⟩
    rintro x ⟨w,hw,hx⟩
    rw [← hx]
    exact all_states_entangled_overlap_bound M hM w hw
  · exact ⟨v,hv,rfl⟩

/-- At every allowed center, a physical state and a maximally entangled
vector saturate the bound, including the singular endpoint at c = 1. -/
theorem all_states_entangled_fraction_overlap_attained {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∃ (M : CMatrix) (hM : Density M) (v : QQ → ℂ),
      steeringCenter M hM = c ∧ MaximallyEntangled v ∧ overlap M v = 1-c/2 := by
  by_cases hc : c < 1
  · obtain ⟨M,hM,v,hd,hcen,hv,hov⟩ := entangled_fraction_attained hc0 hc
    exact ⟨M,hM,v,(steeringCenter_of_nonsingular M hM hd).trans hcen,hv,hov⟩
  · have hc : c = 1 := le_antisymm hc1 (le_of_not_gt hc)
    subst c
    let M := obeseFiltered 1 1
    have hM : Density M := obeseFiltered_density (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    refine ⟨M,hM,bellPlus,?_,bellPlus_maximallyEntangled,?_⟩
    · change (if (partialB (obeseFiltered 1 1)).det = 0 then
        center (obeseFiltered 1 1) else center (canonicalize M hM)) = 1
      rw [if_pos fraction_endpoint_bob_singular, fraction_endpoint_center]
    · norm_num [M, fraction_endpoint_overlap]

/-- Exact saturation of the standard fully entangled fraction, rather
than only saturation of a prescribed overlap. -/
theorem fullyEntangledFraction_attained {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∃ (M : CMatrix) (hM : Density M), steeringCenter M hM = c ∧
      fullyEntangledFraction M = 1-c/2 := by
  obtain ⟨M,hM,v,hcen,hv,hov⟩ :=
    all_states_entangled_fraction_overlap_attained hc0 hc1
  refine ⟨M,hM,hcen,le_antisymm ?_ ?_⟩
  · simpa [hcen] using fullyEntangledFraction_bound M hM
  · rw [← hov]
    exact overlap_le_fullyEntangledFraction M hM v hv

/-- The physically attainable fully entangled fractions at fixed center. -/
def entangledFractionSpectrum (c : ℝ) : Set ℝ :=
  {x | ∃ (M : CMatrix) (hM : Density M),
    steeringCenter M hM = c ∧ fullyEntangledFraction M = x}

/-- A complete extremal characterization: 1-c/2 is the maximum fully
entangled fraction over all two-qubit states of steering center c. -/
theorem fullyEntangledFraction_isGreatest {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsGreatest (entangledFractionSpectrum c) (1-c/2) := by
  constructor
  · exact fullyEntangledFraction_attained hc0 hc1
  · rintro x ⟨M,hM,hcen,hf⟩
    have h := fullyEntangledFraction_bound M hM
    rwa [hcen,hf] at h

theorem entangledFractionEnvelope_isGreatest {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsGreatest (entangledFractionSpectrum c) (1-c/2) :=
  fullyEntangledFraction_isGreatest hc0 hc1

/-- Unlike the interior flat branch, the endpoint c = 1 has an actual
maximizer: the pure product state obtained at the endpoint filter. -/
theorem steeringEndpoint_isGreatest : IsGreatest (steeringSpectrum 1) 1 := by
  constructor
  · let M := obeseFiltered 1 1
    have hM : Density M := obeseFiltered_density (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    refine ⟨M,hM,?_,?_⟩
    · change (if (partialB (obeseFiltered 1 1)).det = 0 then
        center (obeseFiltered 1 1) else center (canonicalize M hM)) = 1
      rw [if_pos fraction_endpoint_bob_singular, fraction_endpoint_center]
    · exact (obeseFiltered_correlationSq (by norm_num) (by norm_num)
        (by norm_num)).trans (steering_endpoint 1)
  · rintro x ⟨M,hM,hcen,hcorr⟩
    have h := all_states_steering_bound M hM
    rw [hcen, steeringEnvelopeSq_eq_one (by norm_num : (2:ℝ)/3 ≤ 1), hcorr] at h
    exact h

end Milne
