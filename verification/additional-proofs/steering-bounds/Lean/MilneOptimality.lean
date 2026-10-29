import MilneAllStates
import MilneSharpness

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

/-- All physically realizable squared F3 values at a specified steering
center. Positivity, trace normalization, and the computed center are part
of membership, rather than external assumptions about a scalar model. -/
def steeringSpectrum (c : ℝ) : Set ℝ :=
  {x | ∃ (M : CMatrix) (hM : Density M),
    steeringCenter M hM = c ∧ correlationSq M = x}

theorem all_states_envelope_attained {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 2/3) :
    steeringEnvelopeSq c ∈ steeringSpectrum c := by
  obtain ⟨M,hM,hd,hcM,hs⟩ := steeringEnvelope_attained hc0 hc
  exact ⟨M,hM,(steeringCenter_of_nonsingular M hM hd).trans hcM,hs⟩

theorem all_states_envelope_approached {c ε : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hε : 0 < ε) :
    ∃ x ∈ steeringSpectrum c, steeringEnvelopeSq c-ε < x := by
  by_cases hc : c < 2/3
  · exact ⟨steeringEnvelopeSq c, all_states_envelope_attained hc0 hc, by linarith⟩
  · obtain ⟨M,hM,hd,hcM,hs⟩ := steeringEnvelope_supremum (le_of_not_gt hc) hc1 hε
    exact ⟨correlationSq M,
      ⟨M,hM,(steeringCenter_of_nonsingular M hM hd).trans hcM,rfl⟩,hs⟩

/-- Complete solution of the extremal problem: G(c) is exactly the least
upper bound over all physical two-qubit states with steering center c. -/
theorem steeringEnvelope_isLUB {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsLUB (steeringSpectrum c) (steeringEnvelopeSq c) := by
  constructor
  · intro x hx
    obtain ⟨M,hM,hcM,hs⟩ := hx
    have h := all_states_steering_bound M hM
    rwa [hcM,hs] at h
  · intro b hb
    by_contra hn
    have hε : 0 < steeringEnvelopeSq c-b := sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨x,hx,hgt⟩ := all_states_envelope_approached hc0 hc1 hε
    have hxb := hb hx
    linarith

/-- There exists a state violating F3 at a given center exactly when the
center is strictly below two thirds. -/
theorem three_setting_violation_possible_iff {c : ℝ} (hc0 : 0 ≤ c) (_hc1 : c ≤ 1) :
    (∃ (M : CMatrix) (hM : Density M), steeringCenter M hM = c ∧
      1 < steeringValue M) ↔ c < 2/3 := by
  constructor
  · rintro ⟨M,hM,hcM,hv⟩
    have h := violation_requires_center_lt_two_thirds M hM hv
    rwa [hcM] at h
  · intro hc
    obtain ⟨M,hM,hcM,hs⟩ := all_states_envelope_attained hc0 hc
    refine ⟨M,hM,hcM,?_⟩
    have hgt : 1 < correlationSq M := by rw [hs]; exact steeringEnvelopeSq_gt_one hc0 hc
    have hsq := Real.sq_sqrt (correlationSq_nonneg M)
    have hn := Real.sqrt_nonneg (correlationSq M)
    change 1 < Real.sqrt (correlationSq M)
    nlinarith

end Milne
