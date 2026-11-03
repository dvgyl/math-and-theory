import MilneVolumeUnitary
import MilneBobRadialNormalForm

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 16000
noncomputable section
namespace Milne

/-- Complete actual-state domain at a fixed marked radial axis.  The axis
is retained at c=0, so no direction is selected from a degenerate marginal. -/
def physicalTripleVolumeSpectrum (c t τ : ℝ) : Set ℝ :=
  {q | ∃ M : CMatrix, Density M ∧ geometryLocalA M = c • geometryEz ∧
    geometryLocalB M = 0 ∧ vSq (ttVec (correlation M) geometryEz) = t^2 ∧
    correlationSq M = τ ∧ |Matrix.det (correlation M)| = q}

def physicalRadialVolumeSpectrum (c t : ℝ) : Set ℝ :=
  {q | ∃ M : CMatrix, Density M ∧ geometryLocalA M = c • geometryEz ∧
    geometryLocalB M = 0 ∧ vSq (ttVec (correlation M) geometryEz) = t^2 ∧
    |Matrix.det (correlation M)| = q}

theorem geometryLocalB_zero_implies_canonical (M : CMatrix) (hM : Density M)
    (hb : geometryLocalB M = 0) :
    partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ) := by
  have hr := geometry_density_reconstruction M hM
  rw [hb] at hr
  have h := congrArg partialB hr
  rw [blochState_canonical] at h
  exact h.symm

/-- Arbitrary-density-matrix signed determinant bounds in the marked-axis
convention. Bob-only normalization preserves that axis even at c=0. -/
theorem physical_radial_signed_determinant_bounds (M : CMatrix) (hM : Density M)
    (c t : ℝ) (ht0 : 0 ≤ t)
    (ha : geometryLocalA M = c • geometryEz) (hb : geometryLocalB M = 0)
    (hq : vSq (ttVec (correlation M) geometryEz) = t^2) :
    -radialVolumeCap c t ≤ Matrix.det (correlation M) ∧
    Matrix.det (correlation M) ≤ t*((1-t)^2-c^2)/4 := by
  obtain ⟨V,z,w,v,hN⟩ := physical_bob_radial_normal_form M hM c t ht0 ha hb hq
  have hB := geometryLocalB_zero_implies_canonical M hM hb
  have hp : (alignedState c t z w v).PosSemidef := by
    rw [← hN]
    exact (localConjugate_density 1 V M hM).1
  have h := alignedState_signed_determinant_bounds ht0 hp
  rwa [← hN,localConjugate_correlation_det 1 V M hM hB] at h

/-- The strong three-parameter geometry theorem with all density matrices,
all complex coherences and every rank admitted in its domain. -/
theorem physical_triple_volume_bound (M : CMatrix) (hM : Density M)
    (c t : ℝ) (hc1 : c ≤ 1) (ht0 : 0 ≤ t)
    (ha : geometryLocalA M = c • geometryEz) (hb : geometryLocalB M = 0)
    (hq : vSq (ttVec (correlation M) geometryEz) = t^2) :
    |Matrix.det (correlation M)| ≤ tripleVolumeCap c t (correlationSq M) := by
  obtain ⟨V,z,w,v,hN⟩ := physical_bob_radial_normal_form M hM c t ht0 ha hb hq
  have hB := geometryLocalB_zero_implies_canonical M hM hb
  have hp : (alignedState c t z w v).PosSemidef := by
    rw [← hN]
    exact (localConjugate_density 1 V M hM).1
  have h := alignedState_triple_volume_bound hc1 ht0 hp
  rwa [← hN,localConjugate_correlation_det 1 V M hM hB,
    localConjugate_correlationSq 1 V M hM] at h

theorem physical_radial_volume_bound (M : CMatrix) (hM : Density M)
    (c t : ℝ) (ht0 : 0 ≤ t)
    (ha : geometryLocalA M = c • geometryEz) (hb : geometryLocalB M = 0)
    (hq : vSq (ttVec (correlation M) geometryEz) = t^2) :
    |Matrix.det (correlation M)| ≤ radialVolumeCap c t := by
  have h := physical_radial_signed_determinant_bounds M hM c t ht0 ha hb hq
  apply abs_le.mpr
  refine ⟨h.1,?_⟩
  have hm : t*((1-t)^2-c^2)/4 ≤ radialVolumeCap c t := by
    unfold radialVolumeCap
    nlinarith [sq_nonneg t]
  exact h.2.trans hm

/-- Exact, attained triple-volume envelope on the full physical domain. -/
theorem physicalTripleVolumeSpectrum_isGreatest {c t τ : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c)
    (hτ0 : t^2 ≤ τ) (hτ1 : τ ≤ 1-c^2+2*t^2) :
    IsGreatest (physicalTripleVolumeSpectrum c t τ) (tripleVolumeCap c t τ) := by
  constructor
  · obtain ⟨z,w,v,hM,hτ,hq⟩ :=
      alignedTripleVolumeSpectrum_attained hc0 hc1 ht0 ht1 hτ0 hτ1
    refine ⟨alignedState c t z w v,alignedState_density c t z w v hM,?_,?_,?_,hτ,hq⟩
    · rw [alignedState_bloch,geometryLocalA_blochState]
    · rw [alignedState_bloch,geometryLocalB_blochState]
    · rw [alignedState_bloch,blochState_correlations,alignedT_radial]
  · rintro q ⟨M,hM,ha,hb,ht,hτ,hq⟩
    have h := physical_triple_volume_bound M hM c t hc1 ht0 ha hb ht
    rwa [hτ,hq] at h

/-- Exact volume maximum for every feasible centre and radial support,
with an explicit physical witness and a domain including singular states. -/
theorem physicalRadialVolumeSpectrum_isGreatest {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) :
    IsGreatest (physicalRadialVolumeSpectrum c t) (radialVolumeCap c t) := by
  constructor
  · exact ⟨volumeWitness c t,volumeWitness_attains hc0 hc1 ht0 ht1⟩
  · rintro q ⟨M,hM,ha,hb,ht,hq⟩
    have h := physical_radial_volume_bound M hM c t ht0 ha hb ht
    rwa [hq] at h

end Milne

#print axioms Milne.physicalTripleVolumeSpectrum_isGreatest
#print axioms Milne.physicalRadialVolumeSpectrum_isGreatest
