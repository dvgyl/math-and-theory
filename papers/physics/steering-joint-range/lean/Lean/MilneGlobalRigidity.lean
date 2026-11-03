import MilneCanonicalRigidity
import MilnePhysicalOrbitFilter

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4000
noncomputable section
namespace Milne

theorem rigidityConj_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A B : Matrix ι ι ℂ) :
    rigidityConj U (A*B) = rigidityConj U A*rigidityConj U B := by
  unfold rigidityConj
  calc
    _ = (U:Matrix ι ι ℂ)*A*((U:Matrix ι ι ℂ)ᴴ*(U:Matrix ι ι ℂ))*B*
        (U:Matrix ι ι ℂ)ᴴ := by rw [rigidity_unitary_adjoint_mul]; noncomm_ring
    _ = _ := by noncomm_ring

theorem localConjugate_onBob (U V : Matrix.unitaryGroup Q ℂ)
    (F : Matrix Q Q ℂ) :
    localConjugate U V (onBob F) = onBob (rigidityConj V F) := by
  rw [localConjugate_bob_alice]
  have h : onAlice (U:Matrix Q Q ℂ)*onBob F*onAlice (U:Matrix Q Q ℂ)ᴴ = onBob F := by
    calc
      _ = onBob F*(onAlice (U:Matrix Q Q ℂ)*onAlice (U:Matrix Q Q ℂ)ᴴ) := by
        rw [onAlice_onBob_commute]
        noncomm_ring
      _ = onBob F := by
        rw [← onAlice_mul,rigidity_unitary_mul_adjoint,onAlice_one,mul_one]
  rw [h,← onBob_mul,← onBob_mul]
  rfl

theorem localConjugate_bob_sandwich (U V : Matrix.unitaryGroup Q ℂ)
    (M : CMatrix) (F : Matrix Q Q ℂ) :
    localConjugate U V (onBob F*M*onBob F) =
      onBob (rigidityConj V F)*localConjugate U V M*onBob (rigidityConj V F) := by
  have hmul (A B : CMatrix) : localConjugate U V (A*B) =
      localConjugate U V A*localConjugate U V B :=
    rigidityConj_product _ A B
  rw [hmul,hmul,localConjugate_onBob]

def alignedObeseT (c : ℝ) : T3 :=
  alignedT (1-c) 0 ((Real.sqrt (1-c)/2:ℝ):ℂ) 0

theorem alignedObese_bloch (c : ℝ) :
    alignedObese c = blochState (c • geometryEz) 0 (alignedObeseT c) :=
  alignedState_bloch c (1-c) 0 _ 0

/-- The full three-dimensional filter objective for the maximizing
canonical state, before any choice of filter direction. -/
theorem alignedObese_orbit_polynomial {c : ℝ} (hc1 : c ≤ 1) (b : V3) :
    orbitQuadratic (tSq (alignedObeseT c))
      (ttVec (alignedObeseT c) (c • geometryEz))
      (orbitK (c • geometryEz) (alignedObeseT c)) b =
      steeringQuadratic c (b 2)-(2-3*c)*((b 0)^2+(b 1)^2) := by
  have hs := Real.sq_sqrt (show 0 ≤ 1-c by linarith)
  rw [orbit_physical_quadratic_identity]
  simp [alignedObeseT,alignedT,geometryEz,tSq,vSq,tVec,Pi.smul_apply,
    smul_eq_mul,Pi.add_apply,Fin.sum_univ_three,steeringQuadratic]
  ring_nf
  all_goals rw [hs]
  all_goals ring

/-- The exact optimal filter effect is unique throughout the curved branch,
including c=0. No polar decomposition or invertibility of the filter is
assumed: every complex normalized filter is covered. -/
theorem alignedObese_optimal_effect {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 2/3)
    (F : Matrix Q Q ℂ) (hTr : Matrix.trace (Fᴴ*F) = 2)
    (he : correlationSq (complexFiltered (alignedObese c) F) = steeringEnvelopeSq c) :
    Fᴴ*F = 1+spin (optimalFilterLength c • geometryEz) := by
  obtain ⟨b,hb,hF⟩ := complex_filter_effect_coordinates F hTr
  have hPSD : (blochState (c • geometryEz) 0 (alignedObeseT c)).PosSemidef := by
    rw [← alignedObese_bloch]
    exact (alignedObese_density hc0 (by linarith)).1
  rw [alignedObese_bloch,
    canonical_complex_filter_correlation _ b _ hPSD F hF,
    alignedObese_orbit_polynomial (by linarith)] at he
  have hsq := steering_completed_square hc0 (le_of_lt hc) (b 2)
  have hD : 0 < steeringDenominator c := steeringDenominator_pos hc0 (le_of_lt hc)
  have hA : 0 < 2-3*c := by linarith
  have hx : 0 ≤ (b 0)^2+(b 1)^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hy := sq_nonneg (b 2-optimalFilterLength c)
  have hp := mul_nonneg (le_of_lt hA) hx
  have hq := mul_nonneg (le_of_lt hD) hy
  have hz : (2-3*c)*((b 0)^2+(b 1)^2) = 0 := by linarith
  have hzz : steeringDenominator c*(b 2-optimalFilterLength c)^2 = 0 := by linarith
  have hxy : (b 0)^2+(b 1)^2 = 0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hA)
  have hb0 : b 0 = 0 := by nlinarith [sq_nonneg (b 1)]
  have hb1 : b 1 = 0 := by nlinarith [sq_nonneg (b 0)]
  have hb2 : b 2 = optimalFilterLength c := by
    have h := (mul_eq_zero.mp hzz).resolve_left (ne_of_gt hD)
    nlinarith
  have hbvec : b = optimalFilterLength c • geometryEz := by
    funext i
    fin_cases i <;> simp [geometryEz,Pi.smul_apply,smul_eq_mul,hb0,hb1,hb2]
  rwa [hbvec] at hF

def alignedEndpointFilter (r : ℝ) : Matrix Q Q ℂ := endpointFilter (-r)

theorem alignedEndpointFilter_psd (r : ℝ) : (alignedEndpointFilter r).PosSemidef :=
  endpointFilter_psd

theorem alignedEndpointFilter_square {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    alignedEndpointFilter r*alignedEndpointFilter r = 1+spin (r • geometryEz) := by
  have hplus := Real.sq_sqrt (show 0 ≤ 1+r by linarith)
  have hminus := Real.sq_sqrt (show 0 ≤ 1-r by linarith)
  have hplusC : (Real.sqrt (1+r):ℂ)^2 = (1+r:ℂ) := by exact_mod_cast hplus
  have hminusC : (Real.sqrt (1-r):ℂ)^2 = (1-r:ℂ) := by exact_mod_cast hminus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alignedEndpointFilter,endpointFilter,Matrix.mul_apply,Matrix.diagonal_apply,
      Matrix.one_apply,Fin.sum_univ_two,spin,geometryEz,Pi.smul_apply,smul_eq_mul,
      ← pow_two,hplusC,hminusC]
  simpa only [sub_eq_add_neg] using hminusC

def alignedOptimalState (c : ℝ) : CMatrix :=
  onBob (alignedEndpointFilter (optimalFilterLength c))*alignedObese c*
    onBob (alignedEndpointFilter (optimalFilterLength c))

theorem alignedObese_optimal_positive_filter {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 2/3)
    (F : Matrix Q Q ℂ) (hF : F.PosSemidef)
    (hTr : Matrix.trace (F*F) = 2)
    (he : correlationSq (onBob F*alignedObese c*onBob F) = steeringEnvelopeSq c) :
    F = alignedEndpointFilter (optimalFilterLength c) := by
  have he' : correlationSq (complexFiltered (alignedObese c) F) = steeringEnvelopeSq c := by
    simpa only [complexFiltered,hF.1.eq] using he
  have hTr' : Matrix.trace (Fᴴ*F) = 2 := by rwa [hF.1.eq]
  have heffect := alignedObese_optimal_effect hc0 hc F hTr' he'
  rw [hF.1.eq] at heffect
  have hr := steering_vertex_in_unit_interval hc0 (le_of_lt hc)
  apply hF.eq_of_sq_eq_sq (alignedEndpointFilter_psd _)
  rw [pow_two,pow_two,heffect]
  exact (alignedEndpointFilter_square hr.1 hr.2).symm

theorem alignedOptimalState_correlationSq {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 2/3) :
    correlationSq (alignedOptimalState c) = steeringEnvelopeSq c := by
  let r := optimalFilterLength c
  let F := alignedEndpointFilter r
  have hF : F.PosSemidef := alignedEndpointFilter_psd r
  have hr := steering_vertex_in_unit_interval hc0 (le_of_lt hc)
  have hE : Fᴴ*F = 1+spin (r • geometryEz) := by
    rw [hF.1.eq]
    exact alignedEndpointFilter_square hr.1 hr.2
  have hPSD : (blochState (c • geometryEz) 0 (alignedObeseT c)).PosSemidef := by
    rw [← alignedObese_bloch]
    exact (alignedObese_density hc0 (by linarith)).1
  change correlationSq (onBob F*alignedObese c*onBob F) = _
  have h := canonical_complex_filter_correlation (c • geometryEz) (r • geometryEz)
    (alignedObeseT c) hPSD F hE
  rw [← alignedObese_bloch,alignedObese_orbit_polynomial (by linarith)] at h
  simp only [complexFiltered,hF.1.eq] at h
  simp [geometryEz,Pi.smul_apply,smul_eq_mul] at h
  rw [h]
  exact steering_vertex_attains hc0 (le_of_lt hc)

/-- Complete classification of every global envelope maximizer on the
curved branch as one actual local-unitary orbit. The joint state may have
any rank; Bob invertibility is derived from strict violation. -/
theorem global_steering_equality_iff (M : CMatrix) (hM : Density M)
    (hc : steeringCenter M hM < 2/3) :
    correlationSq M = steeringEnvelopeSq (steeringCenter M hM) ↔
      ∃ U V : Matrix.unitaryGroup Q ℂ,
        localConjugate U V M = alignedOptimalState (steeringCenter M hM) := by
  have hc0 := steeringCenter_nonneg M hM
  constructor
  · intro he
    have hd : (partialB M).det ≠ 0 := by
      intro hd
      have hb := singular_Bob_correlationSq_le_one M hM hd
      have hg := steeringEnvelopeSq_gt_one hc0 hc
      rw [he] at hb
      linarith
    let N := canonicalize M hM
    let F := bobFilter M hM
    have hN : Density N := canonicalize_density M hM hd
    have hNB : partialB N = (1/2:ℂ) • (1 : Matrix Q Q ℂ) := canonicalize_partialB M hM hd
    have hNc : center N = steeringCenter M hM := (steeringCenter_of_nonsingular M hM hd).symm
    have hmax := ((arbitrary_envelope_equality_iff M hM hd (le_of_lt hc)).mp he).2.1
    have hmaxN : correlationSq N = (1-center N)*(3-center N) := by
      rw [hNc]
      dsimp only [N]
      nlinarith
    obtain ⟨U,V,hUV⟩ := (canonical_obese_equality_iff N hN hNB).mp hmaxN
    rw [hNc] at hUV
    let G := rigidityConj V F
    have hF : F.PosSemidef := ((partialB_psd hM.1).add (partialB_psd hM.1)).posSemidef_sqrt
    have hG : G.PosSemidef := hF.mul_mul_conjTranspose_same (V:Matrix Q Q ℂ)
    have hTr : Matrix.trace (G*G) = 2 := by
      change Matrix.trace (rigidityConj V F*rigidityConj V F) = 2
      rw [← rigidityConj_product,rigidityConj_trace]
      exact bobFilter_trace M hM
    have hrec : localConjugate U V M =
        onBob G*alignedObese (steeringCenter M hM)*onBob G := by
      have hr := canonicalize_reconstruction M hM hd
      calc
        localConjugate U V M = localConjugate U V (onBob F*N*onBob F) :=
          congrArg (fun X => localConjugate U V X) hr.symm
        _ = _ := by rw [localConjugate_bob_sandwich,hUV]
    have hval : correlationSq (onBob G*alignedObese (steeringCenter M hM)*onBob G) =
        steeringEnvelopeSq (steeringCenter M hM) := by
      rw [← hrec,localConjugate_correlationSq U V M hM,he]
    have hGeq := alignedObese_optimal_positive_filter hc0 hc G hG hTr hval
    refine ⟨U,V,?_⟩
    rw [hrec,hGeq]
    rfl
  · rintro ⟨U,V,hUV⟩
    have hi := localConjugate_correlationSq U V M hM
    rw [hUV,alignedOptimalState_correlationSq hc0 hc] at hi
    exact hi.symm

end Milne

#print axioms Milne.alignedObese_optimal_effect
#print axioms Milne.global_steering_equality_iff
