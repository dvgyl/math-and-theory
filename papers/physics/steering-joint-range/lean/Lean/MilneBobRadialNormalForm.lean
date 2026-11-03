import MilneCanonicalNormalForm
import MilneAlignedEquality

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4000
noncomputable section
namespace Milne

/-- The ordered eigenvalue gap of the Alice block difference is exactly the
radial support of the steering ellipsoid, including a zero gap. -/
theorem alignedBlockDifference_blochSq (c : ℝ) (T : T3) :
    blochSq (alignedBlockDifference (blochState (c • geometryEz) 0 T)) =
      vSq (ttVec T geometryEz) := by
  simp [blochSq,alignedBlockDifference,bobBlock,blochState,spin,
    onAlice,onBob,pauli,pauliZ,geometryEz,Pi.smul_apply,smul_eq_mul,
    Matrix.sub_apply,Matrix.mul_apply,Matrix.trace,Matrix.diag,
    Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_three,
    Complex.mul_re,Complex.mul_im,Complex.normSq_apply,vSq,ttVec,Prod.ext_iff]
  ring

/-- Bob alone can align the radial row to the positive z axis while leaving
the prescribed Alice centre and every local-unitary invariant unchanged.
The input is an actual positive Bloch density, with arbitrary joint rank. -/
theorem bloch_bob_radial_normal_form (c t : ℝ) (T : T3)
    (ht0 : 0 ≤ t)
    (hM : (blochState (c • geometryEz) 0 T).PosSemidef)
    (hq : vSq (ttVec T geometryEz) = t^2) :
    ∃ V : Matrix.unitaryGroup Q ℂ, ∃ z w v : ℂ,
      localConjugate 1 V (blochState (c • geometryEz) 0 T) =
        alignedState c t z w v := by
  let M := blochState (c • geometryEz) 0 T
  have hMD : Density M := blochState_density _ _ _ hM
  have hMA : partialA M = qubitState (c • geometryEz) := blochState_partialA _ _ _
  have hMB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ) := blochState_canonical _ _
  let H := alignedBlockDifference M
  have hH : H.IsHermitian := alignedBlockDifference_hermitian M hMD.1.1
  have htr : Matrix.trace H = (c:ℂ) := alignedBlockDifference_trace M c hMA
  have hsq : blochSq H = t^2 := (alignedBlockDifference_blochSq c T).trans hq
  obtain ⟨V,hV⟩ := qubit_ordered_diagonalization H hH
  rw [htr,hsq,Real.sqrt_sq ht0] at hV
  let N := localConjugate 1 V M
  have hND : Density N := localConjugate_density 1 V M hMD
  have hNA : partialA N = qubitState (c • geometryEz) := by
    rw [localConjugate_partialA]
    simpa [rigidityConj] using hMA
  have hNB : partialB N = (1/2:ℂ) • (1 : Matrix Q Q ℂ) :=
    localConjugate_canonical 1 V M hMB
  have hNe : N = onBob (V:Matrix Q Q ℂ)*M*onBob (V:Matrix Q Q ℂ)ᴴ := by
    change localConjugate 1 V M = _
    rw [localConjugate_alice_bob]
    simp [onAlice_one]
  have hNH : alignedBlockDifference N = qubitDiagonal c t := by
    rw [hNe,alignedBlockDifference_bob_filter]
    simpa only [Complex.ofReal_re] using hV
  exact ⟨V,N (0,0) (1,0),N (0,0) (1,1),N (0,1) (1,0),
    matrix_eq_aligned_of_marginals N c t hND.1.1 hNA hNB hNH⟩

/-- The same radial normal form stated directly for arbitrary density
matrices and their measured Pauli coordinates, with no representation gap. -/
theorem physical_bob_radial_normal_form (M : CMatrix) (hM : Density M)
    (c t : ℝ) (ht0 : 0 ≤ t)
    (ha : geometryLocalA M = c • geometryEz) (hb : geometryLocalB M = 0)
    (hq : vSq (ttVec (correlation M) geometryEz) = t^2) :
    ∃ V : Matrix.unitaryGroup Q ℂ, ∃ z w v : ℂ,
      localConjugate 1 V M = alignedState c t z w v := by
  have hr := geometry_density_reconstruction M hM
  rw [ha,hb] at hr
  have hp : (blochState (c • geometryEz) 0 (correlation M)).PosSemidef := by
    rw [hr]
    exact hM.1
  obtain ⟨V,z,w,v,h⟩ := bloch_bob_radial_normal_form c t (correlation M) ht0 hp hq
  rw [hr] at h
  exact ⟨V,z,w,v,h⟩

/-- Complete fixed-centre, fixed-radial-support equality classification for
arbitrary density matrices, with every matrix and basis change explicit. -/
theorem physical_radial_equality_iff (M : CMatrix) (hM : Density M)
    (c t : ℝ) (ht0 : 0 ≤ t)
    (ha : geometryLocalA M = c • geometryEz) (hb : geometryLocalB M = 0)
    (hq : vSq (ttVec (correlation M) geometryEz) = t^2) :
    correlationSq M = 1-c^2+2*t^2 ↔
      ∃ V : Matrix.unitaryGroup Q ℂ, ∃ z w v : ℂ,
        localConjugate 1 V M = alignedState c t z w v ∧
        (t:ℂ)*z = 0 ∧
        Complex.normSq z+Complex.normSq w = (1+c+t)*(1-c+t)/16 ∧
        Complex.normSq z+Complex.normSq v = (1+c-t)*(1-c-t)/16 ∧
        z*star v = w*star z := by
  constructor
  · intro he
    obtain ⟨V,z,w,v,h⟩ := physical_bob_radial_normal_form M hM c t ht0 ha hb hq
    have hp : (alignedState c t z w v).PosSemidef := by
      rw [← h]
      exact (localConjugate_density 1 V M hM).1
    refine ⟨V,z,w,v,h,(alignedState_saturation_iff c t z w v hp).mp ?_⟩
    rw [← h,localConjugate_correlationSq 1 V M hM,he]
  · rintro ⟨V,z,w,v,h,hs⟩
    have hp : (alignedState c t z w v).PosSemidef := by
      rw [← h]
      exact (localConjugate_density 1 V M hM).1
    have he := (alignedState_saturation_iff c t z w v hp).mpr hs
    rwa [← h,localConjugate_correlationSq 1 V M hM] at he

end Milne

#print axioms Milne.alignedBlockDifference_blochSq
#print axioms Milne.physical_bob_radial_normal_form
#print axioms Milne.physical_radial_equality_iff
