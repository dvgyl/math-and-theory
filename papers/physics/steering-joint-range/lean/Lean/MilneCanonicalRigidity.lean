import MilneCanonicalNormalForm
import MilneAlignedStability
import MilneTraceDistance

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 16000
noncomputable section
namespace Milne

/-- A phase that makes a complex coherence nonnegative, with an explicit
choice at zero. -/
def coherencePhase (w : ℂ) : ℂ :=
  if w = 0 then 1 else star w/(Real.sqrt (Complex.normSq w):ℂ)

theorem coherencePhase_normSq (w : ℂ) : Complex.normSq (coherencePhase w) = 1 := by
  by_cases hw : w = 0
  · simp [coherencePhase,hw]
  · have hs := Real.sq_sqrt (Complex.normSq_nonneg w)
    have hn : Complex.normSq w ≠ 0 := (Complex.normSq_pos.mpr hw).ne'
    simp only [coherencePhase,if_neg hw,Complex.normSq_div,Complex.star_def,
      Complex.normSq_conj,Complex.normSq_ofReal]
    rw [← pow_two,hs,div_self hn]

theorem coherencePhase_mul (w : ℂ) :
    coherencePhase w*w = (Real.sqrt (Complex.normSq w):ℂ) := by
  by_cases hw : w = 0
  · simp [coherencePhase,hw]
  · have hs := Real.sq_sqrt (Complex.normSq_nonneg w)
    have hs0 : Real.sqrt (Complex.normSq w) ≠ 0 :=
      (Real.sqrt_pos.mpr (Complex.normSq_pos.mpr hw)).ne'
    have hsC : (Real.sqrt (Complex.normSq w):ℂ) ≠ 0 := by exact_mod_cast hs0
    have hsqC : (Real.sqrt (Complex.normSq w):ℂ)^2 = (Complex.normSq w:ℂ) := by
      exact_mod_cast hs
    rw [coherencePhase,if_neg hw]
    calc
      star w/(Real.sqrt (Complex.normSq w):ℂ)*w =
        (star w*w)/(Real.sqrt (Complex.normSq w):ℂ) := by ring
      _ = (Complex.normSq w:ℂ)/(Real.sqrt (Complex.normSq w):ℂ) := by
        rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self]
      _ = (Real.sqrt (Complex.normSq w):ℂ) := by
        rw [← hsqC,pow_two]
        field_simp

def phaseUnitary (u : ℂ) (hu : Complex.normSq u = 1) : Matrix.unitaryGroup Q ℂ :=
  ⟨Matrix.diagonal ![u,1],Matrix.mem_unitaryGroup_iff.mpr (by
    change Matrix.diagonal ![u,1]*(Matrix.diagonal ![u,1])ᴴ = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.diagonal_apply,
        Matrix.one_apply,Fin.sum_univ_two,Complex.star_def,Complex.mul_conj,hu])⟩

theorem alignedState_phase_conjugate (u : ℂ) (hu : Complex.normSq u = 1)
    (c t : ℝ) (z w v : ℂ) :
    localConjugate (phaseUnitary u hu) 1 (alignedState c t z w v) =
      alignedState c t (u*z) (u*w) (u*v) := by
  have huC : u*star u = 1 := by
    simpa [Complex.star_def,hu] using Complex.mul_conj u
  have huc (x : ℂ) : u*x*star u = x := by
    calc
      u*x*star u = x*(u*star u) := by ring
      _ = x := by rw [huC]; simp
  rw [localConjugate_alice_bob]
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [phaseUnitary,alignedState,alignedA,alignedD,alignedC,onAlice,onBob,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.diagonal_apply,
      Matrix.one_apply,Fintype.sum_prod_type,Fin.sum_univ_two,huc,StarMul.star_mul]
  all_goals ring
  · simp only [Complex.star_def] at huC
    linear_combination ((1+c+t)/4:ℂ)*huC
  · simp only [Complex.star_def] at huC
    linear_combination ((1+c-t)/4:ℂ)*huC

/-- The radial normal form can always be chosen with a real nonnegative
00--11 coherence. This is an actual local unitary, including zero coherence. -/
theorem canonical_positive_aligned_normal_form (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) :
    ∃ U V : Matrix.unitaryGroup Q ℂ, ∃ t w : ℝ, ∃ z v : ℂ,
      0 ≤ t ∧ t ≤ 1-center M ∧ 0 ≤ w ∧
      localConjugate U V M = alignedState (center M) t z (w:ℂ) v := by
  obtain ⟨U,V,t,z,w,v,ht0,ht1,he⟩ := canonical_aligned_normal_form M hM hB
  let P := phaseUnitary (coherencePhase w) (coherencePhase_normSq w)
  have hphase : localConjugate P 1 (localConjugate U V M) =
      alignedState (center M) t (coherencePhase w*z)
        (Real.sqrt (Complex.normSq w):ℂ) (coherencePhase w*v) := by
    rw [he,alignedState_phase_conjugate,coherencePhase_mul]
  rw [localConjugate_comp] at hphase
  simp only [one_mul,mul_one] at hphase
  exact ⟨P*U,V,t,Real.sqrt (Complex.normSq w),coherencePhase w*z,coherencePhase w*v,
    ht0,ht1,Real.sqrt_nonneg _,hphase⟩

/-- Full local-unitary Hilbert--Schmidt rigidity for every actual canonical
two-qubit state. No aligned-basis hypothesis is left to the user. -/
theorem canonical_hs_rigidity (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (hc1 : center M < 1) :
    ∃ U V : Matrix.unitaryGroup Q ℂ,
      4*matrixHsSq (localConjugate U V M-alignedObese (center M)) ≤
        rigidityDeficit (center M) M*(5+center M)/(2*(1-center M)) := by
  obtain ⟨U,V,t,w,z,v,ht0,ht1,hw0,he⟩ := canonical_positive_aligned_normal_form M hM hB
  have hp : (alignedState (center M) t z (w:ℂ) v).PosSemidef := by
    rw [← he]
    exact (localConjugate_density U V M hM).1
  have h := aligned_hs_stability (center_nonneg M) hc1 ht0 hw0 hp
  have hδ : rigidityDeficit (center M) (alignedState (center M) t z (w:ℂ) v) =
      rigidityDeficit (center M) M := by
    rw [← he,rigidityDeficit,rigidityDeficit,localConjugate_correlationSq U V M hM]
  refine ⟨U,V,?_⟩
  rw [he]
  have hfull := h.1.trans h.2
  rwa [hδ] at hfull

/-- Genuine spectral trace-norm rigidity after actual local unitaries, for
all global state ranks. The bound is derived from matrix positivity. -/
theorem canonical_trace_rigidity (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (hc1 : center M < 1) :
    ∃ U V : Matrix.unitaryGroup Q ℂ,
      (hermitianTraceNorm ((localConjugate_density U V M hM).1.1.sub
        (alignedObese_hermitian (center M))))^2 ≤
        rigidityDeficit (center M) M*(5+center M)/(2*(1-center M)) := by
  obtain ⟨U,V,h⟩ := canonical_hs_rigidity M hM hB hc1
  exact ⟨U,V,(hermitianTraceNorm_sq_le_four_hs
    ((localConjugate_density U V M hM).1.1.sub
      (alignedObese_hermitian (center M)))).trans h⟩

/-- The quantitative estimate with the universal trace-norm diameter of the
state space. The usual trace distance is half this spectral trace norm. -/
theorem canonical_trace_rigidity_capped (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (hc1 : center M < 1) :
    ∃ U V : Matrix.unitaryGroup Q ℂ,
      (hermitianTraceNorm ((localConjugate_density U V M hM).1.1.sub
        (alignedObese_hermitian (center M))))^2 ≤
        min 4 (rigidityDeficit (center M) M*(5+center M)/(2*(1-center M))) := by
  obtain ⟨U,V,h⟩ := canonical_trace_rigidity M hM hB hc1
  refine ⟨U,V,le_min ?_ h⟩
  exact density_trace_distance_sq_le_four (localConjugate U V M)
    (alignedObese (center M)) (localConjugate_density U V M hM)
    (alignedObese_density (center_nonneg M) (center_le_one M hM))

theorem canonical_obese_equality_of_center_lt_one (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (hc1 : center M < 1)
    (he : correlationSq M = (1-center M)*(3-center M)) :
    ∃ U V : Matrix.unitaryGroup Q ℂ, localConjugate U V M = alignedObese (center M) := by
  obtain ⟨U,V,h⟩ := canonical_hs_rigidity M hM hB hc1
  have hδ : rigidityDeficit (center M) M = 0 := by rw [rigidityDeficit,he]; ring
  rw [hδ] at h
  simp only [zero_mul,zero_div] at h
  have hz : matrixHsSq (localConjugate U V M-alignedObese (center M)) = 0 := by
    have hn := matrixHsSq_nonneg (localConjugate U V M-alignedObese (center M))
    linarith
  exact ⟨U,V,sub_eq_zero.mp ((matrixHsSq_eq_zero_iff _).mp hz)⟩

theorem canonical_center_one_normal_form (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) (hc : center M = 1) :
    ∃ U V : Matrix.unitaryGroup Q ℂ, localConjugate U V M = alignedObese 1 := by
  obtain ⟨U,V,t,z,w,v,ht0,ht1,he⟩ := canonical_aligned_normal_form M hM hB
  have ht : t = 0 := by rw [hc] at ht1; linarith
  rw [hc,ht] at he
  have hp : (alignedState 1 0 z w v).PosSemidef := by
    rw [← he]
    exact (localConjugate_density U V M hM).1
  have hz := alignedState_minor_z 1 0 z w v hp
  have hw := alignedState_minor_w 1 0 z w v hp
  have hv := alignedState_minor_v 1 0 z w v hp
  norm_num at hz hw hv
  have hz0 : z = 0 := Complex.normSq_eq_zero.mp (le_antisymm hz (Complex.normSq_nonneg z))
  have hw0 : w = 0 := Complex.normSq_eq_zero.mp (le_antisymm hw (Complex.normSq_nonneg w))
  have hv0 : v = 0 := Complex.normSq_eq_zero.mp (le_antisymm hv (Complex.normSq_nonneg v))
  refine ⟨U,V,?_⟩
  rw [he,hz0,hw0,hv0]
  simp [alignedObese]

/-- Complete local-unitary classification of all canonical correlation
maximizers, including c=0 and the pure-Alice endpoint c=1. -/
theorem canonical_obese_equality_iff (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) :
    correlationSq M = (1-center M)*(3-center M) ↔
      ∃ U V : Matrix.unitaryGroup Q ℂ,
        localConjugate U V M = alignedObese (center M) := by
  constructor
  · intro he
    by_cases hc1 : center M < 1
    · exact canonical_obese_equality_of_center_lt_one M hM hB hc1 he
    · have hc : center M = 1 := le_antisymm (center_le_one M hM) (le_of_not_gt hc1)
      simpa only [hc] using canonical_center_one_normal_form M hM hB hc
  · rintro ⟨U,V,h⟩
    have hi := localConjugate_correlationSq U V M hM
    rw [h,alignedObese_correlationSq (center_le_one M hM)] at hi
    exact hi.symm

end Milne

#print axioms Milne.canonical_positive_aligned_normal_form
#print axioms Milne.canonical_hs_rigidity
#print axioms Milne.canonical_trace_rigidity
#print axioms Milne.canonical_trace_rigidity_capped
#print axioms Milne.canonical_obese_equality_iff
