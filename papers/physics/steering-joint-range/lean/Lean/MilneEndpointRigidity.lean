import MilneCanonicalRigidity

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4000
noncomputable section
namespace Milne

def pureProduct00 : CMatrix := pure (Pi.single (0,0) 1)

/-- The two pure north-pole marginals fix the entire joint state. The
support theorem, not division by a marginal, treats this singular case. -/
theorem density_north_pole_marginals (M : CMatrix) (hM : Density M)
    (ha : partialA M = qubitState geometryEz)
    (hb : partialB M = qubitState geometryEz) : M = pureProduct00 := by
  have hd : (partialB M).det = 0 := by
    rw [hb]
    have hz0 : geometryEz 0 = 0 := rfl
    have hz1 : geometryEz 1 = 0 := rfl
    have hz2 : geometryEz 2 = 1 := rfl
    norm_num [qubitState,spin,hz0,hz1,hz2,Matrix.det_fin_two,Matrix.one_apply]
  have hs := singular_Bob_support M hM hd
  rw [hb] at hs
  have he (a i b j : Q) : M (a,i) (b,j) =
      if i = 0 ∧ j = 0 then M (a,0) (b,0) else 0 := by
    have h := congrArg (fun X : CMatrix => X (a,i) (b,j)) hs
    fin_cases a <;> fin_cases i <;> fin_cases b <;> fin_cases j <;>
      simpa [onBob,qubitState,spin,geometryEz,Matrix.mul_apply,
        Matrix.one_apply,Fintype.sum_prod_type,Fin.sum_univ_two] using h
  have h00 (a b : Q) : M (a,0) (b,0) = qubitState geometryEz a b := by
    have hz : M (a,1) (b,1) = 0 := by simpa using he a 1 b 1
    have h := congrFun (congrFun ha a) b
    simpa only [partialA,Fin.sum_univ_two,hz,add_zero] using h
  ext ⟨a,i⟩ ⟨b,j⟩
  rw [he,h00]
  fin_cases a <;> fin_cases i <;> fin_cases b <;> fin_cases j <;>
    simp [h00,pureProduct00,pure,qubitState,spin,geometryEz,Matrix.one_apply,
      Prod.ext_iff]
  norm_num

/-- Every two-qubit state whose two marginals are pure is a pure product
state up to actual local unitaries. All singular cases are included. -/
theorem two_pure_marginals_local_normal_form (M : CMatrix) (hM : Density M)
    (ha : blochSq (partialA M) = 1) (hb : blochSq (partialB M) = 1) :
    ∃ U V : Matrix.unitaryGroup Q ℂ, localConjugate U V M = pureProduct00 := by
  obtain ⟨U,hU⟩ := qubit_density_diagonalization (partialA M) (partialA_psd hM.1).1
    (by rw [trace_partialA,hM.2])
  obtain ⟨V,hV⟩ := qubit_density_diagonalization (partialB M) (partialB_psd hM.1).1
    (by rw [trace_partialB,hM.2])
  rw [ha,Real.sqrt_one,one_smul] at hU
  rw [hb,Real.sqrt_one,one_smul] at hV
  refine ⟨U,V,density_north_pole_marginals _ (localConjugate_density U V M hM) ?_ ?_⟩
  · rw [localConjugate_partialA,hU]
  · rw [localConjugate_partialB,hV]

theorem pureProduct00_correlationSq : correlationSq pureProduct00 = 1 := by
  have hp : pureProduct00 = pointProduct 1 := by
    norm_num [pureProduct00,pointProduct]
  rw [hp,singular_Bob_correlationSq_eq_blochSq (pointProduct 1)
    (pointProduct_density (by norm_num) (by norm_num)) (pointProduct_bob_det 1),
    pointProduct_blochSq]
  norm_num

/-- The only global envelope maximizers at the final centre c=1 are pure
product states. This completes the endpoint excluded by the stability
constant's factor 1/(1-c). -/
theorem global_endpoint_equality_iff (M : CMatrix) (hM : Density M)
    (hc : steeringCenter M hM = 1) :
    correlationSq M = 1 ↔
      ∃ U V : Matrix.unitaryGroup Q ℂ, localConjugate U V M = pureProduct00 := by
  constructor
  · intro he
    have hd : (partialB M).det = 0 := by
      by_contra hd
      have hq := arbitrary_joint_steering_bound M hM hd
      rw [hc] at hq
      have hs := steeringQuadratic_lt_one (c:=1) (by norm_num) (by norm_num)
        (blochLength_nonneg (partialB M)) (fullrank_Bob_blochLength_lt_one M hM hd)
      rw [he] at hq
      exact (not_lt_of_ge hq) hs
    have hb := singular_Bob_blochSq M hM hd
    have ha : blochSq (partialA M) = 1 := by
      rw [← singular_Bob_correlationSq_eq_blochSq M hM hd,he]
    exact two_pure_marginals_local_normal_form M hM ha hb
  · rintro ⟨U,V,h⟩
    have hi := localConjugate_correlationSq U V M hM
    rw [h,pureProduct00_correlationSq] at hi
    exact hi.symm

end Milne

#print axioms Milne.density_north_pole_marginals
#print axioms Milne.global_endpoint_equality_iff
