import QuantumLocalUnitary
import CanonicalEffects

/-! Actual normalization and polar reduction of arbitrary invertible qubit
filters on canonical two-qubit states. -/
set_option autoImplicit false
set_option maxHeartbeats 3600000
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix
namespace UnilateralCHSH.Quantum

def filterSuccess (F : QubitMatrix) : ℝ := (Matrix.trace (Fᴴ*F)).re/2

def normalizedEffect (F : QubitMatrix) : QubitMatrix :=
  ((filterSuccess F)⁻¹ : ℂ) • (Fᴴ*F)

def normalizedKraus (F : QubitMatrix) : QubitMatrix :=
  ((Real.sqrt (filterSuccess F))⁻¹ : ℂ) • F

theorem filterSuccess_positive (F : QubitMatrix) (hF : F.det≠0) :
    0<filterSuccess F := by
  have h := qubit_posDef_trace_positive (Fᴴ*F) (qubit_gram_posDef F hF)
  unfold filterSuccess
  linarith

theorem gram_trace_eq_success (F : QubitMatrix) :
    Matrix.trace (Fᴴ*F) = ((2*filterSuccess F : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re,filterSuccess]
    ring
  · simp only [Complex.ofReal_im]
    exact qubit_hermitian_trace_real _ (Matrix.posSemidef_conjTranspose_mul_self F).1

theorem canonical_trace_onAlice (c : Vec) (D : Mat3) (E : QubitMatrix) :
    Matrix.trace (canonical c D * onAlice E) = Matrix.trace E/2 := by
  simp [canonical,blochState,onAlice,onBob,pauli,Matrix.trace,Matrix.diag,
    Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_three]
  ring

theorem canonical_general_filter_trace (c : Vec) (D : Mat3) (F : QubitMatrix) :
    Matrix.trace (filtered (canonical c D) F) = (filterSuccess F : ℂ) := by
  calc
    _ = Matrix.trace ((onAlice F)ᴴ*onAlice F*canonical c D) := by
      unfold filtered
      rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (canonical c D*((onAlice F)ᴴ*onAlice F)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (canonical c D*onAlice (Fᴴ*F)) := by
      rw [onAlice_mul,onAlice_conjTranspose]
    _ = Matrix.trace (Fᴴ*F)/2 := canonical_trace_onAlice c D _
    _ = _ := by
      rw [gram_trace_eq_success]
      push_cast
      ring

theorem normalizedEffect_posDef (F : QubitMatrix) (hF : F.det≠0) :
    (normalizedEffect F).PosDef := by
  simpa only [normalizedEffect,Complex.ofReal_inv] using
    qubit_posDef_smul_real _ (qubit_gram_posDef F hF) _
      (inv_pos.mpr (filterSuccess_positive F hF))

theorem normalizedEffect_trace (F : QubitMatrix) (hF : F.det≠0) :
    Matrix.trace (normalizedEffect F)=2 := by
  have hp : filterSuccess F≠0 := ne_of_gt (filterSuccess_positive F hF)
  unfold normalizedEffect
  rw [Matrix.trace_smul,gram_trace_eq_success]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  field_simp [hp]

theorem normalizedEffect_parametrization (F : QubitMatrix) (hF : F.det≠0) :
    ∃ u : Vec, normSq u<1 ∧ normalizedEffect F=spinEffect u :=
  trace_two_posDef_effect _ (normalizedEffect_posDef F hF) (normalizedEffect_trace F hF)

theorem success_sqrt_inverse_square (F : QubitMatrix) (hF : F.det≠0) :
    ((Real.sqrt (filterSuccess F))⁻¹ : ℂ) *
      ((Real.sqrt (filterSuccess F))⁻¹ : ℂ) = ((filterSuccess F)⁻¹ : ℂ) := by
  have hp := filterSuccess_positive F hF
  have hs := Real.sq_sqrt hp.le
  have hpne : filterSuccess F≠0 := ne_of_gt hp
  have hsne : Real.sqrt (filterSuccess F)≠0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have h : (Real.sqrt (filterSuccess F))⁻¹*(Real.sqrt (filterSuccess F))⁻¹ =
      (filterSuccess F)⁻¹ := by
    field_simp [hpne,hsne]
  exact_mod_cast h

theorem normalizedKraus_gram (F : QubitMatrix) (hF : F.det≠0) :
    (normalizedKraus F)ᴴ*normalizedKraus F = normalizedEffect F := by
  unfold normalizedKraus normalizedEffect
  rw [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  simp only [Complex.star_def,map_inv₀,Complex.conj_ofReal]
  rw [success_sqrt_inverse_square F hF]

theorem normalizedFiltered_canonical_eq (c : Vec) (D : Mat3) (F : QubitMatrix) :
    normalizedFiltered (canonical c D) F =
      ((filterSuccess F)⁻¹ : ℂ) • filtered (canonical c D) F := by
  unfold normalizedFiltered normalizeState
  rw [canonical_general_filter_trace]
  simp

theorem normalizedKraus_filtered (c : Vec) (D : Mat3) (F : QubitMatrix)
    (hF : F.det≠0) :
    filtered (canonical c D) (normalizedKraus F) =
      normalizedFiltered (canonical c D) F := by
  rw [normalizedKraus,filtered_smul_filter]
  simp only [Complex.star_def,map_inv₀,Complex.conj_ofReal]
  rw [success_sqrt_inverse_square F hF,normalizedFiltered_canonical_eq]

theorem canonical_filter_polar (c : Vec) (D : Mat3) (F : QubitMatrix)
    (hF : F.det≠0) :
    ∃ (u : Vec) (U : QubitMatrix), normSq u<1 ∧ IsQubitUnitary U ∧
      normalizedKraus F=U*positiveFilter u ∧
      normalizedFiltered (canonical c D) F =
        filtered (filtered (canonical c D) (positiveFilter u)) U := by
  obtain ⟨u,hu,he⟩ := normalizedEffect_parametrization F hF
  let S := positiveFilter u
  let R := normalizedKraus F
  let U := R*S⁻¹
  have hd : IsUnit S.det := isUnit_iff_ne_zero.mpr (positive_filter_invertible u hu)
  have hl : S⁻¹*S=1 := Matrix.nonsing_inv_mul S hd
  have hr : S*S⁻¹=1 := Matrix.mul_nonsing_inv S hd
  have hS : Sᴴ=S := (positive_filter_hermitian u).eq
  have hRi : Rᴴ*R=S*S := by
    rw [normalizedKraus_gram F hF,he,positive_filter_effect_square u hu.le]
  have hUleft : Uᴴ*U=1 := by
    dsimp only [U]
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_nonsing_inv,hS]
    calc
      _ = S⁻¹*(Rᴴ*R)*S⁻¹ := by noncomm_ring
      _ = (S⁻¹*S)*(S*S⁻¹) := by rw [hRi]; noncomm_ring
      _ = 1 := by rw [hl,hr]; simp
  have hU : IsQubitUnitary U := ⟨hUleft,Matrix.mul_eq_one_comm.mp hUleft⟩
  have hfactor : normalizedKraus F=U*positiveFilter u := by
    dsimp only [U]
    rw [Matrix.mul_assoc,hl,Matrix.mul_one]
  refine ⟨u,U,hu,hU,hfactor,?_⟩
  rw [← normalizedKraus_filtered c D F hF,hfactor,filtered_compose]

theorem normalizedFiltered_positiveFilter (c u : Vec) (D : Mat3)
    (hu : normSq u≤1) :
    normalizedFiltered (canonical c D) (positiveFilter u) =
      filtered (canonical c D) (positiveFilter u) := by
  unfold normalizedFiltered normalizeState
  rw [positive_filter_trace c u D hu]
  simp


theorem canonical_GL_density (c : Vec) (D : Mat3) (F : QubitMatrix)
    (hρ : (canonical c D).PosSemidef) (hF : F.det≠0) :
    (normalizedFiltered (canonical c D) F).PosSemidef ∧
      Matrix.trace (normalizedFiltered (canonical c D) F)=1 := by
  obtain ⟨u,U,hu,hU,_,hstate⟩ := canonical_filter_polar c D F hF
  rw [hstate]
  have hs := positive_filter_density c u D hρ hu.le
  exact ⟨filtered_psd hs.1 U,by rw [filtered_unitary_trace _ U hU,hs.2]⟩

end UnilateralCHSH.Quantum
