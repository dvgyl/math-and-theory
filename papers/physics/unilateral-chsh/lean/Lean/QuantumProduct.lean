import QuantumSupport
import QuantumLocalUnitary
import CanonicalEffects

/-! Actual tensor products, qubit density matrices, and their filtering. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace UnilateralCHSH.Quantum

def qubitDensity (a : Vec) : QubitMatrix := (1/2:ℂ) • spinEffect a

def tensorState (A B : QubitMatrix) : State := onAlice A * onBob B

theorem tensorState_apply (A B : QubitMatrix) (p q : QQ) :
    tensorState A B p q=A p.1 q.1*B p.2 q.2 := onAlice_mul_onBob_apply _ _ _ _

theorem tensorState_trace (A B : QubitMatrix) :
    Matrix.trace (tensorState A B)=Matrix.trace A*Matrix.trace B := by
  simp only [Matrix.trace,Matrix.diag,tensorState_apply,Fintype.sum_prod_type,
    Fin.sum_univ_two]
  ring

theorem tensorState_smul_left (A B : QubitMatrix) (z : ℂ) :
    tensorState (z • A) B=z • tensorState A B := by
  ext p q
  simp [tensorState_apply]
  ring

theorem tensorState_filtered (A B F : QubitMatrix) :
    filtered (tensorState A B) F=tensorState (F*A*Fᴴ) B := by
  unfold filtered tensorState
  rw [onAlice_mul,onAlice_mul,onAlice_conjTranspose]
  have hc := onAlice_onBob_commute Fᴴ B
  rw [onAlice_conjTranspose] at hc
  calc
    _=onAlice F*onAlice A*(onBob B*(onAlice F)ᴴ) := by noncomm_ring
    _=_ := by rw [←hc]; noncomm_ring

theorem qubitDensity_trace (a : Vec) : Matrix.trace (qubitDensity a)=1 := by
  rw [qubitDensity,Matrix.trace_smul,spinEffect,Matrix.trace_add,realSpin_trace]
  norm_num [Matrix.trace,Matrix.diag,Fin.sum_univ_two]

theorem qubitDensity_posSemidef (a : Vec) (ha : normSq a≤1) :
    (qubitDensity a).PosSemidef := by
  simpa [qubitDensity] using
    qubit_posSemidef_smul_real _ (spinEffect_posSemidef a ha) (1/2) (by norm_num)

theorem qubitDensity_det (a : Vec) :
    (qubitDensity a).det=((1-normSq a)/4:ℝ) := by
  rw [qubitDensity,Matrix.det_smul,spinEffect_det]
  norm_num
  ring

theorem product_blochState (a b : Vec) :
    blochState a b (fun i j => a i*b j)=tensorState (qubitDensity a) (qubitDensity b) := by
  ext p q
  rw [tensorState_apply]
  rcases p with ⟨p₀,p₁⟩
  rcases q with ⟨q₀,q₁⟩
  fin_cases p₀ <;> fin_cases p₁ <;> fin_cases q₀ <;> fin_cases q₁ <;> apply Complex.ext <;>
    simp [blochState,qubitDensity,spinEffect,realSpin,complexSpin,onAlice,onBob,pauli,
      Matrix.one_apply,Prod.ext_iff,Fin.sum_univ_three,Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem inverse_sandwich (A F : QubitMatrix) (hF : F.det≠0) :
    F⁻¹*(F*A*Fᴴ)*(F⁻¹)ᴴ=A := by
  have hi := Matrix.nonsing_inv_mul F (isUnit_iff_ne_zero.mpr hF)
  calc
    _=(F⁻¹*F)*A*(Fᴴ*(F⁻¹)ᴴ) := by noncomm_ring
    _=A := by rw [←Matrix.conjTranspose_mul,hi]; simp

theorem qubit_filter_trace_positive (A F : QubitMatrix) (hA : A.PosSemidef)
    (ht : Matrix.trace A=1) (hF : F.det≠0) :
    0<(Matrix.trace (F*A*Fᴴ)).re := by
  have hp := hA.mul_mul_conjTranspose_same F
  have hn := psd_trace_nonneg hp
  apply lt_of_le_of_ne hn
  intro hz
  have hzero := psd_eq_zero_of_trace_re_zero hp hz.symm
  have ha0 : A=0 := by
    rw [←inverse_sandwich A F hF,hzero]
    simp
  rw [ha0] at ht
  simp at ht

theorem normalize_tensor_filtered (a b : Vec) (F : QubitMatrix) :
    normalizedFiltered (tensorState (qubitDensity a) (qubitDensity b)) F =
      tensorState
        ((((Matrix.trace (F*qubitDensity a*Fᴴ)).re)⁻¹:ℂ) • (F*qubitDensity a*Fᴴ))
        (qubitDensity b) := by
  unfold normalizedFiltered normalizeState
  rw [tensorState_filtered,tensorState_trace,qubitDensity_trace,mul_one,
    tensorState_smul_left]

/-- Invertible filtering preserves purity of a trace-one qubit density
matrix. The proof uses the actual determinant and constructs its Bloch vector. -/
theorem filtered_pure_qubit (a : Vec) (ha : normSq a=1)
    (F : QubitMatrix) (hF : F.det≠0) :
    ∃ a' : Vec, normSq a'=1 ∧
      ((((Matrix.trace (F*qubitDensity a*Fᴴ)).re)⁻¹:ℂ) • (F*qubitDensity a*Fᴴ))=
        qubitDensity a' := by
  let X := F*qubitDensity a*Fᴴ
  let p := (Matrix.trace X).re
  have hX : X.PosSemidef := (qubitDensity_posSemidef a ha.le).mul_mul_conjTranspose_same F
  have hp : 0<p := qubit_filter_trace_positive _ F (qubitDensity_posSemidef a ha.le)
    (qubitDensity_trace a) hF
  have hpn : p≠0 := ne_of_gt hp
  have htX : Matrix.trace X=(p:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using qubit_hermitian_trace_real X hX.1
  let E : QubitMatrix := ((2/p:ℝ):ℂ) • X
  have hE : E.PosSemidef := qubit_posSemidef_smul_real X hX (2/p) (by positivity)
  have htE : Matrix.trace E=2 := by
    dsimp only [E]
    rw [Matrix.trace_smul,htX]
    push_cast
    field_simp
  obtain ⟨a',he⟩ := trace_two_hermitian_effect E hE.1 htE
  have hdX : X.det=0 := by
    dsimp only [X]
    rw [Matrix.det_mul,Matrix.det_mul,qubitDensity_det,ha]
    simp
  have hdE : E.det=0 := by
    dsimp only [E]
    rw [Matrix.det_smul,hdX,mul_zero]
  have ha' : normSq a'=1 := by
    rw [he,spinEffect_det] at hdE
    have hr := congrArg Complex.re hdE
    simp only [Complex.ofReal_re,Complex.zero_re] at hr
    linarith
  refine ⟨a',ha',?_⟩
  change (p⁻¹:ℂ) • X=qubitDensity a'
  rw [qubitDensity,←he]
  dsimp only [E]
  rw [smul_smul]
  congr 1
  push_cast
  field_simp

theorem filtered_pure_product (a b : Vec) (ha : normSq a=1)
    (F : QubitMatrix) (hF : F.det≠0) :
    ∃ a' : Vec, normSq a'=1 ∧
      normalizedFiltered (blochState a b (fun i j => a i*b j)) F=
        blochState a' b (fun i j => a' i*b j) := by
  obtain ⟨a',ha',he⟩ := filtered_pure_qubit a ha F hF
  refine ⟨a',ha',?_⟩
  rw [product_blochState,product_blochState,normalize_tensor_filtered,he]

end UnilateralCHSH.Quantum
