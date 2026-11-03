import QuantumFano
import QuantumProduct
import CanonicalGLValues

/-! The pure-marginal boundary: product support and exact CHSH values. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16000
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace UnilateralCHSH.Quantum

theorem pure_support_trace (a b : Vec) (T : Mat3) :
    (Matrix.trace (blochState a b T*onAlice (spinEffect (-a)))).re=1-normSq a := by
  simp [blochState,onAlice,onBob,spinEffect,realSpin,complexSpin,pauli,
    Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.one_apply,Fintype.sum_prod_type,
    Fin.sum_univ_two,Fin.sum_univ_three,Complex.mul_re,Complex.mul_im,normSq,dot]
  ring

theorem pure_support_correlation (a b : Vec) (T : Mat3) (i j : Fin 3) :
    (Matrix.trace ((blochState a b T*onAlice (spinEffect (-a)))*pauliPair i j)).re=
      T i j-a i*b j := by
  fin_cases i <;> fin_cases j <;>
    simp [blochState,onAlice,onBob,spinEffect,realSpin,complexSpin,pauliPair,pauli,
      Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.one_apply,Fintype.sum_prod_type,
      Fin.sum_univ_two,Fin.sum_univ_three,Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem blochState_pure_marginal_correlation (a b : Vec) (T : Mat3)
    (hρ : (blochState a b T).PosSemidef) (ha : normSq a=1) :
    T=fun i j => a i*b j := by
  have hn : normSq (-a)≤1 := by simpa [normSq,dot] using ha.le
  have hH : (onAlice (spinEffect (-a))).PosSemidef := by
    rw [←positive_filter_effect_gram (-a) hn,onAlice_mul,onAlice_conjTranspose]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hz := psd_mul_zero_of_trace_product_zero hρ hH
    (by rw [pure_support_trace,ha]; norm_num)
  ext i j
  have he := pure_support_correlation a b T i j
  rw [hz,Matrix.zero_mul,Matrix.trace_zero] at he
  simp only [Complex.zero_re] at he
  linarith

/-- An actual positive trace-one state with pure Alice marginal is a product
state. No product decomposition or correlation factorization is assumed. -/
theorem pure_marginal_factorization (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)=1) :
    ρ=blochState (aliceBloch ρ) (bobBloch ρ)
      (fun i j => aliceBloch ρ i*bobBloch ρ j) := by
  have hf := fano_complete ρ hρ.1 ht
  have hp : (blochState (aliceBloch ρ) (bobBloch ρ) (correlation ρ)).PosSemidef := by
    rw [←hf]
    exact hρ
  have hT := blochState_pure_marginal_correlation _ _ _ hp ha
  rw [hT] at hf
  exact hf

theorem product_plane_value (a b n : Vec) :
    Horodecki.planeValue (fun i j => a i*b j) n=
      (normSq a-(dot n a)^2)*normSq b := by
  simp only [Horodecki.planeValue,planeColumnValue,column,normSq,dot]
  ring

theorem pure_product_chsh_upper (a b : Vec) (ha : normSq a=1)
    (a₀ a₁ b₀ b₁ : Vec) (hm : Horodecki.IsMeasurements a₀ a₁ b₀ b₁) :
    (bellExpectation (blochState a b (fun i j => a i*b j)) a₀ a₁ b₀ b₁)^2≤normSq b := by
  have hc : correlation (blochState a b (fun i j => a i*b j))=(fun i j => a i*b j) := by
    ext i j
    exact correlation_blochState _ _ _ i j
  rw [bell_expectation_correlation,hc]
  change (Horodecki.chshValue (fun i j => a i*b j) a₀ a₁ b₀ b₁)^2≤normSq b
  apply (Horodecki.exact_chsh_bound _ _).mp _ a₀ a₁ b₀ b₁ hm
  intro n _
  rw [product_plane_value,ha]
  have hp := mul_nonneg (sq_nonneg (dot n a)) (normSq_nonneg b)
  nlinarith

theorem pure_product_chsh_attained (a b : Vec) (ha : normSq a=1) :
    ∃ a₀ a₁ b₀ b₁ : Vec, Horodecki.IsMeasurements a₀ a₁ b₀ b₁ ∧
      (bellExpectation (blochState a b (fun i j => a i*b j)) a₀ a₁ b₀ b₁)^2=normSq b := by
  obtain ⟨n,hn,hna⟩ := Horodecki.exists_unit_perpendicular a
  have hn' : dot n a=0 := by rw [dot_symm]; exact hna
  obtain ⟨a₀,a₁,b₀,b₁,hm,hv⟩ := Horodecki.plane_attained (fun i j => a i*b j) n hn
  refine ⟨a₀,a₁,b₀,b₁,hm,?_⟩
  have hc : correlation (blochState a b (fun i j => a i*b j))=(fun i j => a i*b j) := by
    ext i j
    exact correlation_blochState _ _ _ i j
  rw [bell_expectation_correlation,hc]
  change (Horodecki.chshValue (fun i j => a i*b j) a₀ a₁ b₀ b₁)^2=normSq b
  rw [hv,product_plane_value,ha,hn']
  ring

theorem pure_product_spinCHSH_greatest (a b : Vec) (ha : normSq a=1) :
    IsGreatest (spinCHSHValues (blochState a b (fun i j => a i*b j))) (normSq b) := by
  refine ⟨pure_product_chsh_attained a b ha,?_⟩
  rintro z ⟨a₀,a₁,b₀,b₁,hm,hv⟩
  rw [←hv]
  exact pure_product_chsh_upper a b ha a₀ a₁ b₀ b₁ hm

theorem normalizedFiltered_identity (ρ : State) (ht : Matrix.trace ρ=1) :
    normalizedFiltered ρ (1 : QubitMatrix)=ρ := by
  unfold normalizedFiltered normalizeState
  rw [filtered_one,ht]
  simp

/-- The exact attained value for ALL invertible complex Alice filters at a
pure Alice marginal. It can be strictly below the classical threshold. -/
theorem pure_marginal_gl_isGreatest (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)=1) :
    IsGreatest (aliceGLValues ρ) (normSq (bobBloch ρ)) := by
  have hp := pure_marginal_factorization ρ hρ ht ha
  constructor
  · obtain ⟨a₀,a₁,b₀,b₁,hm,hv⟩ :=
      pure_product_chsh_attained (aliceBloch ρ) (bobBloch ρ) ha
    refine ⟨1,a₀,a₁,b₀,b₁,by simp,hm,?_⟩
    rw [normalizedFiltered_identity ρ ht]
    exact (congrArg (fun σ : State => (bellExpectation σ a₀ a₁ b₀ b₁)^2) hp).trans hv
  · rintro z ⟨F,a₀,a₁,b₀,b₁,hF,hm,hv⟩
    obtain ⟨a',ha',he⟩ := filtered_pure_product (aliceBloch ρ) (bobBloch ρ) ha F hF
    rw [hp,he] at hv
    rw [←hv]
    exact pure_product_chsh_upper a' (bobBloch ρ) ha' a₀ a₁ b₀ b₁ hm

theorem pure_marginal_gl_isLUB (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)=1) :
    IsLUB (aliceGLValues ρ) (normSq (bobBloch ρ)) := by
  have hg := pure_marginal_gl_isGreatest ρ hρ ht ha
  exact ⟨hg.2,fun _ hb => hb hg.1⟩

end UnilateralCHSH.Quantum
