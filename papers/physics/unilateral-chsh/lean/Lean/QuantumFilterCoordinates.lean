import QuantumWhitening

/-! Coordinate identities for arbitrary input states and explicit whitening. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix
namespace UnilateralCHSH.Quantum

theorem realSpin_pauli_decomposition (u : Vec) :
    realSpin u=∑ i : Fin 3, (u i:ℂ) • pauli i := by
  ext p q
  fin_cases p <;> fin_cases q <;> apply Complex.ext <;>
    simp [realSpin,complexSpin,pauli,Fin.sum_univ_three,Complex.mul_re,Complex.mul_im]

theorem pauliPair_as_product (i j : Fin 3) :
    pauliPair i j=onAlice (pauli i)*onBob (pauli j) := by
  ext p q
  exact (onAlice_mul_onBob_apply _ _ _ _).symm

theorem mixedSpin_expectation (ρ : State) (u : Vec) (j : Fin 3) :
    (Matrix.trace (ρ*(onAlice (realSpin u)*onBob (pauli j)))).re=
      dot u (column (correlation ρ) j) := by
  rw [realSpin_pauli_decomposition]
  simp only [Fin.sum_univ_three,onAlice_add,onAlice_smul,Matrix.add_mul,
    Matrix.smul_mul,Matrix.mul_add,Matrix.mul_smul,Matrix.trace_add,
    Matrix.trace_smul,smul_eq_mul,Complex.add_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,←pauliPair_as_product]
  rfl

theorem affineFilter_pauli_sandwich (u : Vec) (f g : ℝ) (i : Fin 3) :
    affineFilter u f g*pauli i*affineFilter u f g=
      ((f^2-g^2*normSq u:ℝ):ℂ) • pauli i +
      ((2*g^2*u i:ℝ):ℂ) • realSpin u +
      ((2*f*g*u i:ℝ):ℂ) • (1 : QubitMatrix) := by
  ext p q
  fin_cases i <;> fin_cases p <;> fin_cases q <;> apply Complex.ext <;>
    simp [affineFilter,realSpin,complexSpin,pauli,normSq,dot,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,Complex.mul_re,Complex.mul_im,pow_two]
  all_goals ring

theorem bobBloch_affine_filtered (ρ : State) (u : Vec) (f g : ℝ) (j : Fin 3) :
    bobBloch (filtered ρ (affineFilter u f g)) j=
      (f^2+g^2*normSq u)*bobBloch ρ j+
        2*f*g*dot u (column (correlation ρ) j) := by
  let F := affineFilter u f g
  have hp : (onAlice F)ᴴ*onBob (pauli j)*onAlice F=
      onAlice (Fᴴ*F)*onBob (pauli j) := by
    simpa only [onAlice_one,Matrix.one_mul,Matrix.mul_one] using
      tensor_pullback F 1 (pauli j)
  unfold bobBloch filtered
  rw [trace_sandwich_move,hp]
  dsimp only [F]
  rw [(affineFilter_hermitian u f g).eq,affineFilter_square]
  simp only [onAlice_add,onAlice_smul,onAlice_one,Matrix.add_mul,Matrix.smul_mul,
    Matrix.one_mul,Matrix.mul_add,Matrix.mul_smul,Matrix.trace_add,Matrix.trace_smul,
    smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,mixedSpin_expectation]

theorem correlation_affine_filtered (ρ : State) (u : Vec) (f g : ℝ) (i j : Fin 3) :
    correlation (filtered ρ (affineFilter u f g)) i j=
      (f^2-g^2*normSq u)*correlation ρ i j+
      2*g^2*u i*dot u (column (correlation ρ) j)+2*f*g*u i*bobBloch ρ j := by
  unfold correlation
  rw [pauliPair_as_product,filtered,trace_sandwich_move,tensor_pullback]
  rw [(affineFilter_hermitian u f g).eq,affineFilter_pauli_sandwich]
  simp only [onAlice_add,onAlice_smul,onAlice_one,Matrix.add_mul,Matrix.smul_mul,
    Matrix.one_mul,Matrix.mul_add,Matrix.mul_smul,Matrix.trace_add,Matrix.trace_smul,
    smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,mixedSpin_expectation,←pauliPair_as_product]
  rfl

theorem bobBloch_positive_filtered (ρ : State) (u : Vec) (hu : normSq u≤1) (j : Fin 3) :
    bobBloch (filtered ρ (positiveFilter u)) j=
      bobBloch ρ j+dot u (column (correlation ρ) j) := by
  rw [positiveFilter,bobBloch_affine_filtered,(positive_filter_coefficients u hu).1,
    (positive_filter_coefficients u hu).2.2.1]
  ring

theorem correlation_positive_filtered (ρ : State) (u : Vec)
    (hu : normSq u≤1) (i j : Fin 3) :
    correlation (filtered ρ (positiveFilter u)) i j=
      filteredColumn u (column (correlation ρ) j) (filterRadius u) (bobBloch ρ j) i := by
  rw [positiveFilter,correlation_affine_filtered]
  obtain ⟨_,h2,h3,h4⟩ := positive_filter_coefficients u hu
  rw [h2,h3,h4]
  simp only [filteredColumn,spatial,column]
  ring

theorem bobBloch_scaled_filter (ρ : State) (F : QubitMatrix) (r : ℝ) (j : Fin 3) :
    bobBloch (filtered ρ ((r:ℂ) • F)) j=r^2*bobBloch (filtered ρ F) j := by
  unfold bobBloch
  rw [filtered_smul_filter,Matrix.smul_mul,Matrix.trace_smul]
  simp [Complex.star_def,Complex.mul_re,Complex.mul_im,pow_two]

theorem correlation_scaled_filter (ρ : State) (F : QubitMatrix) (r : ℝ) (i j : Fin 3) :
    correlation (filtered ρ ((r:ℂ) • F)) i j=r^2*correlation (filtered ρ F) i j := by
  unfold correlation
  rw [filtered_smul_filter,Matrix.smul_mul,Matrix.trace_smul]
  simp [Complex.star_def,Complex.mul_re,Complex.mul_im,pow_two]

def whitenedBobFormula (a b : Vec) (T : Mat3) : Vec :=
  fun j => (b j-dot a (column T j))/(1-normSq a)

def whitenedCorrelationFormula (a b : Vec) (T : Mat3) : Mat3 :=
  fun i j => (filterRadius a*T i j+
    a i*dot a (column T j)/(1+filterRadius a)-a i*b j)/(1-normSq a)

theorem whitened_bob_formula (ρ : State) (ha : normSq (aliceBloch ρ)<1) :
    whitenedBob ρ=whitenedBobFormula (aliceBloch ρ) (bobBloch ρ) (correlation ρ) := by
  let a := aliceBloch ρ
  have hr : filterRadius a^2=1-normSq a := Real.sq_sqrt (sub_nonneg.mpr ha.le)
  funext j
  change bobBloch (filtered ρ (((filterRadius a)⁻¹:ℂ) • positiveFilter (-a))) j=
    (bobBloch ρ j-dot a (column (correlation ρ) j))/(1-normSq a)
  rw [←Complex.ofReal_inv,bobBloch_scaled_filter,
    bobBloch_positive_filtered ρ (-a) (by simpa [fano_normSq_neg] using ha.le)]
  have hd : dot (-a) (column (correlation ρ) j)= -dot a (column (correlation ρ) j) := by
    simp [dot]
    ring
  rw [hd]
  rw [inv_pow,hr]
  ring

theorem whitened_correlation_formula (ρ : State) (ha : normSq (aliceBloch ρ)<1) :
    whitenedCorrelation ρ=
      whitenedCorrelationFormula (aliceBloch ρ) (bobBloch ρ) (correlation ρ) := by
  let a := aliceBloch ρ
  have hr : filterRadius a^2=1-normSq a := Real.sq_sqrt (sub_nonneg.mpr ha.le)
  have hn : filterRadius a≠0 := ne_of_gt (whitening_radius_positive a ha)
  have hp : 1+filterRadius a≠0 := by have := whitening_radius_positive a ha; linarith
  ext i j
  change correlation (filtered ρ (((filterRadius a)⁻¹:ℂ) • positiveFilter (-a))) i j=
    (filterRadius a*correlation ρ i j+
      a i*dot a (column (correlation ρ) j)/(1+filterRadius a)-a i*bobBloch ρ j)/
      (1-normSq a)
  rw [←Complex.ofReal_inv,correlation_scaled_filter,correlation_positive_filtered ρ (-a)
    (by simpa [fano_normSq_neg] using ha.le),filterRadius_neg]
  have hd : dot (-a) (column (correlation ρ) j)= -dot a (column (correlation ρ) j) := by
    simp [dot]
    ring
  simp only [filteredColumn,spatial,hd,Pi.neg_apply,column]
  rw [←hr]
  field_simp [hn,hp]
  ring

theorem original_whitening_formula (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)<1) :
    filtered ρ (whiteningFilter (aliceBloch ρ))=
      canonical (whitenedBobFormula (aliceBloch ρ) (bobBloch ρ) (correlation ρ))
        (whitenedCorrelationFormula (aliceBloch ρ) (bobBloch ρ) (correlation ρ)) := by
  rw [←whitened_bob_formula ρ ha,←whitened_correlation_formula ρ ha]
  exact whitened_state_canonical ρ hρ ht ha

end UnilateralCHSH.Quantum
