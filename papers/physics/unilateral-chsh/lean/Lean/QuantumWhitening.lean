import QuantumFano
import CanonicalEffects
import QuantumLocalUnitary

/-!
Exact whitening of an arbitrary full-rank Alice marginal.  The filter is
explicit and its two-sided inverse is the positive square-root effect filter.
No normal-form or orbit statement is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix
namespace UnilateralCHSH.Quantum

theorem fano_normSq_neg (a : Vec) : normSq (-a)=normSq a := by
  simp [normSq,dot]

theorem filterRadius_neg (a : Vec) : filterRadius (-a)=filterRadius a := by
  simp only [filterRadius,fano_normSq_neg]

theorem filterScale_neg (a : Vec) : filterScale (-a)=filterScale a := by
  simp only [filterScale,filterRadius_neg]

theorem affineFilter_antipodal_product (a : Vec) (f g : ℝ) :
    affineFilter (-a) f g * affineFilter a f g =
      ((f^2-g^2*normSq a : ℝ) : ℂ) • (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [affineFilter,realSpin,complexSpin,normSq,dot,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.one_apply,Complex.mul_re,Complex.mul_im,pow_two]
  all_goals ring

theorem positive_filter_antipodal_product (a : Vec) (ha : normSq a≤1) :
    positiveFilter (-a)*positiveFilter a = (filterRadius a : ℂ) • 1 := by
  unfold positiveFilter
  rw [filterRadius_neg,filterScale_neg,affineFilter_antipodal_product,
    (positive_filter_coefficients a ha).2.1]

theorem positive_filter_product_antipodal (a : Vec) (ha : normSq a≤1) :
    positiveFilter a*positiveFilter (-a) = (filterRadius a : ℂ) • 1 := by
  have h := positive_filter_antipodal_product (-a) (by simpa [fano_normSq_neg] using ha)
  simpa [filterRadius_neg] using h

def whiteningFilter (a : Vec) : QubitMatrix :=
  ((filterRadius a)⁻¹ : ℂ) • positiveFilter (-a)

def whitenedState (ρ : State) : State := filtered ρ (whiteningFilter (aliceBloch ρ))

def whitenedBob (ρ : State) : Vec := bobBloch (whitenedState ρ)

def whitenedCorrelation (ρ : State) : Mat3 := correlation (whitenedState ρ)

theorem whitening_radius_positive (a : Vec) (ha : normSq a<1) : 0<filterRadius a :=
  Real.sqrt_pos.mpr (sub_pos.mpr ha)

theorem whitening_filter_hermitian (a : Vec) : (whiteningFilter a).IsHermitian := by
  change (whiteningFilter a)ᴴ=whiteningFilter a
  rw [whiteningFilter,Matrix.conjTranspose_smul,(positive_filter_hermitian (-a)).eq]
  simp

theorem whitening_inverse_left (a : Vec) (ha : normSq a<1) :
    whiteningFilter a * positiveFilter a = 1 := by
  have hr : filterRadius a≠0 := ne_of_gt (whitening_radius_positive a ha)
  rw [whiteningFilter,Matrix.smul_mul,positive_filter_antipodal_product a ha.le,
    smul_smul]
  simp [hr]

theorem whitening_inverse_right (a : Vec) (ha : normSq a<1) :
    positiveFilter a * whiteningFilter a = 1 := by
  have hr : filterRadius a≠0 := ne_of_gt (whitening_radius_positive a ha)
  rw [whiteningFilter,Matrix.mul_smul,positive_filter_product_antipodal a ha.le,
    smul_smul]
  simp [hr]

theorem whitening_filter_invertible (a : Vec) (ha : normSq a<1) :
    (whiteningFilter a).det≠0 := by
  have hd := congrArg Matrix.det (whitening_inverse_left a ha)
  rw [Matrix.det_mul,Matrix.det_one] at hd
  intro hz
  simp [hz] at hd

theorem whitening_effect_identity (a : Vec) (ha : normSq a<1) :
    whiteningFilter a*(1+realSpin a)*(whiteningFilter a)ᴴ = 1 := by
  rw [(whitening_filter_hermitian a).eq]
  change whiteningFilter a*spinEffect a*whiteningFilter a=1
  rw [←positive_filter_effect_square a ha.le]
  calc
    _ = (whiteningFilter a*positiveFilter a)*(positiveFilter a*whiteningFilter a) := by
      noncomm_ring
    _ = 1 := by rw [whitening_inverse_left a ha,whitening_inverse_right a ha]; simp

theorem whitened_bloch_marginal (a b : Vec) (T : Mat3) (ha : normSq a<1) :
    marginalAlice (filtered (blochState a b T) (whiteningFilter a))=
      (1/2:ℂ) • (1 : QubitMatrix) := by
  rw [marginalAlice_filtered,marginalAlice_blochState,Matrix.mul_smul,
    Matrix.smul_mul,whitening_effect_identity a ha]

theorem whitened_bloch_trace (a b : Vec) (T : Mat3) (ha : normSq a<1) :
    Matrix.trace (filtered (blochState a b T) (whiteningFilter a))=1 := by
  rw [←trace_marginalAlice,whitened_bloch_marginal a b T ha]
  norm_num [Matrix.trace,Matrix.diag,Fin.sum_univ_two]

theorem whitened_bloch_is_canonical (a b : Vec) (T : Mat3)
    (hρ : (blochState a b T).PosSemidef) (ha : normSq a<1) :
    filtered (blochState a b T) (whiteningFilter a)=
      canonical (bobBloch (filtered (blochState a b T) (whiteningFilter a)))
        (correlation (filtered (blochState a b T) (whiteningFilter a))) :=
  canonical_of_marginal _ (filtered_psd hρ _).1 (whitened_bloch_marginal a b T ha)

theorem whitened_state_marginal (ρ : State) (hρ : ρ.IsHermitian)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)<1) :
    marginalAlice (whitenedState ρ)=(1/2:ℂ) • (1 : QubitMatrix) := by
  unfold whitenedState
  conv_lhs => arg 1; arg 1; rw [fano_complete ρ hρ ht]
  exact whitened_bloch_marginal _ _ _ ha

theorem whitened_state_trace (ρ : State) (hρ : ρ.IsHermitian)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)<1) :
    Matrix.trace (whitenedState ρ)=1 := by
  rw [←trace_marginalAlice,whitened_state_marginal ρ hρ ht ha]
  norm_num [Matrix.trace,Matrix.diag,Fin.sum_univ_two]

theorem whitened_state_canonical (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)<1) :
    whitenedState ρ=canonical (whitenedBob ρ) (whitenedCorrelation ρ) :=
  canonical_of_marginal _ (filtered_psd hρ _).1 (whitened_state_marginal ρ hρ.1 ht ha)

theorem whitened_canonical_posSemidef (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)<1) :
    (canonical (whitenedBob ρ) (whitenedCorrelation ρ)).PosSemidef := by
  rw [←whitened_state_canonical ρ hρ ht ha]
  exact filtered_psd hρ _

theorem original_bloch_norm_le (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) : normSq (aliceBloch ρ)≤1 := by
  have hf := fano_complete ρ hρ.1 ht
  have hp : (blochState (aliceBloch ρ) (bobBloch ρ) (correlation ρ)).PosSemidef := by
    rw [←hf]
    exact hρ
  exact one_add_realSpin_posSemidef_norm _ (bloch_alice_effect_posSemidef _ _ _ hp)

theorem original_bob_bloch_norm_le (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) : normSq (bobBloch ρ)≤1 := by
  have hf := fano_complete ρ hρ.1 ht
  have hp : (blochState (aliceBloch ρ) (bobBloch ρ) (correlation ρ)).PosSemidef := by
    rw [←hf]
    exact hρ
  exact one_add_realSpin_posSemidef_norm _ (bloch_bob_effect_posSemidef _ _ _ hp)

end UnilateralCHSH.Quantum
