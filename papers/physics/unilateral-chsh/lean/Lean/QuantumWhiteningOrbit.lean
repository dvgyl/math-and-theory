import QuantumFilterCoordinates
import CanonicalGLValues

/-! Exact original-state filter orbits and the full-rank marginal optimum. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Matrix ComplexOrder
open Matrix
namespace UnilateralCHSH.Quantum

theorem original_marginalAlice (ρ : State) (hρ : ρ.IsHermitian)
    (ht : Matrix.trace ρ=1) :
    marginalAlice ρ=(1/2:ℂ) • (1+realSpin (aliceBloch ρ)) := by
  conv_lhs => arg 1; rw [fano_complete ρ hρ ht]
  exact marginalAlice_blochState _ _ _

theorem original_marginalBob (ρ : State) (hρ : ρ.IsHermitian)
    (ht : Matrix.trace ρ=1) :
    marginalBob ρ=(1/2:ℂ) • (1+realSpin (bobBloch ρ)) := by
  conv_lhs => arg 1; rw [fano_complete ρ hρ ht]
  exact marginalBob_blochState _ _ _

theorem original_marginalAlice_det (ρ : State) (hρ : ρ.IsHermitian)
    (ht : Matrix.trace ρ=1) :
    (marginalAlice ρ).det=(((1-normSq (aliceBloch ρ))/4:ℝ):ℂ) := by
  rw [original_marginalAlice ρ hρ ht,Matrix.det_smul]
  change (1/2:ℂ)^(Fintype.card Q)*(spinEffect (aliceBloch ρ)).det=_
  rw [spinEffect_det]
  norm_num
  ring

theorem original_marginalAlice_invertible_iff (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) :
    (marginalAlice ρ).det≠0 ↔ normSq (aliceBloch ρ)<1 := by
  rw [original_marginalAlice_det ρ hρ.1 ht]
  constructor
  · intro hd
    have hn := original_bloch_norm_le ρ hρ ht
    have he : normSq (aliceBloch ρ)≠1 := by
      intro he
      apply hd
      rw [he]
      norm_num
    exact lt_of_le_of_ne hn he
  · intro ha
    have hp : 0<(1-normSq (aliceBloch ρ))/4 := by linarith
    exact_mod_cast (ne_of_gt hp)

/-- An arbitrary original state with full-rank Alice marginal has exactly
the same normalized invertible-filter CHSH value set as its canonical state. -/
theorem original_filter_orbit (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)<1) :
    aliceGLValues ρ=canonicalGLValues (whitenedBob ρ) (whitenedCorrelation ρ) := by
  have he := aliceGLValues_filter_invariant ρ (whiteningFilter (aliceBloch ρ))
    (whitening_filter_invertible _ ha)
  change aliceGLValues (whitenedState ρ)=aliceGLValues ρ at he
  rw [whitened_state_canonical ρ hρ ht ha] at he
  exact he.symm

theorem original_filter_orbit_explicit (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)<1) :
    aliceGLValues ρ=
      canonicalGLValues
        (whitenedBobFormula (aliceBloch ρ) (bobBloch ρ) (correlation ρ))
        (whitenedCorrelationFormula (aliceBloch ρ) (bobBloch ρ) (correlation ρ)) := by
  rw [←whitened_bob_formula ρ ha,←whitened_correlation_formula ρ ha]
  exact original_filter_orbit ρ hρ ht ha

theorem original_fullRank_isLUB (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)<1) :
    IsLUB (aliceGLValues ρ)
      (Reduction.canonicalMaximum (whitenedCorrelation ρ) (whitenedBob ρ)) := by
  rw [original_filter_orbit ρ hρ ht ha]
  exact canonical_gl_isLUB _ _

theorem original_fullRank_attainment_under_guard (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)<1)
    (hguard : 1<traceThree (covariance (whitenedCorrelation ρ))-normSq (whitenedBob ρ)) :
    IsGreatest (aliceGLValues ρ)
      (Reduction.canonicalMaximum (whitenedCorrelation ρ) (whitenedBob ρ)) := by
  rw [original_filter_orbit ρ hρ ht ha]
  exact canonical_gl_attains_under_guard _ _ (whitened_canonical_posSemidef ρ hρ ht ha) hguard

theorem original_fullRank_approximation (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)<1) (ε : ℝ) (hε : 0<ε) :
    ∃ z∈aliceGLValues ρ,
      Reduction.canonicalMaximum (whitenedCorrelation ρ) (whitenedBob ρ)-ε<z := by
  rw [original_filter_orbit ρ hρ ht ha]
  exact canonical_gl_approximation _ _ ε hε

end UnilateralCHSH.Quantum
