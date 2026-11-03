import QuantumWhiteningOrbit
import QuantumPureMarginal
import QuantumSwap

/-!
End-to-end unilateral CHSH theorems for every actual two-qubit density
matrix, including pure filtered marginals and both filtering parties.
The statements quantify over arbitrary invertible complex 2 by 2 filters
and actual four-observable Bell expectations. The maximum is squared and
the Bell expectation is divided by two (classical threshold one).
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Matrix ComplexOrder
open Matrix
namespace UnilateralCHSH.Quantum

def aliceMaximum (ρ : State) : ℝ :=
  if normSq (aliceBloch ρ)<1 then
    Reduction.canonicalMaximum (whitenedCorrelation ρ) (whitenedBob ρ)
  else normSq (bobBloch ρ)

def bobMaximum (ρ : State) : ℝ := aliceMaximum (swapState ρ)

/-- Eq. 9's arbitrary-complex-filter supremum, for every positive trace-one
two-qubit matrix, without a rank or nondegeneracy assumption. -/
theorem all_states_alice_isLUB (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) : IsLUB (aliceGLValues ρ) (aliceMaximum ρ) := by
  by_cases ha : normSq (aliceBloch ρ)<1
  · rw [aliceMaximum,if_pos ha]
    exact original_fullRank_isLUB ρ hρ ht ha
  · have he : normSq (aliceBloch ρ)=1 := by
      have hn := original_bloch_norm_le ρ hρ ht
      linarith
    rw [aliceMaximum,if_neg ha]
    exact pure_marginal_gl_isLUB ρ hρ ht he

theorem all_states_bob_isLUB (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) : IsLUB (bobGLValues ρ) (bobMaximum ρ) := by
  rw [bobGLValues_eq_alice_swap]
  exact all_states_alice_isLUB (swapState ρ) (swapState_posSemidef ρ hρ)
    (by rwa [swapState_trace])

theorem all_states_both_isLUB (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) :
    IsLUB (aliceGLValues ρ) (aliceMaximum ρ) ∧
      IsLUB (bobGLValues ρ) (bobMaximum ρ) :=
  ⟨all_states_alice_isLUB ρ hρ ht,all_states_bob_isLUB ρ hρ ht⟩

theorem all_states_alice_approximation (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ε : ℝ) (hε : 0<ε) :
    ∃ z∈aliceGLValues ρ, aliceMaximum ρ-ε<z := by
  by_contra h
  push_neg at h
  have hb := (all_states_alice_isLUB ρ hρ ht).2 h
  linarith

theorem all_states_bob_approximation (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ε : ℝ) (hε : 0<ε) :
    ∃ z∈bobGLValues ρ, bobMaximum ρ-ε<z := by
  rw [bobGLValues_eq_alice_swap]
  exact all_states_alice_approximation (swapState ρ) (swapState_posSemidef ρ hρ)
    (by rwa [swapState_trace]) ε hε

theorem all_states_alice_violation_iff_maximum (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) :
    (∃ z∈aliceGLValues ρ, 1<z) ↔ 1<aliceMaximum ρ := by
  constructor
  · rintro ⟨z,hz,hv⟩
    exact lt_of_lt_of_le hv ((all_states_alice_isLUB ρ hρ ht).1 hz)
  · intro hv
    obtain ⟨z,hz,he⟩ := all_states_alice_approximation ρ hρ ht
      ((aliceMaximum ρ-1)/2) (by linarith)
    exact ⟨z,hz,by linarith⟩

def aliceActivationCondition (ρ : State) : Prop :=
  normSq (aliceBloch ρ)<1 ∧
  1<traceThree (covariance (whitenedCorrelation ρ))-normSq (whitenedBob ρ) ∧
  ∃ n : Vec, normSq n=1 ∧
    quad (schurMatrix
      (shift (covariance (whitenedCorrelation ρ)) (-normSq (whitenedBob ρ)))
      (crossMatrix (matVec (whitenedCorrelation ρ) (whitenedBob ρ)))
      (shift (covariance (whitenedCorrelation ρ)) (-normSq (whitenedBob ρ)))⁻¹) n <
        traceThree (covariance (whitenedCorrelation ρ))-normSq (whitenedBob ρ)-1

/-- Necessary and sufficient unilateral activation, with the physical
strict Gram guard and a single actual-inverse Schur Rayleigh test. -/
theorem all_states_alice_activation_iff (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) :
    (∃ z∈aliceGLValues ρ, 1<z) ↔ aliceActivationCondition ρ := by
  by_cases ha : normSq (aliceBloch ρ)<1
  · rw [original_filter_orbit ρ hρ ht ha,canonical_gl_activation_iff _ _
      (whitened_canonical_posSemidef ρ hρ ht ha)]
    simp only [aliceActivationCondition,ha,true_and]
  · have he : normSq (aliceBloch ρ)=1 := by
      have hn := original_bloch_norm_le ρ hρ ht
      linarith
    have hg := pure_marginal_gl_isGreatest ρ hρ ht he
    have hb := original_bob_bloch_norm_le ρ hρ ht
    simp only [aliceActivationCondition,ha,false_and,iff_false]
    rintro ⟨z,hz,hv⟩
    have hu := hg.2 hz
    linarith

theorem all_states_bob_activation_iff (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) :
    (∃ z∈bobGLValues ρ, 1<z) ↔ aliceActivationCondition (swapState ρ) := by
  rw [bobGLValues_eq_alice_swap]
  exact all_states_alice_activation_iff (swapState ρ) (swapState_posSemidef ρ hρ)
    (by rwa [swapState_trace])

def inputCHSHNonviolating (ρ : State) : Prop :=
  ∀ z∈spinCHSHValues ρ, z≤1

theorem input_nonviolating_iff_planes (ρ : State) :
    inputCHSHNonviolating ρ ↔
      ∀ n : Vec, normSq n=1 → Horodecki.planeValue (correlation ρ) n≤1 := by
  rw [Horodecki.exact_chsh_bound]
  constructor
  · intro h a₀ a₁ b₀ b₁ hm
    have hz := h _ ⟨a₀,a₁,b₀,b₁,hm,rfl⟩
    simpa only [bell_expectation_correlation,Horodecki.chshValue] using hz
  · intro h z hz
    obtain ⟨a₀,a₁,b₀,b₁,hm,hv⟩ := hz
    rw [←hv,bell_expectation_correlation]
    exact h a₀ a₁ b₀ b₁ hm

/-- Hidden activation additionally requires that the original, unfiltered
state is CHSH nonviolating. Both parts have explicit correlation conditions. -/
theorem all_states_alice_hidden_activation_iff (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) :
    (inputCHSHNonviolating ρ ∧ ∃ z∈aliceGLValues ρ, 1<z) ↔
      ((∀ n : Vec, normSq n=1 → Horodecki.planeValue (correlation ρ) n≤1) ∧
        aliceActivationCondition ρ) := by
  rw [input_nonviolating_iff_planes,all_states_alice_activation_iff ρ hρ ht]

theorem all_states_bob_hidden_activation_iff (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) :
    (inputCHSHNonviolating ρ ∧ ∃ z∈bobGLValues ρ, 1<z) ↔
      ((∀ n : Vec, normSq n=1 → Horodecki.planeValue (correlation ρ) n≤1) ∧
        aliceActivationCondition (swapState ρ)) := by
  rw [input_nonviolating_iff_planes,all_states_bob_activation_iff ρ hρ ht]

theorem all_states_alice_violation_attained (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (hv : ∃ z∈aliceGLValues ρ, 1<z) :
    IsGreatest (aliceGLValues ρ) (aliceMaximum ρ) := by
  obtain ⟨ha,hg,_⟩ := (all_states_alice_activation_iff ρ hρ ht).mp hv
  rw [aliceMaximum,if_pos ha]
  exact original_fullRank_attainment_under_guard ρ hρ ht ha hg

theorem all_states_bob_violation_attained (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (hv : ∃ z∈bobGLValues ρ, 1<z) :
    IsGreatest (bobGLValues ρ) (bobMaximum ρ) := by
  rw [bobGLValues_eq_alice_swap] at hv ⊢
  exact all_states_alice_violation_attained (swapState ρ) (swapState_posSemidef ρ hρ)
    (by rwa [swapState_trace]) hv

theorem original_finite_candidates (ρ : State) (ha : normSq (aliceBloch ρ)<1) :
    let D := whitenedCorrelation ρ
    let c := whitenedBob ρ
    let A := covariance D
    let C := crossMatrix (matVec D c)
    IsGreatest (Global.candidateValues A C (normSq c) (traceThree A)) (aliceMaximum ρ) ∧
      (Global.candidateValues A C (normSq c) (traceThree A)).ncard≤4 := by
  dsimp only
  rw [aliceMaximum,if_pos ha]
  exact ⟨Global.maximum_isGreatest_candidates _ _ _ _
      (covariance_symmetric _) (crossMatrix_skew _),
    Global.candidateValues_ncard_le_four _ _ _ _
      (covariance_symmetric _) (crossMatrix_skew _)⟩

/-- The physical strict-guard formula is the least eigenvalue of an explicit
three by three Schur matrix, with an actual optimizing complex filter. -/
theorem all_states_alice_schur_formula (ρ : State) (hρ : ρ.PosSemidef)
    (ht : Matrix.trace ρ=1) (ha : normSq (aliceBloch ρ)<1)
    (hg : 1<traceThree (covariance (whitenedCorrelation ρ))-normSq (whitenedBob ρ)) :
    let D := whitenedCorrelation ρ
    let c := whitenedBob ρ
    let K := shift (covariance D) (-normSq c)
    let C := crossMatrix (matVec D c)
    let alpha := traceThree (covariance D)-normSq c
    K.det≠0 ∧ ∃ (r : ℝ) (n : Vec), 0<r ∧ normSq n=1 ∧
      matVec (schurMatrix K C K⁻¹) n=(fun i => r*n i) ∧
      (∀ x : Vec, r*normSq x≤quad (schurMatrix K C K⁻¹) x) ∧
      aliceMaximum ρ=alpha-r ∧ IsGreatest (aliceGLValues ρ) (alpha-r) := by
  dsimp only
  obtain ⟨hd,r,n,v,hr,hn,_,_,_,he,hm,_,hv⟩ := canonical_reduced_shortcut
    (whitenedBob ρ) (whitenedCorrelation ρ) (whitened_canonical_posSemidef ρ hρ ht ha) hg
  have hv' : aliceMaximum ρ=
      traceThree (covariance (whitenedCorrelation ρ))-normSq (whitenedBob ρ)-r := by
    rw [aliceMaximum,if_pos ha]
    exact hv
  refine ⟨hd,r,n,hr,hn,he,hm,hv',?_⟩
  rw [←hv]
  exact original_fullRank_attainment_under_guard ρ hρ ht ha hg

end UnilateralCHSH.Quantum
