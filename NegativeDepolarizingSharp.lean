module
public import BellSupport
public import Mathlib.Analysis.SpecificLimits.Basic


@[expose] public section

/-!
# Sharp lower bound for negative qubit depolarization

The witness uses two actual orthogonal pure density matrices on a three-level
reference and a qubit.  A rational reflection certifies a matching asymptotic
lower bound without assuming a spectral norm formula.
-/

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey
open Filter Topology

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace NegativeDepolarizingSharp
noncomputable section

abbrev Q := Fin 2
abbrev R := Fin 3
abbrev S := R × Q
abbrev StateMat := Matrix S S ℂ

attribute [local simp] Prod.ext_iff

-- Closed finite-index facts keep the entrywise proofs independent of opaque
-- numeral reductions in `Fin 3`.
@[simp] theorem fin3_zero_ne_one : (0 : Fin 3) ≠ 1 := by decide
@[simp] theorem fin3_zero_ne_two : (0 : Fin 3) ≠ 2 := by decide
@[simp] theorem fin3_one_ne_zero : (1 : Fin 3) ≠ 0 := by decide
@[simp] theorem fin3_one_ne_two : (1 : Fin 3) ≠ 2 := by decide
@[simp] theorem fin3_two_ne_zero : (2 : Fin 3) ≠ 0 := by decide
@[simp] theorem fin3_two_ne_one : (2 : Fin 3) ≠ 1 := by decide
@[simp] theorem fin3_mk_eq_two {k : ℕ} {hk : k < 3} :
    (⟨k,hk⟩ : Fin 3) = 2 ↔ k = 2 := Fin.mk.inj_iff
@[simp] theorem fin3_two_eq_mk {k : ℕ} {hk : k < 3} :
    (2 : Fin 3) = ⟨k,hk⟩ ↔ 2 = k := by
  rw [eq_comm, fin3_mk_eq_two, eq_comm]

@[simp] theorem vec3_two (a b c : ℂ) : (![a,b,c] : R → ℂ) 2 = c := rfl

def plusKet (u : ℝ) : S → ℂ := fun p =>
  if p = (0,0) then 1 else if p = (1,1) then u else 0

def minusKet (u : ℝ) : S → ℂ := fun p =>
  if p = (1,0) then u else if p = (2,1) then 1 else 0

def plusRaw (u : ℝ) : StateMat := BellSupport.outer (plusKet u)
def minusRaw (u : ℝ) : StateMat := BellSupport.outer (minusKet u)
def rawDifference (u : ℝ) : StateMat := plusRaw u - minusRaw u

theorem plusRaw_posSemidef (u : ℝ) : (plusRaw u).PosSemidef :=
  BellSupport.outer_posSemidef _

theorem minusRaw_posSemidef (u : ℝ) : (minusRaw u).PosSemidef :=
  BellSupport.outer_posSemidef _

theorem rawDifference_hermitian (u : ℝ) : (rawDifference u).IsHermitian :=
  (plusRaw_posSemidef u).1.sub (minusRaw_posSemidef u).1

theorem plusRaw_trace (u : ℝ) : (plusRaw u).trace = ((1 + u^2 : ℝ) : ℂ) := by
  norm_num [plusRaw, BellSupport.outer, plusKet, Matrix.trace,
    Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.star_def]
  ring

theorem minusRaw_trace (u : ℝ) : (minusRaw u).trace = ((1 + u^2 : ℝ) : ℂ) := by
  norm_num [minusRaw, BellSupport.outer, minusKet, Matrix.trace,
    Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.star_def]
  ring

theorem weight_pos (u : ℝ) : 0 < 1 + u^2 := by nlinarith [sq_nonneg u]

def rho (u : ℝ) : Density S where
  mat := (1 + u^2)⁻¹ • plusRaw u
  positive := posSemidef_real_smul _ (plusRaw_posSemidef u) _
    (inv_nonneg.mpr (weight_pos u).le)
  normalized := by
    rw [Matrix.trace_smul, plusRaw_trace]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (weight_pos u).ne')

def sigma (u : ℝ) : Density S where
  mat := (1 + u^2)⁻¹ • minusRaw u
  positive := posSemidef_real_smul _ (minusRaw_posSemidef u) _
    (inv_nonneg.mpr (weight_pos u).le)
  normalized := by
    rw [Matrix.trace_smul, minusRaw_trace]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (weight_pos u).ne')

theorem state_difference (u : ℝ) :
    difference 1 (rho u) (sigma u) = (1 + u^2)⁻¹ • rawDifference u := by
  simp only [difference, rho, sigma, one_smul, rawDifference, smul_sub]

def referenceDifference : Matrix R R ℂ := Matrix.diagonal ![1,0,-1]

theorem referenceDifference_hermitian : referenceDifference.IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  fin_cases i <;> simp [referenceDifference, _root_.IsSelfAdjoint]

theorem marginal_rawDifference (u : ℝ) :
    partialTraceMatrix (rawDifference u) = referenceDifference := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceMatrix, rawDifference, plusRaw, minusRaw, BellSupport.outer,
      plusKet, minusKet, referenceDifference, Fin.sum_univ_succ, Complex.star_def]

theorem referenceDifference_traceNorm :
    traceNorm referenceDifference referenceDifference_hermitian = 2 := by
  have heq : referenceDifference =
      (basisDensity (0 : R)).mat - (basisDensity (2 : R)).mat := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [referenceDifference, basisDensity]
  have hd : (1 - referenceDifference * referenceDifference).PosSemidef := by
    have hh : 1 - referenceDifference * referenceDifference =
        (basisDensity (1 : R)).mat := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [referenceDifference, basisDensity, Matrix.mul_apply,
          Matrix.one_apply, Fin.sum_univ_succ]
    rw [hh]
    exact (basisDensity (1 : R)).positive
  apply le_antisymm
  · have h := traceNorm_sub_le_of_posSemidef
      (basisDensity (0 : R)).mat (basisDensity (2 : R)).mat
      (basisDensity (0 : R)).positive (basisDensity (2 : R)).positive
    simpa only [heq, (basisDensity (0 : R)).normalized,
      show (1 : ℝ) + 1 = 2 from by norm_num,
      (basisDensity (2 : R)).normalized, Complex.one_re] using h
  · have h := trace_mul_le_traceNorm_of_square_defect referenceDifference
      referenceDifference_hermitian referenceDifference referenceDifference_hermitian hd
    norm_num [referenceDifference, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_succ] at h
    exact h

def inputSign : StateMat := Matrix.diagonal (fun p =>
  if p = (0,0) ∨ p = (1,1) then (1 : ℂ) else -1)

theorem inputSign_hermitian : inputSign.IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro p
  simp only [inputSign, _root_.IsSelfAdjoint]
  split_ifs <;> simp

theorem inputSign_sq : inputSign * inputSign = 1 := by
  rw [inputSign, Matrix.diagonal_mul_diagonal]
  have hh : (fun p : S =>
      (if p = (0,0) ∨ p = (1,1) then (1 : ℂ) else -1) *
      (if p = (0,0) ∨ p = (1,1) then (1 : ℂ) else -1)) = fun _ => 1 := by
    funext p
    split_ifs <;> norm_num
  rw [hh, Matrix.diagonal_one]

theorem inputSign_pairing (u : ℝ) :
    (inputSign * rawDifference u).trace.re = 2 * (1 + u^2) := by
  norm_num [inputSign, rawDifference, plusRaw, minusRaw, BellSupport.outer,
    plusKet, minusKet, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Complex.star_def, Complex.mul_re]
  ring

theorem rawDifference_traceNorm (u : ℝ) :
    traceNorm (rawDifference u) (rawDifference_hermitian u) = 2 * (1 + u^2) := by
  apply le_antisymm
  · have h := traceNorm_sub_le_of_posSemidef (plusRaw u) (minusRaw u)
      (plusRaw_posSemidef u) (minusRaw_posSemidef u)
    rw [plusRaw_trace, minusRaw_trace] at h
    simpa only [Complex.ofReal_re, two_mul] using h
  · have h := trace_mul_le_traceNorm_of_square_defect (rawDifference u)
      (rawDifference_hermitian u) inputSign inputSign_hermitian
      (by rw [inputSign_sq, sub_self]; exact Matrix.PosSemidef.zero)
    rwa [inputSign_pairing] at h

theorem raw_input_gap (u : ℝ) :
    positiveTraceGap (rawDifference u) (rawDifference_hermitian u) = u^2 := by
  rw [positiveTraceGap_eq]
  unfold normGap
  simp only [rawDifference_traceNorm, marginal_rawDifference, referenceDifference_traceNorm]
  ring

theorem initialGap_exact (u : ℝ) :
    initialGap 1 (rho u) (sigma u) = u^2 / (1 + u^2) := by
  unfold initialGap
  simp only [state_difference]
  rw [positiveTraceGap_smul (rawDifference u) (rawDifference_hermitian u) _
    (inv_nonneg.mpr (weight_pos u).le), raw_input_gap]
  ring

def reflectC (t : ℝ) : ℝ := (1-t^2)/(1+t^2)
def reflectD (t : ℝ) : ℝ := 2*t/(1+t^2)

theorem reflect_sq (t : ℝ) : reflectC t ^ 2 + reflectD t ^ 2 = 1 := by
  unfold reflectC reflectD
  field_simp [(weight_pos t).ne']
  ring

/-- Two rational reflections, completed by signed scalar blocks. -/
def outputSign (t : ℝ) : StateMat := fun p q =>
  if p = q then
    if p = (0,0) ∨ p = (1,0) then (reflectC t : ℂ)
    else if p = (1,1) ∨ p = (2,1) then -(reflectC t : ℂ)
    else if p = (0,1) then 1 else -1
  else if (p = (0,0) ∧ q = (1,1)) ∨ (p = (1,1) ∧ q = (0,0)) then -(reflectD t : ℂ)
  else if (p = (1,0) ∧ q = (2,1)) ∨ (p = (2,1) ∧ q = (1,0)) then (reflectD t : ℂ)
  else 0

theorem outputSign_hermitian (t : ℝ) : (outputSign t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    norm_num [outputSign, Complex.star_def]

theorem outputSign_sq (t : ℝ) : outputSign t * outputSign t = 1 := by
  have hh : (reflectC t : ℂ)^2 + (reflectD t : ℂ)^2 = 1 := by
    exact_mod_cast reflect_sq t
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    norm_num [outputSign, Matrix.mul_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ]
  all_goals try ring
  all_goals simpa only [add_comm] using hh

def outputMatrix (s u : ℝ) : StateMat :=
  ((1+s)/2 : ℝ) • (referenceDifference ⊗ₖ (1 : Matrix Q Q ℂ)) - s • rawDifference u

theorem amplify_rawDifference (N : QuantumChannel Q Q) (s : ℝ)
    (hN : ∀ X, N.map X = ((1+s)/2 : ℝ) •
      (X.trace • (1 : Matrix Q Q ℂ)) - s • X) (u : ℝ) :
    amplify N.map (rawDifference u) = outputMatrix s u := by
  ext p q
  change N.map (fun a b => rawDifference u (p.1,a) (q.1,b)) p.2 q.2 = _
  rw [hN]
  change ((1+s)/2 : ℝ) •
      (((partialTraceMatrix (rawDifference u)) p.1 q.1) * (1 : Matrix Q Q ℂ) p.2 q.2) -
      s • rawDifference u p q = _
  rw [marginal_rawDifference]
  rfl

theorem outputSign_pairing (s u t : ℝ) :
    (outputSign t * outputMatrix s u).trace.re =
      (1+s) + (1-s)*reflectC t + 2*s*u^2*reflectC t + 4*s*u*reflectD t := by
  norm_num [outputSign, outputMatrix, rawDifference, plusRaw, minusRaw, BellSupport.outer,
    plusKet, minusKet, referenceDifference, Matrix.trace, Matrix.mul_apply,
    Matrix.kronecker_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Complex.real_smul, Complex.star_def, Complex.mul_re]
  ring

theorem raw_final_gap_lower (N : QuantumChannel Q Q) (s : ℝ)
    (hN : ∀ X, N.map X = ((1+s)/2 : ℝ) •
      (X.trace • (1 : Matrix Q Q ℂ)) - s • X) (u t : ℝ) :
    ((1-s)/2)*(reflectC t-1) + s*u^2*reflectC t + 2*s*u*reflectD t ≤
      positiveTraceGap (amplify N.map (rawDifference u))
        (N.amplify_hermitian _ (rawDifference_hermitian u)) := by
  have h := trace_mul_le_traceNorm_of_square_defect
    (amplify N.map (rawDifference u)) (N.amplify_hermitian _ (rawDifference_hermitian u))
    (outputSign t) (outputSign_hermitian t)
    (by rw [outputSign_sq, sub_self]; exact Matrix.PosSemidef.zero)
  have hpair : (outputSign t * amplify N.map (rawDifference u)).trace.re =
      (1+s) + (1-s)*reflectC t + 2*s*u^2*reflectC t + 4*s*u*reflectD t := by
    rw [amplify_rawDifference N s hN, outputSign_pairing]
  rw [hpair] at h
  simp only [positiveTraceGap_eq, normGap, N.partialTrace_amplify,
    marginal_rawDifference, referenceDifference_traceNorm]
  linarith

def sharpBound (s : ℝ) : ℝ := s*(1+3*s)/(1-s)
def slope (s : ℝ) : ℝ := 2*s/(1-s)
def rationalBound (s u : ℝ) : ℝ :=
  (sharpBound s - s*(slope s)^2*u^2) / (1+(slope s)^2*u^2)

theorem rationalBound_den_pos (s u : ℝ) : 0 < 1+(slope s)^2*u^2 := by
  nlinarith [sq_nonneg (slope s * u)]

theorem rational_lower_identity (s u : ℝ) (hs : s ≠ 1) :
    ((1-s)/2)*(reflectC (slope s*u)-1) + s*u^2*reflectC (slope s*u) +
      2*s*u*reflectD (slope s*u) = u^2*rationalBound s u := by
  have hs' : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hd : 1+(slope s*u)^2 = 1+(slope s)^2*u^2 := by ring
  have hden := (rationalBound_den_pos s u).ne'
  unfold reflectC reflectD rationalBound
  rw [hd]
  field_simp [hden]
  unfold sharpBound slope
  field_simp [hs']
  ring

theorem finalGap_factor (N : QuantumChannel Q Q) (u : ℝ) :
    finalGap N 1 (rho u) (sigma u) = (1+u^2)⁻¹ *
      positiveTraceGap (amplify N.map (rawDifference u))
        (N.amplify_hermitian _ (rawDifference_hermitian u)) := by
  unfold finalGap
  simp only [state_difference, amplify_real_smul]
  exact positiveTraceGap_smul (amplify N.map (rawDifference u))
    (N.amplify_hermitian _ (rawDifference_hermitian u)) _
    (inv_nonneg.mpr (weight_pos u).le)

theorem initialGap_positive (u : ℝ) (hu : 0 < u) :
    0 < initialGap 1 (rho u) (sigma u) := by
  rw [initialGap_exact]
  exact div_pos (sq_pos_of_pos hu) (weight_pos u)

/-- An explicit finite-dimensional family of genuine conditional ratios tends
to the claimed sharp coefficient. -/
theorem rationalBound_le_ratio (N : QuantumChannel Q Q) (s : ℝ) (hs : s ≠ 1)
    (hN : ∀ X, N.map X = ((1+s)/2 : ℝ) •
      (X.trace • (1 : Matrix Q Q ℂ)) - s • X) (u : ℝ) (hu : 0 < u) :
    rationalBound s u ≤ finalGap N 1 (rho u) (sigma u) / initialGap 1 (rho u) (sigma u) := by
  have h := raw_final_gap_lower N s hN u (slope s*u)
  rw [rational_lower_identity s u hs] at h
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (weight_pos u).le)
  apply (le_div_iff₀ (initialGap_positive u hu)).mpr
  rw [initialGap_exact, finalGap_factor]
  convert hm using 1
  all_goals ring

theorem rationalBound_le_coefficient (N : QuantumChannel Q Q) (s : ℝ) (hs : s ≠ 1)
    (hN : ∀ X, N.map X = ((1+s)/2 : ℝ) •
      (X.trace • (1 : Matrix Q Q ℂ)) - s • X) (u : ℝ) (hu : 0 < u) :
    rationalBound s u ≤ conditionalCoefficient N 1 := by
  have hr : finalGap N 1 (rho u) (sigma u) / initialGap 1 (rho u) (sigma u) ∈
      conditionalRatioSet N 1 := by
    refine ⟨⟨R, inferInstance, inferInstance⟩, rho u, sigma u,
      initialGap_positive u hu, rfl⟩
  exact (rationalBound_le_ratio N s hs hN u hu).trans
    (le_csSup (conditionalRatioSet_bddAbove N 1) hr)

theorem rationalBound_continuous (s : ℝ) : Continuous (rationalBound s) := by
  unfold rationalBound
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro u
    exact (rationalBound_den_pos s u).ne'

/-- Sharp lower bound for the actual conditional coefficient, with arbitrary
finite references admitted in its definition. -/
theorem sharpBound_le_conditionalCoefficient (N : QuantumChannel Q Q)
    (s : ℝ) (hs : s ≠ 1)
    (hN : ∀ X, N.map X = ((1+s)/2 : ℝ) •
      (X.trace • (1 : Matrix Q Q ℂ)) - s • X) :
    s*(1+3*s)/(1-s) ≤ conditionalCoefficient N 1 := by
  have hlim : Tendsto (fun n : ℕ => rationalBound s (1/((n:ℝ)+1)))
      atTop (𝓝 (sharpBound s)) := by
    have h := (rationalBound_continuous s).tendsto 0 |>.comp
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [rationalBound, Function.comp_def] using h
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  exact rationalBound_le_coefficient N s hs hN _ (by positivity)

end
end NegativeDepolarizingSharp
