module
public import FlagBlocks
public import Mathlib.Order.ConditionallyCompleteLattice.Basic


@[expose] public section

/-!
# Conditional hockey-stick coefficients and orthogonal reference flags

The divergence is the trace of the positive spectral part of `rho - gamma sigma`.
Reference systems range over all finite types.  The channel is a complex-linear,
trace-preserving, completely positive map, and amplification is defined explicitly
by applying the channel to each reference block.
-/

open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample

namespace ConditionalHockey

noncomputable section

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Trace of the positive spectral part of a Hermitian matrix. -/
def positiveTrace (X : Matrix n n ℂ) (hX : X.IsHermitian) : ℝ :=
  ∑ i, max (hX.eigenvalues i) 0

theorem positiveTrace_eq (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    positiveTrace X hX = (traceNorm X hX + X.trace.re) / 2 := by
  have hpoint : ∀ x : ℝ, max x 0 = (|x| + x) / 2 := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx, abs_of_nonneg hx]
      ring
    · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      rw [max_eq_right hx', abs_of_nonpos hx']
      ring
  have htrace : X.trace.re = ∑ i, hX.eigenvalues i := by
    have h := congrArg Complex.re (trace_eq_sum_hermitian_eigenvalues X hX)
    simpa only [Complex.re_sum, Complex.ofReal_re] using h
  unfold positiveTrace traceNorm
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_add_distrib, htrace]

variable {R A B : Type} [Fintype R] [DecidableEq R]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def normGap (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) : ℝ :=
  traceNorm X hX - traceNorm (partialTraceMatrix X) (partialTraceMatrix_hermitian X hX)

/-- The reference-subtracted positive-part divergence of a Hermitian difference. -/
def positiveTraceGap (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) : ℝ :=
  positiveTrace X hX - positiveTrace (partialTraceMatrix X)
    (partialTraceMatrix_hermitian X hX)

theorem positiveTraceGap_eq (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) :
    positiveTraceGap X hX = normGap X hX / 2 := by
  unfold positiveTraceGap normGap
  rw [positiveTrace_eq, positiveTrace_eq, partialTraceMatrix_trace]
  ring

theorem partialTrace_norm_le (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) :
    traceNorm (partialTraceMatrix X) (partialTraceMatrix_hermitian X hX) ≤ traceNorm X hX :=
  traceNorm_map_le partialTraceMatrix partialTraceMatrix_sub partialTraceMatrix_posSemidef
    partialTraceMatrix_trace X hX (partialTraceMatrix_hermitian X hX)

theorem positiveTraceGap_nonneg (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) :
    0 ≤ positiveTraceGap X hX := by
  rw [positiveTraceGap_eq]
  exact div_nonneg (sub_nonneg.mpr (partialTrace_norm_le X hX)) (by norm_num)

theorem normGap_smul (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian)
    (c : ℝ) (hc : 0 ≤ c) :
    normGap (c • X) (hermitian_real_smul X hX c) = c * normGap X hX := by
  unfold normGap
  rw [traceNorm_real_smul X hX c hc]
  simp only [partialTraceMatrix_smul]
  rw [traceNorm_real_smul (partialTraceMatrix X) (partialTraceMatrix_hermitian X hX) c hc]
  ring

theorem positiveTraceGap_smul (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian)
    (c : ℝ) (hc : 0 ≤ c) :
    positiveTraceGap (c • X) (hermitian_real_smul X hX c) = c * positiveTraceGap X hX := by
  rw [positiveTraceGap_eq, positiveTraceGap_eq, normGap_smul X hX c hc]
  ring

theorem positiveTraceGap_flag_posSemidef (X : Matrix (R × A) (R × A) ℂ)
    (W : Matrix A A ℂ) (hX : X.IsHermitian) (hW : W.PosSemidef) :
    positiveTraceGap (flagMatrix X W) (flagMatrix_hermitian X W hX hW.1) =
      positiveTraceGap X hX := by
  rw [positiveTraceGap_eq, positiveTraceGap_eq]
  unfold normGap
  rw [traceNorm_gap_flagMatrix_posSemidef X W hX hW]

theorem positiveTraceGap_flag_neg_posSemidef (X : Matrix (R × A) (R × A) ℂ)
    (W : Matrix A A ℂ) (hX : X.IsHermitian) (hW : W.PosSemidef) :
    positiveTraceGap (flagMatrix X (-W)) (flagMatrix_hermitian X (-W) hX hW.1.neg) =
      positiveTraceGap X hX := by
  rw [positiveTraceGap_eq, positiveTraceGap_eq]
  unfold normGap
  rw [traceNorm_gap_flagMatrix_neg_posSemidef X W hX hW]

/-- A normalized positive-semidefinite density matrix. -/
structure Density (n : Type) [Fintype n] [DecidableEq n] where
  mat : Matrix n n ℂ
  positive : mat.PosSemidef
  normalized : mat.trace = 1

def basisDensity (a : A) : Density A where
  mat := Matrix.diagonal (fun b => if b = a then 1 else 0)
  positive := by
    apply Matrix.PosSemidef.diagonal
    intro b
    change (0 : ℂ) ≤ if b = a then 1 else 0
    split_ifs <;> norm_num
  normalized := by simp [Matrix.trace_diagonal]

def liftDensity (ρ : Density (R × A)) : Density ((R ⊕ Unit) × A) where
  mat := flagMatrix ρ.mat 0
  positive := flagMatrix_posSemidef _ _ ρ.positive Matrix.PosSemidef.zero
  normalized := by rw [flagMatrix_trace, Matrix.trace_zero, add_zero, ρ.normalized]

def mixFlagDensity (ρ : Density (R × A)) (ω : Density A)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : Density ((R ⊕ Unit) × A) where
  mat := flagMatrix (c • ρ.mat) ((1 - c) • ω.mat)
  positive := flagMatrix_posSemidef _ _
    (posSemidef_real_smul _ ρ.positive c hc0)
    (posSemidef_real_smul _ ω.positive (1 - c) (sub_nonneg.mpr hc1))
  normalized := by
    rw [flagMatrix_trace, Matrix.trace_smul, Matrix.trace_smul, ρ.normalized, ω.normalized]
    simp only [Complex.real_smul, mul_one, Complex.ofReal_sub, Complex.ofReal_one]
    ring

/-- Explicit matrix amplification by the identity on the reference factor. -/
def amplify (N : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (X : Matrix (R × A) (R × A) ℂ) : Matrix (R × B) (R × B) ℂ :=
  fun r s => N (fun a b => X (r.1, a) (s.1, b)) r.2 s.2

omit [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem amplify_sub [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (N : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (X Y : Matrix (R × A) (R × A) ℂ) :
    amplify N (X - Y) = amplify N X - amplify N Y := by
  ext r s
  exact congrArg (fun M : Matrix B B ℂ => M r.2 s.2)
    (N.map_sub (fun a b => X (r.1, a) (s.1, b)) (fun a b => Y (r.1, a) (s.1, b)))

omit [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem amplify_real_smul [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (N : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (X : Matrix (R × A) (R × A) ℂ) (c : ℝ) :
    amplify N (c • X) = c • amplify N X := by
  ext r s
  exact congrArg (fun M : Matrix B B ℂ => M r.2 s.2)
    (N.map_smul_of_tower c (fun a b => X (r.1, a) (s.1, b)))

omit [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem amplify_flagMatrix [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (N : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (X : Matrix (R × A) (R × A) ℂ) (W : Matrix A A ℂ) :
    amplify N (flagMatrix X W) = flagMatrix (amplify N X) (N W) := by
  ext ⟨r, b⟩ ⟨s, c⟩
  rcases r with r | u <;> rcases s with s | v <;>
    simp [amplify, flagMatrix_inl_inl, flagMatrix_inl_inr,
      flagMatrix_inr_inl, flagMatrix_inr_inr, map_zero]
  all_goals
    change N (0 : Matrix A A ℂ) b c = 0
    rw [map_zero]
    rfl

/-- A finite-dimensional complex-linear CPTP map, with CP stated for the explicit amplification. -/
structure QuantumChannel (A B : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] where
  map : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ
  trace_preserving : ∀ X, (map X).trace = X.trace
  completely_positive : ∀ (R : Type) [Fintype R] [DecidableEq R]
    (X : Matrix (R × A) (R × A) ℂ), X.PosSemidef → (amplify map X).PosSemidef

namespace QuantumChannel

theorem positive (N : QuantumChannel A B) (X : Matrix A A ℂ) (hX : X.PosSemidef) :
    (N.map X).PosSemidef := by
  have h := N.completely_positive Unit
    (X.submatrix (fun i : Unit × A => i.2) (fun i : Unit × A => i.2))
    (hX.submatrix (fun i : Unit × A => i.2))
  exact h.submatrix (fun b => ((), b))

theorem amplify_hermitian (N : QuantumChannel A B)
    (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) :
    (amplify N.map X).IsHermitian := by
  obtain ⟨P, Q, hP, hQ, hdiff, _⟩ := exists_posSemidef_decomposition X hX
  rw [hdiff, amplify_sub]
  exact (N.completely_positive R P hP).1.sub (N.completely_positive R Q hQ).1

omit [Fintype R] [DecidableEq R] in
theorem partialTrace_amplify [Fintype R] [DecidableEq R] (N : QuantumChannel A B)
    (X : Matrix (R × A) (R × A) ℂ) :
    partialTraceMatrix (amplify N.map X) = partialTraceMatrix X := by
  ext r s
  exact N.trace_preserving (fun a b => X (r, a) (s, b))

theorem amplify_trace (N : QuantumChannel A B) (X : Matrix (R × A) (R × A) ℂ) :
    (amplify N.map X).trace = X.trace := by
  rw [← partialTraceMatrix_trace, N.partialTrace_amplify, partialTraceMatrix_trace]

theorem amplify_norm_le (N : QuantumChannel A B)
    (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) :
    traceNorm (amplify N.map X) (N.amplify_hermitian X hX) ≤ traceNorm X hX :=
  traceNorm_map_le (amplify N.map) (amplify_sub N.map) (N.completely_positive R)
    N.amplify_trace X hX (N.amplify_hermitian X hX)

def outputDensity (N : QuantumChannel A B) (ρ : Density (R × A)) : Density (R × B) where
  mat := amplify N.map ρ.mat
  positive := N.completely_positive R ρ.mat ρ.positive
  normalized := by rw [N.amplify_trace, ρ.normalized]

end QuantumChannel

def difference (γ : ℝ) (ρ σ : Density n) : Matrix n n ℂ := ρ.mat - γ • σ.mat

theorem difference_hermitian (γ : ℝ) (ρ σ : Density n) : (difference γ ρ σ).IsHermitian :=
  ρ.positive.1.sub (hermitian_real_smul σ.mat σ.positive.1 γ)

/-- The quantum hockey-stick divergence, with its usual positive-part definition. -/
def hockeyStick (γ : ℝ) (ρ σ : Density n) : ℝ :=
  positiveTrace (difference γ ρ σ) (difference_hermitian γ ρ σ)

/-- At parameter one, the actual hockey-stick divergence is the usual trace distance. -/
theorem hockeyStick_one_eq_traceDistance (ρ σ : Density n) :
    hockeyStick 1 ρ σ = traceNorm (ρ.mat - σ.mat) (ρ.positive.1.sub σ.positive.1) / 2 := by
  unfold hockeyStick difference
  simp only [one_smul]
  rw [positiveTrace_eq, Matrix.trace_sub, ρ.normalized, σ.normalized,
    sub_self, Complex.zero_re, add_zero]

def marginalDensity (ρ : Density (R × A)) : Density R where
  mat := partialTraceMatrix ρ.mat
  positive := partialTraceMatrix_posSemidef ρ.mat ρ.positive
  normalized := by rw [partialTraceMatrix_trace, ρ.normalized]

def initialGap (γ : ℝ) (ρ σ : Density (R × A)) : ℝ :=
  positiveTraceGap (difference γ ρ σ) (difference_hermitian γ ρ σ)

/-- The defined gap is literally the divergence minus the marginal divergence. -/
theorem initialGap_eq (γ : ℝ) (ρ σ : Density (R × A)) :
    initialGap γ ρ σ = hockeyStick γ ρ σ - hockeyStick γ (marginalDensity ρ) (marginalDensity σ) := by
  unfold initialGap positiveTraceGap hockeyStick
  congr 1
  simp only [difference, partialTraceMatrix_sub, partialTraceMatrix_smul, marginalDensity]

def finalGap (N : QuantumChannel A B) (γ : ℝ) (ρ σ : Density (R × A)) : ℝ :=
  positiveTraceGap (amplify N.map (difference γ ρ σ))
    (N.amplify_hermitian _ (difference_hermitian γ ρ σ))

theorem finalGap_eq_output (N : QuantumChannel A B) (γ : ℝ) (ρ σ : Density (R × A)) :
    finalGap N γ ρ σ = initialGap γ (N.outputDensity ρ) (N.outputDensity σ) := by
  unfold finalGap initialGap
  congr 1
  simp only [difference, amplify_sub, amplify_real_smul, QuantumChannel.outputDensity]

/-- The numerator uses the original reference marginal, since a channel preserves it. -/
theorem finalGap_eq (N : QuantumChannel A B) (γ : ℝ) (ρ σ : Density (R × A)) :
    finalGap N γ ρ σ = hockeyStick γ (N.outputDensity ρ) (N.outputDensity σ) -
      hockeyStick γ (marginalDensity ρ) (marginalDensity σ) := by
  rw [finalGap_eq_output, initialGap_eq]
  congr 1
  unfold hockeyStick difference
  simp only [marginalDensity, QuantumChannel.outputDensity, N.partialTrace_amplify]

theorem finalGap_nonneg (N : QuantumChannel A B) (γ : ℝ) (ρ σ : Density (R × A)) :
    0 ≤ finalGap N γ ρ σ :=
  positiveTraceGap_nonneg _ (N.amplify_hermitian _ (difference_hermitian γ ρ σ))

theorem finalGap_le_initialGap (N : QuantumChannel A B) (γ : ℝ) (ρ σ : Density (R × A)) :
    finalGap N γ ρ σ ≤ initialGap γ ρ σ := by
  have h := N.amplify_norm_le (difference γ ρ σ) (difference_hermitian γ ρ σ)
  unfold finalGap initialGap
  rw [positiveTraceGap_eq, positiveTraceGap_eq]
  unfold normGap
  simp only [N.partialTrace_amplify]
  linarith

theorem forward_difference (γ : ℝ) (hγ : 1 ≤ γ)
    (ρ σ : Density (R × A)) (ω : Density A) :
    difference 1
      (mixFlagDensity ρ ω γ⁻¹ (inv_nonneg.mpr (zero_le_one.trans hγ))
        (inv_le_one_of_one_le₀ hγ)) (liftDensity σ) =
      flagMatrix (γ⁻¹ • difference γ ρ σ) ((1 - γ⁻¹) • ω.mat) := by
  have hne : γ ≠ 0 := (zero_lt_one.trans_le hγ).ne'
  simp only [difference, mixFlagDensity, liftDensity, one_smul]
  rw [flagMatrix_sub]
  simp only [sub_zero, smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem reverse_difference (γ : ℝ) (hγ : 1 ≤ γ)
    (ρ σ : Density (R × A)) (ω : Density A) :
    difference γ (liftDensity ρ)
      (mixFlagDensity σ ω γ⁻¹ (inv_nonneg.mpr (zero_le_one.trans hγ))
        (inv_le_one_of_one_le₀ hγ)) =
      flagMatrix (difference 1 ρ σ) (-((γ - 1) • ω.mat)) := by
  have hne : γ ≠ 0 := (zero_lt_one.trans_le hγ).ne'
  have hc : γ * (1 - γ⁻¹) = γ - 1 := by rw [mul_sub, mul_one, mul_inv_cancel₀ hne]
  simp only [difference, mixFlagDensity, liftDensity, one_smul]
  rw [flagMatrix_smul, flagMatrix_sub]
  simp only [smul_smul, mul_inv_cancel₀ hne, one_smul, hc, zero_sub]

/-- The forward flag construction preserves both gaps by the same positive factor. -/
theorem forward_gaps (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 ≤ γ)
    (ρ σ : Density (R × A)) (ω : Density A) :
    ∃ P Q : Density ((R ⊕ Unit) × A),
      initialGap 1 P Q = γ⁻¹ * initialGap γ ρ σ ∧
      finalGap N 1 P Q = γ⁻¹ * finalGap N γ ρ σ := by
  let P := mixFlagDensity ρ ω γ⁻¹ (inv_nonneg.mpr (zero_le_one.trans hγ))
    (inv_le_one_of_one_le₀ hγ)
  let Q := liftDensity σ
  have hc0 : 0 ≤ γ⁻¹ := inv_nonneg.mpr (zero_le_one.trans hγ)
  have hc1 : 0 ≤ 1 - γ⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hγ)
  have hdiff : difference 1 P Q =
      flagMatrix (γ⁻¹ • difference γ ρ σ) ((1 - γ⁻¹) • ω.mat) :=
    forward_difference γ hγ ρ σ ω
  refine ⟨P, Q, ?_, ?_⟩
  · unfold initialGap
    simp only [hdiff]
    rw [positiveTraceGap_flag_posSemidef _ _
      (hermitian_real_smul _ (difference_hermitian γ ρ σ) γ⁻¹)
      (posSemidef_real_smul _ ω.positive _ hc1)]
    exact positiveTraceGap_smul _ (difference_hermitian γ ρ σ) γ⁻¹ hc0
  · have houtput : amplify N.map (difference 1 P Q) =
        flagMatrix (γ⁻¹ • amplify N.map (difference γ ρ σ))
          ((1 - γ⁻¹) • N.map ω.mat) := by
      rw [hdiff, amplify_flagMatrix, amplify_real_smul, N.map.map_smul_of_tower]
    unfold finalGap
    simp only [houtput]
    rw [positiveTraceGap_flag_posSemidef _ _
      (hermitian_real_smul _ (N.amplify_hermitian _ (difference_hermitian γ ρ σ)) γ⁻¹)
      (posSemidef_real_smul _ (N.positive ω.mat ω.positive) _ hc1)]
    exact positiveTraceGap_smul _ (N.amplify_hermitian _ (difference_hermitian γ ρ σ)) γ⁻¹ hc0

/-- The reverse flag construction preserves both gaps exactly. -/
theorem reverse_gaps (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 ≤ γ)
    (ρ σ : Density (R × A)) (ω : Density A) :
    ∃ P Q : Density ((R ⊕ Unit) × A),
      initialGap γ P Q = initialGap 1 ρ σ ∧
      finalGap N γ P Q = finalGap N 1 ρ σ := by
  let P := liftDensity ρ
  let Q := mixFlagDensity σ ω γ⁻¹ (inv_nonneg.mpr (zero_le_one.trans hγ))
    (inv_le_one_of_one_le₀ hγ)
  have hc : 0 ≤ γ - 1 := sub_nonneg.mpr hγ
  have hdiff : difference γ P Q =
      flagMatrix (difference 1 ρ σ) (-((γ - 1) • ω.mat)) :=
    reverse_difference γ hγ ρ σ ω
  refine ⟨P, Q, ?_, ?_⟩
  · unfold initialGap
    simp only [hdiff]
    exact positiveTraceGap_flag_neg_posSemidef _ _ (difference_hermitian 1 ρ σ)
      (posSemidef_real_smul _ ω.positive _ hc)
  · have houtput : amplify N.map (difference γ P Q) =
        flagMatrix (amplify N.map (difference 1 ρ σ))
          (-((γ - 1) • N.map ω.mat)) := by
      rw [hdiff, amplify_flagMatrix, N.map.map_neg, N.map.map_smul_of_tower]
    unfold finalGap
    simp only [houtput]
    exact positiveTraceGap_flag_neg_posSemidef _ _
      (N.amplify_hermitian _ (difference_hermitian 1 ρ σ))
      (posSemidef_real_smul _ (N.positive ω.mat ω.positive) _ hc)

/-- All finite reference systems are included, with no fixed dimension bound. -/
structure FiniteReference where
  Carrier : Type
  fintype : Fintype Carrier
  decidableEq : DecidableEq Carrier

attribute [instance] FiniteReference.fintype FiniteReference.decidableEq

def FiniteReference.flag (R : FiniteReference) : FiniteReference where
  Carrier := R.Carrier ⊕ Unit
  fintype := inferInstance
  decidableEq := inferInstance

/-- The exact attainable ratios, with strictly positive denominators and genuine density matrices. -/
def conditionalRatioSet (N : QuantumChannel A B) (γ : ℝ) : Set ℝ := {r |
  ∃ (R : FiniteReference) (ρ σ : Density (R.Carrier × A)),
    0 < initialGap γ ρ σ ∧ r = finalGap N γ ρ σ / initialGap γ ρ σ}

theorem conditionalRatioSet_subset_unitInterval (N : QuantumChannel A B) (γ : ℝ) :
    conditionalRatioSet N γ ⊆ Set.Icc 0 1 := by
  rintro r ⟨R, ρ, σ, hpos, rfl⟩
  constructor
  · exact div_nonneg (finalGap_nonneg N γ ρ σ) hpos.le
  · apply (div_le_iff₀ hpos).mpr
    simpa using finalGap_le_initialGap N γ ρ σ

theorem conditionalRatioSet_bddAbove (N : QuantumChannel A B) (γ : ℝ) :
    BddAbove (conditionalRatioSet N γ) :=
  ⟨1, fun _ hr => (conditionalRatioSet_subset_unitInterval N γ hr).2⟩

/-- A single orthogonal reference flag gives equality of the complete attainable ratio sets. -/
theorem conditionalRatioSet_parameter_independent_of_density (N : QuantumChannel A B)
    (γ : ℝ) (hγ : 1 ≤ γ) (ω : Density A) :
    conditionalRatioSet N γ = conditionalRatioSet N 1 := by
  ext r
  constructor
  · rintro ⟨R, ρ, σ, hpos, hr⟩
    obtain ⟨P, Q, hI, hF⟩ := forward_gaps N γ hγ ρ σ ω
    refine ⟨R.flag, P, Q, ?_, ?_⟩
    · rw [hI]
      exact mul_pos (inv_pos.mpr (zero_lt_one.trans_le hγ)) hpos
    · rw [hF, hI, mul_div_mul_left _ _ (inv_pos.mpr (zero_lt_one.trans_le hγ)).ne']
      exact hr
  · rintro ⟨R, ρ, σ, hpos, hr⟩
    obtain ⟨P, Q, hI, hF⟩ := reverse_gaps N γ hγ ρ σ ω
    refine ⟨R.flag, P, Q, ?_, ?_⟩
    · rwa [hI]
    · rwa [hF, hI]

theorem conditionalRatioSet_parameter_independent [Nonempty A] (N : QuantumChannel A B)
    (γ : ℝ) (hγ : 1 ≤ γ) : conditionalRatioSet N γ = conditionalRatioSet N 1 := by
  exact conditionalRatioSet_parameter_independent_of_density N γ hγ
    (basisDensity (Classical.choice ‹Nonempty A›))

/-- The usual conditional contraction coefficient, as the supremum of genuine ratios. -/
def conditionalCoefficient (N : QuantumChannel A B) (γ : ℝ) : ℝ :=
  sSup (conditionalRatioSet N γ)

/-- Universal parameter independence of conditional quantum hockey-stick contraction. -/
theorem conditionalCoefficient_parameter_independent [Nonempty A] (N : QuantumChannel A B)
    (γ : ℝ) (hγ : 1 ≤ γ) : conditionalCoefficient N γ = conditionalCoefficient N 1 := by
  unfold conditionalCoefficient
  rw [conditionalRatioSet_parameter_independent N γ hγ]

end

end ConditionalHockey
