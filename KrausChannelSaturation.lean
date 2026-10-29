module
public import KrausSaturation
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity


@[expose] public section

/-!
# Complete hockey-stick saturation from a Kraus intertwiner

The coefficient below is the literal supremum over every finite reference
system, genuine density matrices with equal reference marginal, and strictly
positive input hockey-stick divergence. The channel is the concrete CPTP
structure from ConditionalHockey, not a collection of assumed norm bounds.
-/

open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey KrausSaturation

namespace KrausChannelSaturation
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 2048

abbrev Q := Fin 2
abbrev Input := Bool × Q
abbrev InputMat := Matrix Input Input ℂ

theorem positiveTrace_congr {n : Type} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (h : X = Y) :
    positiveTrace X hX = positiveTrace Y hY := by
  cases h
  rfl

def matrixUnit (i j : Q) : Matrix Q Q ℂ := Matrix.single i j 1

theorem matrixUnit_diag_positive (i : Q) : (matrixUnit i i).PosSemidef := by
  have heq : matrixUnit i i = (basisDensity i).mat := by
    ext a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      norm_num [matrixUnit, Matrix.single, basisDensity, Matrix.diagonal]
  rw [heq]
  exact (basisDensity i).positive

theorem matrixUnit_diag_trace (i : Q) : (matrixUnit i i).trace = 1 := by
  fin_cases i <;> norm_num [matrixUnit, Matrix.single, Matrix.trace, Fin.sum_univ_succ]

def phaseVector (s t : ℝ) (i : Input) : ℂ :=
  if i = (false, 0) then (s : ℂ) else if i = (true, 1) then (t : ℂ) else 0

def phaseOuter (s t : ℝ) : InputMat := fun i j => phaseVector s t i * phaseVector s t j

theorem phaseOuter_positive (s t : ℝ) : (phaseOuter s t).PosSemidef := by
  let V : Matrix Input Unit ℂ := fun i _ => phaseVector s t i
  have hv : ∀ i, star (phaseVector s t i) = phaseVector s t i := by
    intro i
    unfold phaseVector
    split_ifs <;> simp [Complex.star_def]
  have heq : phaseOuter s t = V * Vᴴ := by
    ext i j
    change phaseVector s t i * phaseVector s t j = (V * Vᴴ) i j
    rw [Matrix.mul_apply]
    simp only [Fintype.sum_unique, Matrix.conjTranspose_apply]
    change phaseVector s t i * phaseVector s t j =
      phaseVector s t i * star (phaseVector s t j)
    rw [hv]
  rw [heq]
  exact Matrix.posSemidef_self_mul_conjTranspose V

def pairEquiv (B : Type) : (Bool × B) ≃ (B ⊕ B) where
  toFun x := if x.1 then Sum.inr x.2 else Sum.inl x.2
  invFun x := match x with | Sum.inl b => (false,b) | Sum.inr b => (true,b)
  left_inv := by rintro ⟨r,b⟩; cases r <;> rfl
  right_inv := by intro x; cases x <;> rfl

def pairBlocks {B : Type} (P Q R S : Matrix B B ℂ) : Matrix (Bool × B) (Bool × B) ℂ :=
  (Matrix.fromBlocks P Q R S).submatrix (pairEquiv B) (pairEquiv B)

theorem phaseOuter_blocks (s t : ℝ) : phaseOuter s t =
    pairBlocks ((s^2) • matrixUnit 0 0) ((s*t) • matrixUnit 0 1)
      ((s*t) • matrixUnit 1 0) ((t^2) • matrixUnit 1 1) := by
  ext ⟨r,a⟩ ⟨w,b⟩
  cases r <;> cases w <;> fin_cases a <;> fin_cases b <;>
    simp [phaseOuter, phaseVector, pairBlocks, pairEquiv, Matrix.submatrix_apply,
      Matrix.fromBlocks, matrixUnit, Matrix.single, Prod.ext_iff,
      Matrix.smul_apply, Complex.real_smul] <;> ring

variable {B : Type} [Fintype B] [DecidableEq B]

theorem amplify_pairBlocks (N : QuantumChannel Q B) (P Q R S : Matrix (Fin 2) (Fin 2) ℂ) :
    amplify N.map (pairBlocks P Q R S) =
      pairBlocks (N.map P) (N.map Q) (N.map R) (N.map S) := by
  ext ⟨r,b⟩ ⟨s,c⟩
  cases r <;> cases s <;> rfl

theorem channel_offDiagonal_adjoint (N : QuantumChannel Q B) :
    N.map (matrixUnit 1 0) = (N.map (matrixUnit 0 1))ᴴ := by
  have hp := (N.completely_positive Bool (phaseOuter 1 1) (phaseOuter_positive 1 1)).1
  have heq : amplify N.map (phaseOuter 1 1) =
      pairBlocks (N.map (matrixUnit 0 0)) (N.map (matrixUnit 0 1))
        (N.map (matrixUnit 1 0)) (N.map (matrixUnit 1 1)) := by
    rw [phaseOuter_blocks, amplify_pairBlocks]
    norm_num
  ext b c
  have h := hp.apply (true,b) (false,c)
  simpa [heq, pairBlocks, pairEquiv, Matrix.submatrix_apply,
    Matrix.fromBlocks, Matrix.conjTranspose_apply] using h.symm

def phaseRho (u : ℝ) : Density Input where
  mat := (1/(1+u^2) : ℝ) • phaseOuter u 1
  positive := posSemidef_real_smul _ (phaseOuter_positive u 1) _ (by positivity)
  normalized := by
    have hd : (1+(u:ℂ)^2) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < 1+u^2 by positivity))
    simp [phaseOuter, phaseVector, Matrix.trace, Fintype.sum_prod_type,
      Fintype.sum_bool, Fin.sum_univ_succ, Prod.ext_iff, Matrix.smul_apply, Complex.real_smul]
    field_simp [hd]
    all_goals ring

def phaseSigma (u : ℝ) : Density Input where
  mat := (1/(1+u^2) : ℝ) • phaseOuter u (-1)
  positive := posSemidef_real_smul _ (phaseOuter_positive u (-1)) _ (by positivity)
  normalized := by
    have hd : (1+(u:ℂ)^2) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < 1+u^2 by positivity))
    simp [phaseOuter, phaseVector, Matrix.trace, Fintype.sum_prod_type,
      Fintype.sum_bool, Fin.sum_univ_succ, Prod.ext_iff, Matrix.smul_apply, Complex.real_smul]
    field_simp [hd]
    all_goals ring

theorem phase_sameReference (u : ℝ) :
    partialTraceMatrix (phaseRho u).mat = partialTraceMatrix (phaseSigma u).mat := by
  ext r s
  cases r <;> cases s <;>
    simp [phaseRho, phaseSigma, partialTraceMatrix, phaseOuter, phaseVector,
      Fin.sum_univ_succ, Prod.ext_iff, Matrix.smul_apply, Complex.real_smul]

theorem phase_difference_blocks (γ u : ℝ) : difference γ (phaseRho u) (phaseSigma u) =
    (1+u^2)⁻¹ • pairBlocks ((-(γ-1)*u^2) • matrixUnit 0 0)
      (((γ+1)*u) • matrixUnit 0 1) (((γ+1)*u) • matrixUnit 1 0)
      ((-(γ-1)) • matrixUnit 1 1) := by
  have hd : (1+(u:ℂ)^2) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < 1+u^2 by positivity))
  ext ⟨r,a⟩ ⟨s,b⟩
  cases r <;> cases s <;> fin_cases a <;> fin_cases b <;>
    simp [difference, phaseRho, phaseSigma, phaseOuter, phaseVector, pairBlocks,
      pairEquiv, Matrix.submatrix_apply, Matrix.fromBlocks, matrixUnit,
      Matrix.single, Prod.ext_iff, Matrix.smul_apply, Complex.real_smul] <;>
    field_simp [hd] <;> ring

theorem phase_output_blocks (N : QuantumChannel Q B) (γ u : ℝ) :
    amplify N.map (difference γ (phaseRho u) (phaseSigma u)) =
      (normalizedPhaseBlock (N.map (matrixUnit 0 0)) (N.map (matrixUnit 1 1))
        (N.map (matrixUnit 0 1)) (γ-1) (γ+1) u).submatrix (pairEquiv B) (pairEquiv B) := by
  rw [phase_difference_blocks, amplify_real_smul, amplify_pairBlocks]
  simp only [LinearMap.map_smul_of_tower, channel_offDiagonal_adjoint,
    normalizedPhaseBlock, phaseBlock, Matrix.submatrix_smul]
  rfl

def inputUpper (γ u : ℝ) : ℝ := 4*γ*u^2/((γ-1)*(1+u^2))

theorem inputUpper_pos (γ u : ℝ) (hγ : 1 < γ) (hu : 0 < u) : 0 < inputUpper γ u := by
  unfold inputUpper
  exact div_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (sq_pos_of_pos hu))
    (mul_pos (by linarith) (by positivity))

theorem phase_input_upper (γ u : ℝ) (hγ : 1 < γ) (hu : 0 < u) :
    hockeyStick γ (phaseRho u) (phaseSigma u) ≤ inputUpper γ u := by
  let P : InputMat := inputUpper γ u • phaseOuter 1 0
  let S : InputMat := ((γ-1)/(1+u^2) : ℝ) • phaseOuter (-((γ+1)*u/(γ-1))) 1
  have hP : P.PosSemidef := posSemidef_real_smul _ (phaseOuter_positive 1 0) _
    (inputUpper_pos γ u hγ hu).le
  have hS : S.PosSemidef := posSemidef_real_smul _ (phaseOuter_positive _ 1) _
    (div_nonneg (by linarith) (by positivity))
  have hdiff : difference γ (phaseRho u) (phaseSigma u) = P-S := by
    have hd : (1+(u:ℂ)^2) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < 1+u^2 by positivity))
    have hk : (γ:ℂ)-1 ≠ 0 := by exact_mod_cast (ne_of_gt (sub_pos.mpr hγ))
    ext ⟨r,a⟩ ⟨s,b⟩
    cases r <;> cases s <;> fin_cases a <;> fin_cases b <;>
      simp [difference, phaseRho, phaseSigma, P, S, inputUpper, phaseOuter, phaseVector,
        Prod.ext_iff, Matrix.smul_apply, Complex.real_smul] <;>
      field_simp [hd, hk] <;> ring
  have ht : P.trace.re = inputUpper γ u := by
    simp [P, phaseOuter, phaseVector, Matrix.trace, Fintype.sum_prod_type,
      Fintype.sum_bool, Fin.sum_univ_succ, Prod.ext_iff, Matrix.smul_apply, Complex.real_smul]
  have hb := traceNorm_sub_le_of_posSemidef P S hP hS
  unfold hockeyStick
  rw [positiveTrace_congr (difference_hermitian γ (phaseRho u) (phaseSigma u))
    (hP.1.sub hS.1) hdiff, positiveTrace_eq]
  simp only [Matrix.trace_sub, Complex.sub_re]
  rw [← ht]
  linarith

theorem positiveTrace_reindex {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) (e : m ≃ n) :
    positiveTrace (X.submatrix e e) (hX.submatrix e) = positiveTrace X hX := by
  rw [positiveTrace_eq, positiveTrace_eq, traceNorm_submatrix_equiv, trace_submatrix_equiv]

theorem hockey_output_eq {R : Type} [Fintype R] [DecidableEq R]
    (N : QuantumChannel Q B) (γ : ℝ) (ρ σ : Density (R × Q)) :
    hockeyStick γ (N.outputDensity ρ) (N.outputDensity σ) =
      positiveTrace (amplify N.map (difference γ ρ σ)) (N.amplify_hermitian _ (difference_hermitian γ ρ σ)) := by
  unfold hockeyStick
  congr 1
  simp only [difference, QuantumChannel.outputDensity, amplify_sub, amplify_real_smul]

theorem hockey_output_le {R : Type} [Fintype R] [DecidableEq R]
    (N : QuantumChannel Q B) (γ : ℝ) (ρ σ : Density (R × Q)) :
    hockeyStick γ (N.outputDensity ρ) (N.outputDensity σ) ≤ hockeyStick γ ρ σ := by
  rw [hockey_output_eq]
  unfold hockeyStick
  rw [positiveTrace_eq, positiveTrace_eq, N.amplify_trace]
  linarith [N.amplify_norm_le (difference γ ρ σ) (difference_hermitian γ ρ σ)]

theorem phase_output_lower (N : QuantumChannel Q B) (D : Matrix B B ℂ)
    (γ u : ℝ) (hγ : 1 < γ)
    (hquad : D * N.map (matrixUnit 1 1) * Dᴴ = N.map (matrixUnit 0 0))
    (hcross : N.map (matrixUnit 0 1) = D * N.map (matrixUnit 1 1)) :
    inputUpper γ u / (1+((((γ+1)/(γ-1))*u)^2)*graphBound D) ≤
      hockeyStick γ (N.outputDensity (phaseRho u)) (N.outputDensity (phaseSigma u)) := by
  have h₀ := (N.positive _ (matrixUnit_diag_positive 0)).1
  have h₁ := (N.positive _ (matrixUnit_diag_positive 1)).1
  have ht₀ : (N.map (matrixUnit 0 0)).trace = 1 := by
    rw [N.trace_preserving, matrixUnit_diag_trace]
  have hcross' : D * (N.map (matrixUnit 0 1))ᴴ = N.map (matrixUnit 0 0) := by
    rw [hcross, Matrix.conjTranspose_mul, h₁.eq, ← Matrix.mul_assoc]
    exact hquad
  have h := phase_positiveTrace_lower D (N.map (matrixUnit 0 0))
    (N.map (matrixUnit 1 1)) (N.map (matrixUnit 0 1)) γ u hγ h₀ h₁ ht₀ hquad hcross'
  have hblock := normalizedPhaseBlock_hermitian (N.map (matrixUnit 0 0))
    (N.map (matrixUnit 1 1)) (N.map (matrixUnit 0 1)) (γ-1) (γ+1) u h₀ h₁
  rw [hockey_output_eq, positiveTrace_congr
    (N.amplify_hermitian _ (difference_hermitian γ (phaseRho u) (phaseSigma u)))
    (hblock.submatrix (pairEquiv B)) (phase_output_blocks N γ u), positiveTrace_reindex]
  exact h

/-- All finite reference dimensions, genuine equal-reference states, positive denominators. -/
def completeRatioSet (N : QuantumChannel Q B) (γ : ℝ) : Set ℝ := {r |
  ∃ (R : FiniteReference) (ρ σ : Density (R.Carrier × Q)),
    partialTraceMatrix ρ.mat = partialTraceMatrix σ.mat ∧
    0 < hockeyStick γ ρ σ ∧
    r = hockeyStick γ (N.outputDensity ρ) (N.outputDensity σ) / hockeyStick γ ρ σ}

def completeCoefficient (N : QuantumChannel Q B) (γ : ℝ) : ℝ := sSup (completeRatioSet N γ)

theorem completeRatioSet_bddAbove (N : QuantumChannel Q B) (γ : ℝ) :
    BddAbove (completeRatioSet N γ) := by
  refine ⟨1, ?_⟩
  rintro r ⟨R,ρ,σ,_,hpos,rfl⟩
  apply (div_le_iff₀ hpos).mpr
  simpa using hockey_output_le N γ ρ σ

def twoReference : FiniteReference := ⟨Bool, inferInstance, inferInstance⟩

theorem phase_ratio_certificate (N : QuantumChannel Q B) (D : Matrix B B ℂ)
    (γ u : ℝ) (hγ : 1 < γ) (hu : 0 < u)
    (hquad : D * N.map (matrixUnit 1 1) * Dᴴ = N.map (matrixUnit 0 0))
    (hcross : N.map (matrixUnit 0 1) = D * N.map (matrixUnit 1 1)) :
    ∃ r ∈ completeRatioSet N γ,
      1/(1+((((γ+1)/(γ-1))*u)^2)*graphBound D) ≤ r := by
  let H := 1+((((γ+1)/(γ-1))*u)^2)*graphBound D
  have hH : 0 < H := by
    dsimp [H]
    have h := mul_nonneg (sq_nonneg (((γ+1)/(γ-1))*u)) (graphBound_pos D).le
    linarith
  have hout := phase_output_lower N D γ u hγ hquad hcross
  have hinpos : 0 < hockeyStick γ (phaseRho u) (phaseSigma u) :=
    (div_pos (inputUpper_pos γ u hγ hu) hH).trans_le
      (hout.trans (hockey_output_le N γ (phaseRho u) (phaseSigma u)))
  let r := hockeyStick γ (N.outputDensity (phaseRho u)) (N.outputDensity (phaseSigma u)) /
    hockeyStick γ (phaseRho u) (phaseSigma u)
  refine ⟨r, ⟨twoReference, phaseRho u, phaseSigma u, phase_sameReference u, hinpos, rfl⟩, ?_⟩
  apply (le_div_iff₀ hinpos).mpr
  have hmul := mul_le_mul_of_nonneg_left (phase_input_upper γ u hγ hu)
    (le_of_lt (div_pos (by norm_num : (0:ℝ)<1) hH))
  calc
    1/H * hockeyStick γ (phaseRho u) (phaseSigma u) ≤ 1/H * inputUpper γ u := hmul
    _ = inputUpper γ u / H := by ring
    _ ≤ hockeyStick γ (N.outputDensity (phaseRho u)) (N.outputDensity (phaseSigma u)) := hout

/-- A channel block intertwiner forces unit complete contraction at each fixed parameter above one. -/
theorem completeCoefficient_eq_one_of_intertwiner (N : QuantumChannel Q B) (D : Matrix B B ℂ)
    (γ : ℝ) (hγ : 1 < γ)
    (hquad : D * N.map (matrixUnit 1 1) * Dᴴ = N.map (matrixUnit 0 0))
    (hcross : N.map (matrixUnit 0 1) = D * N.map (matrixUnit 1 1)) :
    completeCoefficient N γ = 1 := by
  have hb := completeRatioSet_bddAbove N γ
  have hGB : 0 < graphBound D := graphBound_pos D
  obtain ⟨r,hr,hl⟩ := phase_ratio_certificate N D γ 1 hγ (by norm_num) hquad hcross
  have hn : (completeRatioSet N γ).Nonempty := ⟨r,hr⟩
  have hk0 : 0 ≤ completeCoefficient N γ :=
    (le_trans (by positivity) hl).trans (le_csSup hb hr)
  have hk1 : completeCoefficient N γ ≤ 1 := by
    apply csSup_le hn
    rintro s ⟨R,ρ,σ,_,hpos,rfl⟩
    apply (div_le_iff₀ hpos).mpr
    simpa using hockey_output_le N γ ρ σ
  apply le_antisymm hk1
  by_contra h
  have hk : completeCoefficient N γ < 1 := lt_of_not_ge h
  let c := (γ+1)/(γ-1)
  let K := graphBound D
  have hc : 0 < c := div_pos (by linarith) (by linarith)
  have hK : 0 < K := graphBound_pos D
  have hK1 : 1 ≤ K := graphBound_one_le D
  let δ := 1-completeCoefficient N γ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  let u := δ/(4*c*K)
  have hu : 0 < u := div_pos hδ (mul_pos (mul_pos (by norm_num) hc) hK)
  have heq : c*u*K = δ/4 := by
    dsimp [u]
    field_simp [ne_of_gt hc, ne_of_gt hK]
    all_goals ring
  have hα : 0 ≤ c*u := (mul_pos hc hu).le
  have hαle : c*u ≤ δ/4 := by
    have hm := mul_le_mul_of_nonneg_left hK1 hα
    simpa only [mul_one, heq] using hm
  have hsmall : (c*u)^2*K ≤ δ/16 := by
    have hm := mul_le_mul_of_nonneg_right hαle (by positivity : 0 ≤ δ/4)
    have hδsq : δ^2 ≤ δ := by
      have ht := mul_le_mul_of_nonneg_left hδ1 hδ.le
      simpa [pow_two] using ht
    have hx : (c*u)^2*K = (c*u)*(δ/4) := by rw [← heq]; ring
    rw [hx]
    nlinarith
  obtain ⟨s,hs,hsl⟩ := phase_ratio_certificate N D γ u hγ hu hquad hcross
  have hlower : 1/(1+(c*u)^2*K) ≤ completeCoefficient N γ :=
    hsl.trans (le_csSup hb hs)
  have hden : 0 < 1+(c*u)^2*K := by positivity
  have hm : completeCoefficient N γ * ((c*u)^2*K) ≤ (c*u)^2*K :=
    mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) hK.le) hk1
  have hstrict : completeCoefficient N γ < 1/(1+(c*u)^2*K) := by
    apply (lt_div_iff₀ hden).mpr
    dsimp [δ] at hsmall
    nlinarith
  linarith

/-- Saturation under an actual Kraus representation and a common output intertwiner. -/
theorem completeCoefficient_eq_one_of_kraus {ι : Type} [Fintype ι]
    (N : QuantumChannel Q B) (K : ι → Matrix B Q ℂ) (D : Matrix B B ℂ)
    (hrep : ∀ X, N.map X = ∑ i, K i * X * (K i)ᴴ)
    (hD : ∀ i, D *ᵥ (fun b => K i b 1) = fun b => K i b 0)
    (γ : ℝ) (hγ : 1 < γ) : completeCoefficient N γ = 1 := by
  obtain ⟨hquad,hcross⟩ := kraus_channel_intertwining N K D hrep hD
  exact completeCoefficient_eq_one_of_intertwiner N D γ hγ hquad hcross

theorem positiveTrace_neg_positive {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hP : P.PosSemidef) : positiveTrace (-P) hP.1.neg = 0 := by
  rw [positiveTrace_eq, traceNorm_neg P hP.1, traceNorm_eq_trace_of_posSemidef P hP,
    Matrix.trace_neg, Complex.neg_re]
  ring

theorem initialGap_eq_hockey_of_equalReference {R A : Type}
    [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
    (γ : ℝ) (hγ : 1 ≤ γ) (ρ σ : Density (R × A))
    (href : partialTraceMatrix ρ.mat = partialTraceMatrix σ.mat) :
    initialGap γ ρ σ = hockeyStick γ ρ σ := by
  have hpos : ((γ-1) • partialTraceMatrix ρ.mat).PosSemidef :=
    posSemidef_real_smul _ (partialTraceMatrix_posSemidef ρ.mat ρ.positive) _ (by linarith)
  have hdiff : partialTraceMatrix (difference γ ρ σ) = -((γ-1) • partialTraceMatrix ρ.mat) := by
    rw [difference, partialTraceMatrix_sub, partialTraceMatrix_smul, ← href]
    ext r s
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, Complex.real_smul]
    push_cast
    ring
  unfold initialGap positiveTraceGap hockeyStick
  rw [positiveTrace_congr
    (partialTraceMatrix_hermitian _ (difference_hermitian γ ρ σ)) hpos.1.neg hdiff,
    positiveTrace_neg_positive _ hpos, sub_zero]

theorem finalGap_eq_hockey_of_equalReference {R : Type} [Fintype R] [DecidableEq R]
    (N : QuantumChannel Q B) (γ : ℝ) (hγ : 1 ≤ γ) (ρ σ : Density (R × Q))
    (href : partialTraceMatrix ρ.mat = partialTraceMatrix σ.mat) :
    finalGap N γ ρ σ = hockeyStick γ (N.outputDensity ρ) (N.outputDensity σ) := by
  rw [finalGap_eq_output]
  have href' : partialTraceMatrix (N.outputDensity ρ).mat =
      partialTraceMatrix (N.outputDensity σ).mat := by
    simpa only [QuantumChannel.outputDensity, N.partialTrace_amplify] using href
  exact initialGap_eq_hockey_of_equalReference γ hγ (N.outputDensity ρ) (N.outputDensity σ) href'

theorem completeRatioSet_subset_conditional (N : QuantumChannel Q B) (γ : ℝ) (hγ : 1 ≤ γ) :
    completeRatioSet N γ ⊆ ConditionalHockey.conditionalRatioSet N γ := by
  rintro r ⟨R,ρ,σ,href,hpos,hr⟩
  refine ⟨R,ρ,σ,?_,?_⟩
  · rw [initialGap_eq_hockey_of_equalReference γ hγ ρ σ href]
    exact hpos
  · rw [initialGap_eq_hockey_of_equalReference γ hγ ρ σ href,
      finalGap_eq_hockey_of_equalReference N γ hγ ρ σ href]
    exact hr

/-- The same Kraus criterion saturates conditional trace-distance contraction. -/
theorem conditionalTraceCoefficient_eq_one_of_kraus {ι : Type} [Fintype ι]
    (N : QuantumChannel Q B) (K : ι → Matrix B Q ℂ) (D : Matrix B B ℂ)
    (hrep : ∀ X, N.map X = ∑ i, K i * X * (K i)ᴴ)
    (hD : ∀ i, D *ᵥ (fun b => K i b 1) = fun b => K i b 0) :
    ConditionalHockey.conditionalCoefficient N 1 = 1 := by
  obtain ⟨hquad,hcross⟩ := kraus_channel_intertwining N K D hrep hD
  obtain ⟨r,hr,_⟩ := phase_ratio_certificate N D 2 1 (by norm_num) (by norm_num) hquad hcross
  have hn : (completeRatioSet N 2).Nonempty := ⟨r,hr⟩
  have hsub := completeRatioSet_subset_conditional N 2 (by norm_num)
  have hn' : (ConditionalHockey.conditionalRatioSet N 2).Nonempty := ⟨r,hsub hr⟩
  have hb := ConditionalHockey.conditionalRatioSet_bddAbove N 2
  have hcomplete := completeCoefficient_eq_one_of_kraus N K D hrep hD 2 (by norm_num)
  have hcond : ConditionalHockey.conditionalCoefficient N 2 = 1 := by
    apply le_antisymm
    · exact csSup_le hn' (fun _ hs => (conditionalRatioSet_subset_unitInterval N 2 hs).2)
    · rw [← hcomplete]
      exact csSup_le hn (fun _ hs => le_csSup hb (hsub hs))
  rw [ConditionalHockey.conditionalCoefficient_parameter_independent N 2 (by norm_num)] at hcond
  exact hcond

theorem conditionalHockeyCoefficient_eq_one_of_kraus {ι : Type} [Fintype ι]
    (N : QuantumChannel Q B) (K : ι → Matrix B Q ℂ) (D : Matrix B B ℂ)
    (hrep : ∀ X, N.map X = ∑ i, K i * X * (K i)ᴴ)
    (hD : ∀ i, D *ᵥ (fun b => K i b 1) = fun b => K i b 0)
    (γ : ℝ) (hγ : 1 ≤ γ) : ConditionalHockey.conditionalCoefficient N γ = 1 := by
  rw [ConditionalHockey.conditionalCoefficient_parameter_independent N γ hγ]
  exact conditionalTraceCoefficient_eq_one_of_kraus N K D hrep hD

end
end KrausChannelSaturation
