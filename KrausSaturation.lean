module
public import ConditionalHockey
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases


@[expose] public section

/-!
# Explicit graph effects for Kraus-support saturation arguments

These are matrix lemmas for an actual quantum measurement effect.  No channel
saturation conclusion is asserted in this file until its state and limiting
arguments have also been formalized.
-/

open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample
open ConditionalHockey

namespace KrausSaturation

noncomputable section

variable {B : Type} [Fintype B] [DecidableEq B]

/-- A PSD matrix is dominated by its trace times the identity. -/
theorem posSemidef_trace_domination (P : Matrix B B ℂ) (hP : P.PosSemidef) :
    (P.trace.re • (1 : Matrix B B ℂ) - P).PosSemidef := by
  let U := hP.1.eigenvectorUnitary.1
  let L : Matrix B B ℂ := Matrix.diagonal (Complex.ofReal ∘ hP.1.eigenvalues)
  let Q : Matrix B B ℂ := Matrix.diagonal
    (fun i => ((P.trace.re - hP.1.eigenvalues i : ℝ) : ℂ))
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hP.1.eigenvectorUnitary
  have hspec : P = U * L * Uᴴ := hP.1.spectral_theorem
  have htrace : ∑ i, hP.1.eigenvalues i = P.trace.re := by
    have h := congrArg Complex.re (trace_eq_sum_hermitian_eigenvalues P hP.1)
    simpa only [Complex.re_sum, Complex.ofReal_re] using h.symm
  have hQ : Q.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    have hle : hP.1.eigenvalues i ≤ P.trace.re := by
      rw [← htrace]
      exact Finset.single_le_sum (fun j _ => hP.eigenvalues_nonneg j) (Finset.mem_univ i)
    exact RCLike.ofReal_nonneg.mpr (sub_nonneg.mpr hle)
  have hQeq : Q = P.trace.re • (1 : Matrix B B ℂ) - L := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Q, L, Matrix.diagonal, Matrix.one_apply, Complex.real_smul]
    · simp [Q, L, Matrix.diagonal, Matrix.one_apply, hij, Complex.real_smul]
  have heq : P.trace.re • (1 : Matrix B B ℂ) - P = U * Q * Uᴴ := by
    simp only [hQeq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hU, ← hspec]
  rw [heq]
  exact hQ.mul_mul_conjTranspose_same U

def graphBound (D : Matrix B B ℂ) : ℝ := 1 + (Dᴴ * D).trace.re

theorem graphBound_one_le (D : Matrix B B ℂ) : 1 ≤ graphBound D := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self D
  have ht : 0 ≤ (Dᴴ * D).trace.re := by
    rw [← traceNorm_eq_trace_of_posSemidef _ hp]
    exact traceNorm_nonneg _ hp.1
  dsimp [graphBound]
  linarith

theorem graphBound_pos (D : Matrix B B ℂ) : 0 < graphBound D := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self D
  have ht : 0 ≤ (Dᴴ * D).trace.re := by
    rw [← traceNorm_eq_trace_of_posSemidef _ hp]
    exact traceNorm_nonneg _ hp.1
  dsimp [graphBound]
  linarith

theorem graphBound_dom_right (D : Matrix B B ℂ) :
    (graphBound D • (1 : Matrix B B ℂ) - Dᴴ * D).PosSemidef := by
  have h := Matrix.PosSemidef.one.add
    (posSemidef_trace_domination (Dᴴ * D) (Matrix.posSemidef_conjTranspose_mul_self D))
  simpa only [graphBound, add_smul, one_smul, sub_eq_add_neg, add_assoc] using h

theorem graphBound_dom_left (D : Matrix B B ℂ) :
    (graphBound D • (1 : Matrix B B ℂ) - D * Dᴴ).PosSemidef := by
  have h := Matrix.PosSemidef.one.add
    (posSemidef_trace_domination (D * Dᴴ) (Matrix.posSemidef_self_mul_conjTranspose D))
  have ht : (D * Dᴴ).trace.re = (Dᴴ * D).trace.re :=
    congrArg Complex.re (Matrix.trace_mul_comm D Dᴴ)
  simpa only [graphBound, ht, add_smul, one_smul, sub_eq_add_neg, add_assoc] using h

def graphColumn (D : Matrix B B ℂ) (α : ℝ) : Matrix (B ⊕ B) (B ⊕ B) ℂ :=
  Matrix.fromBlocks 1 0 (α • Dᴴ) 0

def graphGram (D : Matrix B B ℂ) (α : ℝ) : Matrix (B ⊕ B) (B ⊕ B) ℂ :=
  Matrix.fromBlocks 1 (α • D) (α • Dᴴ) ((α ^ 2) • (Dᴴ * D))

theorem graphColumn_gram (D : Matrix B B ℂ) (α : ℝ) :
    graphColumn D α * (graphColumn D α)ᴴ = graphGram D α := by
  simp only [graphColumn, graphGram, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_smul,
    star_trivial, Matrix.conjTranspose_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]

theorem graphGram_posSemidef (D : Matrix B B ℂ) (α : ℝ) : (graphGram D α).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (graphColumn D α)
  rwa [graphColumn_gram] at h

def complementColumn (D : Matrix B B ℂ) (α : ℝ) : Matrix (B ⊕ B) (B ⊕ B) ℂ :=
  Matrix.fromBlocks (α • D) 0 (-1) 0

def complementGram (D : Matrix B B ℂ) (α : ℝ) : Matrix (B ⊕ B) (B ⊕ B) ℂ :=
  Matrix.fromBlocks ((α ^ 2) • (D * Dᴴ)) (-(α • D)) (-(α • Dᴴ)) 1

theorem complementColumn_gram (D : Matrix B B ℂ) (α : ℝ) :
    complementColumn D α * (complementColumn D α)ᴴ = complementGram D α := by
  simp only [complementColumn, complementGram, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_neg, star_trivial, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_neg, Matrix.neg_mul, smul_neg, neg_neg, pow_two]

theorem complementGram_posSemidef (D : Matrix B B ℂ) (α : ℝ) :
    (complementGram D α).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (complementColumn D α)
  rwa [complementColumn_gram] at h

theorem graph_complement_decomposition (D : Matrix B B ℂ) (α K : ℝ) :
    (1 + α ^ 2 * K) • (1 : Matrix (B ⊕ B) (B ⊕ B) ℂ) - graphGram D α =
      complementGram D α + blockSum
        ((α ^ 2) • (K • (1 : Matrix B B ℂ) - D * Dᴴ))
        ((α ^ 2) • (K • (1 : Matrix B B ℂ) - Dᴴ * D)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases hij : i = j <;>
    simp [graphGram, complementGram, blockSum, Matrix.fromBlocks,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
      Complex.real_smul, hij] <;> ring

def graphEffect (D : Matrix B B ℂ) (α K : ℝ) : Matrix (B ⊕ B) (B ⊕ B) ℂ :=
  (1 + α ^ 2 * K)⁻¹ • graphGram D α

theorem graphEffect_posSemidef (D : Matrix B B ℂ) (α K : ℝ) (hK : 0 ≤ K) :
    (graphEffect D α K).PosSemidef := by
  apply posSemidef_real_smul _ (graphGram_posSemidef D α)
  apply inv_nonneg.mpr
  linarith [mul_nonneg (sq_nonneg α) hK]

theorem graphEffect_complement_posSemidef (D : Matrix B B ℂ) (α K : ℝ) (hK : 0 ≤ K)
    (hleft : (K • (1 : Matrix B B ℂ) - D * Dᴴ).PosSemidef)
    (hright : (K • (1 : Matrix B B ℂ) - Dᴴ * D).PosSemidef) :
    (1 - graphEffect D α K).PosSemidef := by
  have hden : 0 < 1 + α ^ 2 * K := by linarith [mul_nonneg (sq_nonneg α) hK]
  have hblock := blockSum_posSemidef _ _
    (posSemidef_real_smul _ hleft (α ^ 2) (sq_nonneg α))
    (posSemidef_real_smul _ hright (α ^ 2) (sq_nonneg α))
  have hdefect : ((1 + α ^ 2 * K) • (1 : Matrix (B ⊕ B) (B ⊕ B) ℂ) -
      graphGram D α).PosSemidef := by
    rw [graph_complement_decomposition]
    exact (complementGram_posSemidef D α).add hblock
  have h := posSemidef_real_smul _ hdefect (1 + α ^ 2 * K)⁻¹
    (inv_nonneg.mpr hden.le)
  have heq : (1 + α ^ 2 * K)⁻¹ •
      ((1 + α ^ 2 * K) • (1 : Matrix (B ⊕ B) (B ⊕ B) ℂ) - graphGram D α) =
      1 - graphEffect D α K := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hden.ne', one_smul]
    rfl
  rwa [heq] at h

/-- An explicit genuine measurement effect for every matrix and every real parameter. -/
theorem graphEffect_is_effect (D : Matrix B B ℂ) (α : ℝ) :
    (graphEffect D α (graphBound D)).PosSemidef ∧
      (1 - graphEffect D α (graphBound D)).PosSemidef :=
  ⟨graphEffect_posSemidef D α (graphBound D) (graphBound_pos D).le,
    graphEffect_complement_posSemidef D α (graphBound D) (graphBound_pos D).le
      (graphBound_dom_left D) (graphBound_dom_right D)⟩

/-- Every genuine measurement effect is a lower certificate for the positive spectral part. -/
theorem effect_pairing_le_positiveTrace (X F : Matrix B B ℂ) (hX : X.IsHermitian)
    (hF : F.PosSemidef) (hFc : (1 - F).PosSemidef) :
    (F * X).trace.re ≤ positiveTrace X hX := by
  have hmEq : 1 - ((2 : ℝ) • F - 1) = (2 : ℝ) • (1 - F) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
    norm_num
    ring
  have hpEq : 1 + ((2 : ℝ) • F - 1) = (2 : ℝ) • F := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
    ring
  have hm : (1 - ((2 : ℝ) • F - 1)).PosSemidef := by
    rw [hmEq]
    exact posSemidef_real_smul _ hFc 2 (by norm_num)
  have hp : (1 + ((2 : ℝ) • F - 1)).PosSemidef := by
    rw [hpEq]
    exact posSemidef_real_smul _ hF 2 (by norm_num)
  have h := trace_mul_le_traceNorm X hX ((2 : ℝ) • F - 1) hm hp
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, Complex.sub_re, Complex.smul_re, smul_eq_mul] at h
  rw [positiveTrace_eq]
  linarith

omit [DecidableEq B] in
theorem trace_fromBlocks [DecidableEq B] (P Q R S : Matrix B B ℂ) :
    (Matrix.fromBlocks P Q R S).trace = P.trace + S.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.fromBlocks]

def phaseBlock (τ₀ τ₁ C : Matrix B B ℂ) (k h u : ℝ) : Matrix (B ⊕ B) (B ⊕ B) ℂ :=
  Matrix.fromBlocks ((-k * u ^ 2) • τ₀) ((h * u) • C)
    ((h * u) • Cᴴ) ((-k) • τ₁)

theorem phaseBlock_hermitian (τ₀ τ₁ C : Matrix B B ℂ) (k h u : ℝ)
    (h₀ : τ₀.IsHermitian) (h₁ : τ₁.IsHermitian) : (phaseBlock τ₀ τ₁ C k h u).IsHermitian := by
  apply (hermitian_real_smul τ₀ h₀ (-k * u ^ 2)).fromBlocks
  · simp only [Matrix.conjTranspose_smul, star_trivial]
  · exact hermitian_real_smul τ₁ h₁ (-k)

def normalizedPhaseBlock (τ₀ τ₁ C : Matrix B B ℂ) (k h u : ℝ) :
    Matrix (B ⊕ B) (B ⊕ B) ℂ := (1 + u ^ 2)⁻¹ • phaseBlock τ₀ τ₁ C k h u

theorem normalizedPhaseBlock_hermitian (τ₀ τ₁ C : Matrix B B ℂ) (k h u : ℝ)
    (h₀ : τ₀.IsHermitian) (h₁ : τ₁.IsHermitian) :
    (normalizedPhaseBlock τ₀ τ₁ C k h u).IsHermitian :=
  hermitian_real_smul _ (phaseBlock_hermitian τ₀ τ₁ C k h u h₀ h₁) _

/-- The graph effect's unscaled pairing, using the two exact intertwining identities. -/
theorem graphGram_phase_pairing (D τ₀ τ₁ C : Matrix B B ℂ) (α k h u : ℝ)
    (h₀ : τ₀.IsHermitian) (ht₀ : τ₀.trace = 1)
    (hquad : D * τ₁ * Dᴴ = τ₀) (hcross : D * Cᴴ = τ₀) :
    (graphGram D α * phaseBlock τ₀ τ₁ C k h u).trace =
      ((-k * u ^ 2 + 2 * α * h * u - k * α ^ 2 : ℝ) : ℂ) := by
  have hcross' : C * Dᴴ = τ₀ := by
    have h := congrArg Matrix.conjTranspose hcross
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h₀.eq] using h
  have htCross : (Dᴴ * C).trace = τ₀.trace := by
    rw [Matrix.trace_mul_comm, hcross']
  have htQuad : (Dᴴ * D * τ₁).trace = τ₀.trace := by
    calc
      (Dᴴ * D * τ₁).trace = (D * τ₁ * Dᴴ).trace := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = τ₀.trace := congrArg Matrix.trace hquad
  simp only [graphGram, phaseBlock, Matrix.fromBlocks_multiply, trace_fromBlocks,
    Matrix.trace_add, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_smul, hcross, htCross, htQuad, ht₀, Complex.real_smul]
  push_cast
  ring

theorem graphEffect_phase_pairing (D τ₀ τ₁ C : Matrix B B ℂ) (α K k h u : ℝ)
    (h₀ : τ₀.IsHermitian) (ht₀ : τ₀.trace = 1)
    (hquad : D * τ₁ * Dᴴ = τ₀) (hcross : D * Cᴴ = τ₀) :
    (graphEffect D α K * normalizedPhaseBlock τ₀ τ₁ C k h u).trace.re =
      (-k * u ^ 2 + 2 * α * h * u - k * α ^ 2) /
        ((1 + u ^ 2) * (1 + α ^ 2 * K)) := by
  simp only [graphEffect, normalizedPhaseBlock, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  rw [graphGram_phase_pairing D τ₀ τ₁ C α k h u h₀ ht₀ hquad hcross]
  simp only [Complex.ofReal_re, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem graphEffect_phase_pairing_specialized (D τ₀ τ₁ C : Matrix B B ℂ)
    (γ u K : ℝ) (hγ : 1 < γ) (hK : 0 ≤ K)
    (h₀ : τ₀.IsHermitian) (ht₀ : τ₀.trace = 1)
    (hquad : D * τ₁ * Dᴴ = τ₀) (hcross : D * Cᴴ = τ₀) :
    (graphEffect D (((γ + 1) / (γ - 1)) * u) K *
      normalizedPhaseBlock τ₀ τ₁ C (γ - 1) (γ + 1) u).trace.re =
      (4 * γ * u ^ 2 / ((γ - 1) * (1 + u ^ 2))) /
        (1 + ((((γ + 1) / (γ - 1)) * u) ^ 2) * K) := by
  rw [graphEffect_phase_pairing D τ₀ τ₁ C _ K _ _ u h₀ ht₀ hquad hcross]
  have hk : γ - 1 ≠ 0 := (sub_pos.mpr hγ).ne'
  have hu : 1 + u ^ 2 ≠ 0 := by nlinarith [sq_nonneg u]
  have hd : 1 + ((((γ + 1) / (γ - 1)) * u) ^ 2) * K ≠ 0 := by
    have hp := mul_nonneg (sq_nonneg (((γ + 1) / (γ - 1)) * u)) hK
    linarith
  field_simp [hk, hu, hd]
  ring

/-- An explicit lower bound for the actual positive spectral part of the phase output block. -/
theorem phase_positiveTrace_lower (D τ₀ τ₁ C : Matrix B B ℂ)
    (γ u : ℝ) (hγ : 1 < γ) (h₀ : τ₀.IsHermitian) (h₁ : τ₁.IsHermitian)
    (ht₀ : τ₀.trace = 1) (hquad : D * τ₁ * Dᴴ = τ₀) (hcross : D * Cᴴ = τ₀) :
    (4 * γ * u ^ 2 / ((γ - 1) * (1 + u ^ 2))) /
        (1 + ((((γ + 1) / (γ - 1)) * u) ^ 2) * graphBound D) ≤
      positiveTrace (normalizedPhaseBlock τ₀ τ₁ C (γ - 1) (γ + 1) u)
        (normalizedPhaseBlock_hermitian τ₀ τ₁ C (γ - 1) (γ + 1) u h₀ h₁) := by
  let α := ((γ + 1) / (γ - 1)) * u
  have heffect := graphEffect_is_effect D α
  have h := effect_pairing_le_positiveTrace
    (normalizedPhaseBlock τ₀ τ₁ C (γ - 1) (γ + 1) u)
    (graphEffect D α (graphBound D))
    (normalizedPhaseBlock_hermitian τ₀ τ₁ C (γ - 1) (γ + 1) u h₀ h₁)
    heffect.1 heffect.2
  rw [graphEffect_phase_pairing_specialized D τ₀ τ₁ C γ u (graphBound D)
    hγ (graphBound_pos D).le h₀ ht₀ hquad hcross] at h
  exact h

variable {ι : Type} [Fintype ι]

omit [Fintype B] [DecidableEq B] in
/-- A matrix-unit sandwich is the outer product of the selected Kraus columns. -/
theorem matrixUnit_sandwich_entry [Fintype B] [DecidableEq B] (L K : Matrix B (Fin 2) ℂ)
    (i j : Fin 2) (b c : B) :
    (L * Matrix.single i j (1 : ℂ) * Kᴴ) b c = L b i * star (K c j) := by
  classical
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply]

theorem kraus_single_cross (D : Matrix B B ℂ) (K : Matrix B (Fin 2) ℂ)
    (hD : D *ᵥ (fun b => K b 1) = fun b => K b 0) :
    D * (K * Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) * Kᴴ) =
      K * Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) * Kᴴ := by
  have hcol : ∀ b, (D * K) b 1 = K b 0 := by
    intro b
    exact congrFun hD b
  have heq : D * (K * Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) * Kᴴ) =
      (D * K) * Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) * Kᴴ := by
    simp only [Matrix.mul_assoc]
  rw [heq]
  ext b c
  rw [matrixUnit_sandwich_entry, matrixUnit_sandwich_entry, hcol]

theorem kraus_single_quadratic (D : Matrix B B ℂ) (K : Matrix B (Fin 2) ℂ)
    (hD : D *ᵥ (fun b => K b 1) = fun b => K b 0) :
    D * (K * Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) * Kᴴ) * Dᴴ =
      K * Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) * Kᴴ := by
  have hcol : ∀ b, (D * K) b 1 = K b 0 := by
    intro b
    exact congrFun hD b
  have heq : D * (K * Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) * Kᴴ) * Dᴴ =
      (D * K) * Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) * (D * K)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [heq]
  ext b c
  rw [matrixUnit_sandwich_entry, matrixUnit_sandwich_entry, hcol, hcol]

/-- The pointwise Kraus-column condition gives the exact channel intertwining identities. -/
theorem kraus_channel_intertwining (N : QuantumChannel (Fin 2) B)
    (K : ι → Matrix B (Fin 2) ℂ) (D : Matrix B B ℂ)
    (hrep : ∀ X, N.map X = ∑ i, K i * X * (K i)ᴴ)
    (hD : ∀ i, D *ᵥ (fun b => K i b 1) = fun b => K i b 0) :
    D * N.map (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)) * Dᴴ =
        N.map (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)) ∧
      N.map (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) =
        D * N.map (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)) := by
  constructor
  · rw [hrep, hrep]
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact kraus_single_quadratic D (K i) (hD i)
  · rw [hrep, hrep]
    rw [Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (kraus_single_cross D (K i) (hD i)).symm

end

end KrausSaturation
