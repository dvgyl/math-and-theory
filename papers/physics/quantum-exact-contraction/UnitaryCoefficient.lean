import GeneralKraus

/-! Exact invariance of conditional hockey-stick ratio sets under unitary
preprocessing and postprocessing, including every finite quantum reference. -/

open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey

namespace UnitaryCoefficient
noncomputable section

variable {A B R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

def channel (U : Matrix A A ℂ) (hU : Uᴴ * U = 1) : QuantumChannel A A :=
  GeneralKraus.channel (fun _ : Unit => U) (by simpa using hU)

@[simp] theorem channel_map (U : Matrix A A ℂ) (hU : Uᴴ * U = 1)
    (X : Matrix A A ℂ) : (channel U hU).map X = U * X * Uᴴ := by
  simp [channel, GeneralKraus.channel_map]

theorem channel_inverse_map (U : Matrix A A ℂ) (hUL : Uᴴ * U = 1)
    (hUR : U * Uᴴ = 1) (X : Matrix A A ℂ) :
    (channel Uᴴ (by simpa using hUR)).map ((channel U hUL).map X) = X := by
  simp only [channel_map, Matrix.conjTranspose_conjTranspose]
  calc
    Uᴴ * (U * X * Uᴴ) * U = (Uᴴ * U) * X * (Uᴴ * U) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [hUL]; simp

omit [Fintype R] [DecidableEq R] in
theorem amplify_inverse [Fintype R] [DecidableEq R] (N : QuantumChannel A B) (L : QuantumChannel B A)
    (hLN : ∀ X, L.map (N.map X) = X)
    (X : Matrix (R × A) (R × A) ℂ) :
    amplify L.map (amplify N.map X) = X := by
  ext r t
  change L.map (N.map (fun a b => X (r.1,a) (t.1,b))) r.2 t.2 = X r t
  rw [hLN]

theorem reversible_traceNorm (N : QuantumChannel A B) (L : QuantumChannel B A)
    (hLN : ∀ X, L.map (N.map X) = X)
    (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) :
    traceNorm (amplify N.map X) (N.amplify_hermitian X hX) = traceNorm X hX := by
  apply le_antisymm (N.amplify_norm_le X hX)
  have h := L.amplify_norm_le (amplify N.map X) (N.amplify_hermitian X hX)
  simpa only [amplify_inverse N L hLN X] using h

theorem reversible_gap (N : QuantumChannel A B) (L : QuantumChannel B A)
    (hLN : ∀ X, L.map (N.map X) = X)
    (X : Matrix (R × A) (R × A) ℂ) (hX : X.IsHermitian) :
    positiveTraceGap (amplify N.map X) (N.amplify_hermitian X hX) =
      positiveTraceGap X hX := by
  rw [positiveTraceGap_eq, positiveTraceGap_eq]
  unfold normGap
  simp only [reversible_traceNorm N L hLN X hX, N.partialTrace_amplify]

theorem difference_output (N : QuantumChannel A B) (γ : ℝ)
    (ρ σ : Density (R × A)) :
    difference γ (N.outputDensity ρ) (N.outputDensity σ) =
      amplify N.map (difference γ ρ σ) := by
  simp only [difference, QuantumChannel.outputDensity, amplify_sub, amplify_real_smul]

theorem reversible_initialGap (N : QuantumChannel A B) (L : QuantumChannel B A)
    (hLN : ∀ X, L.map (N.map X) = X) (γ : ℝ) (ρ σ : Density (R × A)) :
    initialGap γ (N.outputDensity ρ) (N.outputDensity σ) = initialGap γ ρ σ := by
  unfold initialGap
  simp only [difference_output]
  exact reversible_gap N L hLN _ _

theorem density_ext {n : Type} [Fintype n] [DecidableEq n]
    {ρ σ : Density n} (h : ρ.mat = σ.mat) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

theorem output_inverse (N : QuantumChannel A B) (L : QuantumChannel B A)
    (hLN : ∀ X, L.map (N.map X) = X) (ρ : Density (R × A)) :
    L.outputDensity (N.outputDensity ρ) = ρ := by
  apply density_ext
  exact amplify_inverse N L hLN ρ.mat

theorem unitary_initialGap (U : Matrix A A ℂ) (hUL : Uᴴ * U = 1)
    (hUR : U * Uᴴ = 1) (γ : ℝ) (ρ σ : Density (R × A)) :
    initialGap γ ((channel U hUL).outputDensity ρ)
      ((channel U hUL).outputDensity σ) = initialGap γ ρ σ :=
  reversible_initialGap _ (channel Uᴴ (by simpa using hUR))
    (channel_inverse_map U hUL hUR) γ ρ σ

theorem unitary_finalGap (M N : QuantumChannel A B)
    (U : Matrix A A ℂ) (V : Matrix B B ℂ)
    (hUL : Uᴴ * U = 1) (hVL : Vᴴ * V = 1) (hVR : V * Vᴴ = 1)
    (hmap : ∀ X, M.map X = V * N.map (U * X * Uᴴ) * Vᴴ)
    (γ : ℝ) (ρ σ : Density (R × A)) :
    finalGap M γ ρ σ =
      finalGap N γ ((channel U hUL).outputDensity ρ)
        ((channel U hUL).outputDensity σ) := by
  have ha (X : Matrix (R × A) (R × A) ℂ) :
      amplify M.map X = amplify (channel V hVL).map
        (amplify N.map (amplify (channel U hUL).map X)) := by
    ext r t
    change M.map (fun a b => X (r.1,a) (t.1,b)) r.2 t.2 =
      (channel V hVL).map (N.map ((channel U hUL).map
        (fun a b => X (r.1,a) (t.1,b)))) r.2 t.2
    rw [channel_map, channel_map, hmap]
  unfold finalGap
  simp only [difference_output, ha]
  exact reversible_gap _ (channel Vᴴ (by simpa using hVR))
    (channel_inverse_map V hVL hVR) _ _

/-- This is equality of actual attainable state-pair ratios, not just equality
of an upper bound or a chosen family of witnesses. -/
theorem conditionalRatioSet_unitary_equiv (M N : QuantumChannel A B)
    (U : Matrix A A ℂ) (V : Matrix B B ℂ)
    (hUL : Uᴴ * U = 1) (hUR : U * Uᴴ = 1)
    (hVL : Vᴴ * V = 1) (hVR : V * Vᴴ = 1)
    (hmap : ∀ X, M.map X = V * N.map (U * X * Uᴴ) * Vᴴ) (γ : ℝ) :
    conditionalRatioSet M γ = conditionalRatioSet N γ := by
  ext r
  constructor
  · rintro ⟨S,ρ,σ,hpos,hr⟩
    refine ⟨S,(channel U hUL).outputDensity ρ,(channel U hUL).outputDensity σ,?_,?_⟩
    · rwa [unitary_initialGap U hUL hUR]
    · rw [← unitary_finalGap M N U V hUL hVL hVR hmap,
        unitary_initialGap U hUL hUR]
      exact hr
  · rintro ⟨S,ρ,σ,hpos,hr⟩
    let L := channel Uᴴ (by simpa using hUR)
    let ρ' := L.outputDensity ρ
    let σ' := L.outputDensity σ
    have hright (X : Matrix A A ℂ) : (channel U hUL).map (L.map X) = X := by
      change (channel U hUL).map ((channel Uᴴ (by simpa using hUR)).map X) = X
      simpa only [Matrix.conjTranspose_conjTranspose] using
        channel_inverse_map Uᴴ (by simpa using hUR) (by simpa using hUL) X
    have hρ : (channel U hUL).outputDensity ρ' = ρ := output_inverse L _ hright ρ
    have hσ : (channel U hUL).outputDensity σ' = σ := output_inverse L _ hright σ
    have hgap : initialGap γ ρ' σ' = initialGap γ ρ σ := by
      simpa only [hρ,hσ] using (unitary_initialGap U hUL hUR γ ρ' σ').symm
    refine ⟨S,ρ',σ',?_,?_⟩
    · rwa [hgap]
    · rw [unitary_finalGap M N U V hUL hVL hVR hmap,hρ,hσ,hgap]
      exact hr

theorem conditionalCoefficient_unitary_equiv (M N : QuantumChannel A B)
    (U : Matrix A A ℂ) (V : Matrix B B ℂ)
    (hUL : Uᴴ * U = 1) (hUR : U * Uᴴ = 1)
    (hVL : Vᴴ * V = 1) (hVR : V * Vᴴ = 1)
    (hmap : ∀ X, M.map X = V * N.map (U * X * Uᴴ) * Vᴴ) (γ : ℝ) :
    conditionalCoefficient M γ = conditionalCoefficient N γ := by
  unfold conditionalCoefficient
  rw [conditionalRatioSet_unitary_equiv M N U V hUL hUR hVL hVR hmap γ]

end
end UnitaryCoefficient
