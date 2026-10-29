module
public import GeneralContraction


@[expose] public section

/-! Transport of the explicit equal-reference phase witnesses through an encoder. -/
open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey
open KrausSaturation KrausChannelSaturation

namespace PhaseTransport
noncomputable section
set_option maxHeartbeats 2000000
variable {A B S R m n : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
  [Fintype R] [DecidableEq R] [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n]

def amplifyLinear (N : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) :
    Matrix (R × A) (R × A) ℂ →ₗ[ℂ] Matrix (R × B) (R × B) ℂ where
  toFun := amplify N
  map_add' X Y := by
    ext r s
    exact congrArg (fun M : Matrix B B ℂ => M r.2 s.2)
      (N.map_add (fun a b => X (r.1,a) (s.1,b)) (fun a b => Y (r.1,a) (s.1,b)))
  map_smul' c X := by
    ext r s
    exact congrArg (fun M : Matrix B B ℂ => M r.2 s.2)
      (N.map_smul c (fun a b => X (r.1,a) (s.1,b)))

def reindexChannel (N : QuantumChannel A B) (e : n ≃ B) : QuantumChannel A n where
  map := {
    toFun := fun X => (N.map X).submatrix e e
    map_add' := by intro X Y; rw [map_add]; rfl
    map_smul' := by intro c X; rw [map_smul]; rfl }
  trace_preserving X := by
    change ((N.map X).submatrix e e).trace = X.trace
    rw [trace_submatrix_equiv, N.trace_preserving]
  completely_positive R _ _ X hX :=
    (N.completely_positive R X hX).submatrix (fun p : R × n => (p.1,e p.2))

theorem reindex_intertwiner (M : QuantumChannel Q B) (D : Matrix B B ℂ)
    (e : n ≃ B)
    (hquad : D * M.map (matrixUnit 1 1) * Dᴴ = M.map (matrixUnit 0 0))
    (hcross : M.map (matrixUnit 0 1) = D * M.map (matrixUnit 1 1)) :
    D.submatrix e e * (reindexChannel M e).map (matrixUnit 1 1) * (D.submatrix e e)ᴴ =
        (reindexChannel M e).map (matrixUnit 0 0) ∧
    (reindexChannel M e).map (matrixUnit 0 1) =
      D.submatrix e e * (reindexChannel M e).map (matrixUnit 1 1) := by
  constructor
  · change D.submatrix e e * (M.map (matrixUnit 1 1)).submatrix e e * (D.submatrix e e)ᴴ =
      (M.map (matrixUnit 0 0)).submatrix e e
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hquad]
  · change (M.map (matrixUnit 0 1)).submatrix e e =
      D.submatrix e e * (M.map (matrixUnit 1 1)).submatrix e e
    rw [Matrix.submatrix_mul_equiv, hcross]

def reindexDensity (ρ : Density n) (e : m ≃ n) : Density m where
  mat := ρ.mat.submatrix e e
  positive := ρ.positive.submatrix e
  normalized := by rw [trace_submatrix_equiv, ρ.normalized]

theorem density_ext (ρ σ : Density n) (h : ρ.mat = σ.mat) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

theorem hockeyStick_reindex (γ : ℝ) (ρ σ : Density n) (e : m ≃ n) :
    hockeyStick γ (reindexDensity ρ e) (reindexDensity σ e) = hockeyStick γ ρ σ := by
  unfold hockeyStick
  have hd : difference γ (reindexDensity ρ e) (reindexDensity σ e) =
      (difference γ ρ σ).submatrix e e := rfl
  rw [positiveTrace_congr _ ((difference_hermitian γ ρ σ).submatrix e) hd,
    positiveTrace_reindex]

def encodedDensity (E : QuantumChannel Q (S × A)) (ρ : Density (R × Q)) :
    Density ((R × S) × A) :=
  reindexDensity (E.outputDensity ρ) (Equiv.prodAssoc R S A)

theorem encoded_hockey_le (E : QuantumChannel Q (S × A)) (γ : ℝ)
    (ρ σ : Density (R × Q)) :
    hockeyStick γ (encodedDensity E ρ) (encodedDensity E σ) ≤ hockeyStick γ ρ σ := by
  rw [encodedDensity, encodedDensity, hockeyStick_reindex]
  exact GeneralContraction.hockey_output_le E γ ρ σ

omit [DecidableEq A] [Fintype S] [DecidableEq S] in
theorem partialTrace_adjoint [DecidableEq A] [Fintype S] [DecidableEq S] (X : Matrix (S × A) (S × A) ℂ) :
    partialTraceMatrix Xᴴ = (partialTraceMatrix X)ᴴ := by
  ext i j
  simp only [partialTraceMatrix, Matrix.conjTranspose_apply, star_sum]

omit [DecidableEq A] [Fintype S] [DecidableEq S] in
theorem partialTrace_assoc_pairBlocks [DecidableEq A] [Fintype S] [DecidableEq S] (P Q R T : Matrix (S × A) (S × A) ℂ) :
    partialTraceMatrix ((pairBlocks P Q R T).submatrix
      (Equiv.prodAssoc Bool S A) (Equiv.prodAssoc Bool S A)) =
      pairBlocks (partialTraceMatrix P) (partialTraceMatrix Q)
        (partialTraceMatrix R) (partialTraceMatrix T) := by
  ext ⟨r,s⟩ ⟨t,u⟩
  cases r <;> cases t <;> rfl

theorem encoded_phaseOuter_partialTrace (E : QuantumChannel Q (S × A)) (s t : ℝ) :
    partialTraceMatrix ((amplify E.map (phaseOuter s t)).submatrix
      (Equiv.prodAssoc Bool S A) (Equiv.prodAssoc Bool S A)) =
      pairBlocks ((s^2) • partialTraceMatrix (E.map (matrixUnit 0 0)))
        ((s*t) • partialTraceMatrix (E.map (matrixUnit 0 1)))
        ((s*t) • partialTraceMatrix (E.map (matrixUnit 1 0)))
        ((t^2) • partialTraceMatrix (E.map (matrixUnit 1 1))) := by
  rw [phaseOuter_blocks, amplify_pairBlocks, partialTrace_assoc_pairBlocks]
  simp only [LinearMap.map_smul_of_tower, partialTraceMatrix_smul]

theorem encoded_phase_sameReference (E : QuantumChannel Q (S × A))
    (hcross : partialTraceMatrix (E.map (matrixUnit 0 1)) = 0) (u : ℝ) :
    partialTraceMatrix (encodedDensity E (phaseRho u)).mat =
      partialTraceMatrix (encodedDensity E (phaseSigma u)).mat := by
  have hcross' : partialTraceMatrix (E.map (matrixUnit 1 0)) = 0 := by
    rw [channel_offDiagonal_adjoint, partialTrace_adjoint, hcross,
      Matrix.conjTranspose_zero]
  change partialTraceMatrix ((amplify E.map ((1/(1+u^2) : ℝ) • phaseOuter u 1)).submatrix
      (Equiv.prodAssoc Bool S A) (Equiv.prodAssoc Bool S A)) =
    partialTraceMatrix ((amplify E.map ((1/(1+u^2) : ℝ) • phaseOuter u (-1))).submatrix
      (Equiv.prodAssoc Bool S A) (Equiv.prodAssoc Bool S A))
  rw [amplify_real_smul, amplify_real_smul]
  change partialTraceMatrix ((1/(1+u^2) : ℝ) •
      (amplify E.map (phaseOuter u 1)).submatrix
        (Equiv.prodAssoc Bool S A) (Equiv.prodAssoc Bool S A)) =
    partialTraceMatrix ((1/(1+u^2) : ℝ) •
      (amplify E.map (phaseOuter u (-1))).submatrix
        (Equiv.prodAssoc Bool S A) (Equiv.prodAssoc Bool S A))
  rw [partialTraceMatrix_smul, partialTraceMatrix_smul,
    encoded_phaseOuter_partialTrace, encoded_phaseOuter_partialTrace, hcross, hcross']
  norm_num

theorem encoded_output (N : QuantumChannel A B) (E : QuantumChannel Q (S × A))
    (M : QuantumChannel Q (S × B))
    (hM : ∀ X, M.map X = amplify N.map (E.map X)) (ρ : Density (R × Q)) :
    N.outputDensity (encodedDensity E ρ) =
      reindexDensity (M.outputDensity ρ) (Equiv.prodAssoc R S B) := by
  apply density_ext
  ext ⟨⟨r,s⟩,b⟩ ⟨⟨t,u⟩,c⟩
  let Xrt : Matrix Q Q ℂ := fun i j => ρ.mat (r,i) (t,j)
  exact (congrArg (fun Y : Matrix (S × B) (S × B) ℂ => Y (s,b) (u,c))
    (hM Xrt)).symm

theorem encoded_output_hockey (N : QuantumChannel A B) (E : QuantumChannel Q (S × A))
    (M : QuantumChannel Q (S × B))
    (hM : ∀ X, M.map X = amplify N.map (E.map X)) (γ : ℝ)
    (ρ σ : Density (R × Q)) :
    hockeyStick γ (N.outputDensity (encodedDensity E ρ))
      (N.outputDensity (encodedDensity E σ)) =
      hockeyStick γ (M.outputDensity ρ) (M.outputDensity σ) := by
  rw [encoded_output N E M hM ρ, encoded_output N E M hM σ, hockeyStick_reindex]

def encodedReference (S : Type) [Fintype S] [DecidableEq S] : FiniteReference :=
  ⟨Bool × S, inferInstance, inferInstance⟩

theorem phase_ratio_certificate (N : QuantumChannel A B) (E : QuantumChannel Q (S × A))
    (M : QuantumChannel Q (S × B)) (D : Matrix (S × B) (S × B) ℂ)
    (hM : ∀ X, M.map X = amplify N.map (E.map X))
    (href : partialTraceMatrix (E.map (matrixUnit 0 1)) = 0)
    (hquad : D * M.map (matrixUnit 1 1) * Dᴴ = M.map (matrixUnit 0 0))
    (hcross : M.map (matrixUnit 0 1) = D * M.map (matrixUnit 1 1))
    (γ u : ℝ) (hγ : 1 < γ) (hu : 0 < u) :
    ∃ r ∈ GeneralContraction.completeRatioSet N γ,
      1/(1+((((γ+1)/(γ-1))*u)^2)*graphBound D) ≤ r := by
  let ρ := encodedDensity E (phaseRho u)
  let σ := encodedDensity E (phaseSigma u)
  let H := 1+((((γ+1)/(γ-1))*u)^2)*graphBound D
  have hH : 0 < H := by
    dsimp [H]
    have h := mul_nonneg (sq_nonneg (((γ+1)/(γ-1))*u)) (graphBound_pos D).le
    linarith
  have heq := encoded_output_hockey N E M hM γ (phaseRho u) (phaseSigma u)
  have hout : inputUpper γ u / H ≤ hockeyStick γ (N.outputDensity ρ) (N.outputDensity σ) := by
    rw [heq]
    exact phase_output_lower M D γ u hγ hquad hcross
  have hinpos : 0 < hockeyStick γ ρ σ :=
    (div_pos (inputUpper_pos γ u hγ hu) hH).trans_le
      (hout.trans (GeneralContraction.hockey_output_le N γ ρ σ))
  have hin : hockeyStick γ ρ σ ≤ inputUpper γ u :=
    (encoded_hockey_le E γ (phaseRho u) (phaseSigma u)).trans (phase_input_upper γ u hγ hu)
  let r := hockeyStick γ (N.outputDensity ρ) (N.outputDensity σ) / hockeyStick γ ρ σ
  refine ⟨r, ⟨encodedReference S,ρ,σ,encoded_phase_sameReference E href u,hinpos,rfl⟩, ?_⟩
  apply (le_div_iff₀ hinpos).mpr
  have hmul := mul_le_mul_of_nonneg_left hin
    (le_of_lt (div_pos (by norm_num : (0:ℝ)<1) hH))
  calc
    1/H * hockeyStick γ ρ σ ≤ 1/H * inputUpper γ u := hmul
    _ = inputUpper γ u / H := by ring
    _ ≤ hockeyStick γ (N.outputDensity ρ) (N.outputDensity σ) := hout

theorem completeCoefficient_eq_one (N : QuantumChannel A B) (E : QuantumChannel Q (S × A))
    (M : QuantumChannel Q (S × B)) (D : Matrix (S × B) (S × B) ℂ)
    (hM : ∀ X, M.map X = amplify N.map (E.map X))
    (href : partialTraceMatrix (E.map (matrixUnit 0 1)) = 0)
    (hquad : D * M.map (matrixUnit 1 1) * Dᴴ = M.map (matrixUnit 0 0))
    (hcross : M.map (matrixUnit 0 1) = D * M.map (matrixUnit 1 1))
    (γ : ℝ) (hγ : 1 < γ) : GeneralContraction.completeCoefficient N γ = 1 := by
  have hb := GeneralContraction.completeRatioSet_bddAbove N γ
  have hk0 := GeneralContraction.completeCoefficient_nonneg N γ
  have hk1 := GeneralContraction.completeCoefficient_le_one N γ
  apply le_antisymm hk1
  by_contra h
  have hk : GeneralContraction.completeCoefficient N γ < 1 := lt_of_not_ge h
  let c := (γ+1)/(γ-1)
  let K := graphBound D
  have hc : 0 < c := div_pos (by linarith) (by linarith)
  have hK : 0 < K := graphBound_pos D
  have hK1 : 1 ≤ K := graphBound_one_le D
  let δ := 1-GeneralContraction.completeCoefficient N γ
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
  obtain ⟨r,hr,hl⟩ := phase_ratio_certificate N E M D hM href hquad hcross γ u hγ hu
  have hlower : 1/(1+(c*u)^2*K) ≤ GeneralContraction.completeCoefficient N γ :=
    hl.trans (le_csSup hb hr)
  have hden : 0 < 1+(c*u)^2*K := by positivity
  have hm : GeneralContraction.completeCoefficient N γ * ((c*u)^2*K) ≤ (c*u)^2*K :=
    mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) hK.le) hk1
  have hstrict : GeneralContraction.completeCoefficient N γ < 1/(1+(c*u)^2*K) := by
    apply (lt_div_iff₀ hden).mpr
    dsimp [δ] at hsmall
    nlinarith
  linarith

end
end PhaseTransport
