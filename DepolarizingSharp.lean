module
public import TightFrameWitness
public import BellEncoding
public import DepolarizingWitnessScalars


@[expose] public section

/-! Actual normalized quantum-state witnesses and the sharp coefficient lower
bound. The frame and Bell hypotheses are elementary identities on the supplied
matrices; the final concrete theorem supplies explicit Fourier constructions. -/

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey
open TightFrameGeometry TightFrameColumns TightFrameWitness
open Filter Topology

namespace DepolarizingSharp
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

variable {I A : Type} [Fintype I] [DecidableEq I]
  [Fintype A] [DecidableEq A] [Nonempty A]

structure BellFamily (I A : Type) [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] where
  mat : I → Matrix (A×A) (A×A) ℂ
  positive : ∀ i, (mat i).PosSemidef
  trace_one : ∀ i, (mat i).trace = 1
  orthogonal : ∀ i j, mat i * mat j = if i=j then mat i else 0
  resolution : ∑ i, mat i = 1
  marginal : ∀ i, partialTraceMatrix (mat i) = BellEncoding.mixedMarginal

omit [DecidableEq I] in
theorem size_ge_four [DecidableEq I] (hI : 4 ≤ Fintype.card I) : 4 ≤ size I := by
  unfold size
  exact_mod_cast hI

theorem radius_pos (hI : 4 ≤ Fintype.card I) : 0 < radius I := by
  have hn := size_pos (I:=I) (by omega : 2 ≤ Fintype.card I)
  have hn4 := size_ge_four hI
  unfold radius
  exact sub_pos.mpr ((div_lt_one hn).mpr (by linarith))

def normalizer (I : Type) [Fintype I] [DecidableEq I] (u : ℝ) : ℝ :=
  size I * (radius I + u^2)

theorem normalizer_pos (hI : 4 ≤ Fintype.card I) (u : ℝ) :
    0 < normalizer I u :=
  mul_pos (size_pos (by omega)) (add_pos_of_pos_of_nonneg (radius_pos hI) (sq_nonneg u))

omit [Nonempty A] in
theorem encoded_plus_trace [Nonempty A] (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (u : ℝ) :
    (BellEncoding.encode B.mat (plusRaw F u)).trace = ((normalizer I u : ℝ):ℂ) := by
  rw [BellEncoding.encode_trace B.mat _ B.trace_one]
  simp only [plusRaw_trace F (by omega), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [normalizer, size, Complex.ofReal_mul, Complex.ofReal_natCast]

omit [Nonempty A] in
theorem encoded_minus_trace [Nonempty A] (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (u : ℝ) :
    (BellEncoding.encode B.mat (minusRaw F u)).trace = ((normalizer I u : ℝ):ℂ) := by
  rw [BellEncoding.encode_trace B.mat _ B.trace_one]
  simp only [minusRaw_trace F (by omega), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [normalizer, size, Complex.ofReal_mul, Complex.ofReal_natCast]

def rho (F : Frame I) (hI : 4 ≤ Fintype.card I) (B : BellFamily I A) (u : ℝ) :
    Density ((Ref I × A) × A) where
  mat := (normalizer I u)⁻¹ • BellEncoding.encode B.mat (plusRaw F u)
  positive := posSemidef_real_smul _
    (BellEncoding.encode_positive B.mat _ B.positive (plusRaw_positive F u)) _
    (inv_nonneg.mpr (normalizer_pos hI u).le)
  normalized := by
    rw [Matrix.trace_smul, encoded_plus_trace F hI B u]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (normalizer_pos hI u).ne')

def sigma (F : Frame I) (hI : 4 ≤ Fintype.card I) (B : BellFamily I A) (u : ℝ) :
    Density ((Ref I × A) × A) where
  mat := (normalizer I u)⁻¹ • BellEncoding.encode B.mat (minusRaw F u)
  positive := posSemidef_real_smul _
    (BellEncoding.encode_positive B.mat _ B.positive (minusRaw_positive F u)) _
    (inv_nonneg.mpr (normalizer_pos hI u).le)
  normalized := by
    rw [Matrix.trace_smul, encoded_minus_trace F hI B u]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (normalizer_pos hI u).ne')

theorem state_difference (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (u : ℝ) :
    difference 1 (rho F hI B u) (sigma F hI B u) =
      (normalizer I u)⁻¹ • BellEncoding.encode B.mat (rawDifference F u) := by
  simp only [difference, rho, sigma, one_smul, ←smul_sub,
    ←BellEncoding.encode_sub]
  rfl

theorem raw_reference_norm (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (u : ℝ) :
    traceNorm (partialTraceMatrix (BellEncoding.encode B.mat (rawDifference F u)))
      (partialTraceMatrix_hermitian _ (BellEncoding.encode_hermitian B.mat _
        (fun i => (B.positive i).1) (rawDifference_hermitian F u))) =
      2*(size I-2) := by
  have h := BellEncoding.traceNorm_partialTrace_encode_mixed B.mat (rawDifference F u)
    (fun i => (B.positive i).1) (rawDifference_hermitian F u) B.marginal
  have h' : traceNorm
      (partialTraceMatrix (BellEncoding.encode B.mat (rawDifference F u)))
      (partialTraceMatrix_hermitian _ (BellEncoding.encode_hermitian B.mat _
        (fun i => (B.positive i).1) (rawDifference_hermitian F u))) =
      traceNorm (base F) (base_hermitian F) := by
    simpa only [rawDifference_sum F (by omega) u] using h
  exact h'.trans (base_traceNorm F (by omega))

theorem raw_input_gap (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (u : ℝ) :
    positiveTraceGap (BellEncoding.encode B.mat (rawDifference F u))
      (BellEncoding.encode_hermitian B.mat _
        (fun i => (B.positive i).1) (rawDifference_hermitian F u)) = size I*u^2 := by
  rw [positiveTraceGap_eq]
  unfold normGap
  rw [BellEncoding.traceNorm_encode B.mat (rawDifference F u) B.positive B.trace_one
    B.orthogonal B.resolution (rawDifference_hermitian F u),raw_reference_norm F hI B u]
  simp only [rawDifference_traceNorm F (by omega) u,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  have hr : size I*radius I=size I-2 :=
    DepolarizingWitnessScalars.radius_mass (size I) (size_pos (by omega)).ne'
  change (size I*(2*(radius I+u^2))-2*(size I-2))/2=size I*u^2
  nlinarith

theorem initialGap_factor (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (u : ℝ) :
    initialGap 1 (rho F hI B u) (sigma F hI B u) =
      (normalizer I u)⁻¹ * (size I*u^2) := by
  unfold initialGap
  simp only [state_difference]
  rw [positiveTraceGap_smul _
    (BellEncoding.encode_hermitian B.mat _
      (fun i => (B.positive i).1) (rawDifference_hermitian F u)) _
    (inv_nonneg.mpr (normalizer_pos hI u).le),raw_input_gap F hI B u]

theorem initialGap_exact (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (u : ℝ) :
    initialGap 1 (rho F hI B u) (sigma F hI B u) = u^2/(radius I+u^2) := by
  rw [initialGap_factor]
  have hn := (size_pos (I:=I) (by omega)).ne'
  have hr : radius I+u^2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (radius_pos hI) (sq_nonneg u)).ne'
  unfold normalizer
  field_simp

theorem initialGap_positive (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (u : ℝ) (hu : 0<u) :
    0 < initialGap 1 (rho F hI B u) (sigma F hI B u) := by
  rw [initialGap_exact]
  exact div_pos (sq_pos_of_pos hu)
    (add_pos_of_pos_of_nonneg (radius_pos hI) (sq_nonneg u))

omit [Nonempty A] in
theorem amplify_raw [Nonempty A] (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (hsize : size I=(Fintype.card A : ℝ)^2)
    (N : QuantumChannel A A) (s : ℝ)
    (hN : ∀ X, N.map X=((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1:Matrix A A ℂ))-s • X) (u : ℝ) :
    amplify N.map (BellEncoding.encode B.mat (rawDifference F u)) =
      BellEncoding.encode B.mat
        (outputMatrix F (DepolarizingWitnessScalars.b (size I) s) s u) := by
  rw [BellEncoding.amplify_encode_depolarizing N s hN B.mat _ B.resolution B.marginal]
  simp only [rawDifference_sum F (by omega) u,outputMatrix,
    DepolarizingWitnessScalars.b,hsize]
  rfl

theorem raw_final_gap_lower (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (hsize : size I=(Fintype.card A : ℝ)^2)
    (N : QuantumChannel A A) (s : ℝ)
    (hN : ∀ X, N.map X=((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1:Matrix A A ℂ))-s • X) (u t : ℝ) :
    size I * (DepolarizingWitnessScalars.a (size I) s *
      (TightFrameDual.cosine (radius I) t-1) +
      s*u^2*TightFrameDual.cosine (radius I) t +
      4*s*radius I*t*u/TightFrameDual.den (radius I) t) ≤
      positiveTraceGap (amplify N.map (BellEncoding.encode B.mat (rawDifference F u)))
        (N.amplify_hermitian _ (BellEncoding.encode_hermitian B.mat _
          (fun i => (B.positive i).1) (rawDifference_hermitian F u))) := by
  let b := DepolarizingWitnessScalars.b (size I) s
  let L := 2*b*(size I-2)+2*b*(TightFrameDual.cosine (radius I) t-1)-
    2*s*TightFrameDual.cosine (radius I) t*(radius I-u^2)+
    8*s*radius I*t*u/TightFrameDual.den (radius I) t
  have hn : size I*L ≤ ∑ i, traceNorm (outputMatrix F b s u i)
      (outputMatrix_hermitian F b s u i) := by
    have hh := Finset.sum_le_sum (fun (i : I) (_ : i ∈ Finset.univ) =>
      output_traceNorm_lower F (by omega) b s u t i)
    simpa only [size, L, Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh
  have hnorm : traceNorm (amplify N.map (BellEncoding.encode B.mat (rawDifference F u)))
      (N.amplify_hermitian _ (BellEncoding.encode_hermitian B.mat _
        (fun i => (B.positive i).1) (rawDifference_hermitian F u))) =
      ∑ i, traceNorm (outputMatrix F b s u i) (outputMatrix_hermitian F b s u i) := by
    have hh := BellEncoding.traceNorm_encode B.mat (outputMatrix F b s u)
      B.positive B.trace_one B.orthogonal B.resolution (outputMatrix_hermitian F b s u)
    simpa only [amplify_raw F hI B hsize N s hN u] using hh
  rw [positiveTraceGap_eq]
  unfold normGap
  simp only [N.partialTrace_amplify,raw_reference_norm F hI B u,hnorm]
  have hscale : size I*b=1+s := by
    dsimp [b,DepolarizingWitnessScalars.b]
    field_simp [(size_pos (I:=I) (by omega)).ne']
  have hr : size I*radius I=size I-2 :=
    DepolarizingWitnessScalars.radius_mass (size I) (size_pos (by omega)).ne'
  have halg : (size I*L-2*(size I-2))/2 =
      size I * (DepolarizingWitnessScalars.a (size I) s *
        (TightFrameDual.cosine (radius I) t-1) +
        s*u^2*TightFrameDual.cosine (radius I) t +
        4*s*radius I*t*u/TightFrameDual.den (radius I) t) := by
    dsimp [L]
    change _=size I*((b-s*radius I)*(TightFrameDual.cosine (radius I) t-1)+
      s*u^2*TightFrameDual.cosine (radius I) t+
      4*s*radius I*t*u/TightFrameDual.den (radius I) t)
    linear_combination (size I-2)*hscale-s*hr
  rw [←halg]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hn _) (by norm_num)

theorem finalGap_factor (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (N : QuantumChannel A A) (u : ℝ) :
    finalGap N 1 (rho F hI B u) (sigma F hI B u) =
      (normalizer I u)⁻¹ *
        positiveTraceGap (amplify N.map (BellEncoding.encode B.mat (rawDifference F u)))
          (N.amplify_hermitian _ (BellEncoding.encode_hermitian B.mat _
            (fun i => (B.positive i).1) (rawDifference_hermitian F u))) := by
  unfold finalGap
  simp only [state_difference,amplify_real_smul]
  exact positiveTraceGap_smul _ _ _ (inv_nonneg.mpr (normalizer_pos hI u).le)

theorem rationalBound_le_ratio (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (hsize : size I=(Fintype.card A : ℝ)^2)
    (N : QuantumChannel A A) (s : ℝ) (hs : 0≤s) (hb : (size I-1)*s≤1)
    (hN : ∀ X, N.map X=((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1:Matrix A A ℂ))-s • X) (u : ℝ) (hu : 0<u) :
    DepolarizingWitnessScalars.rationalBound (size I) s u ≤
      finalGap N 1 (rho F hI B u) (sigma F hI B u) /
        initialGap 1 (rho F hI B u) (sigma F hI B u) := by
  have h := raw_final_gap_lower F hI B hsize N s hN u
    (DepolarizingWitnessScalars.slope (size I) s*u)
  have hid := DepolarizingWitnessScalars.rational_lower_identity (size I) s u
    (size_ge_four hI)
    (DepolarizingWitnessScalars.a_pos (size I) s (size_ge_four hI) hs hb).ne'
  change DepolarizingWitnessScalars.a (size I) s *
      (TightFrameDual.cosine (radius I) (DepolarizingWitnessScalars.slope (size I) s*u)-1) +
      s*u^2*TightFrameDual.cosine (radius I) (DepolarizingWitnessScalars.slope (size I) s*u) +
      4*s*radius I*(DepolarizingWitnessScalars.slope (size I) s*u)*u/
        TightFrameDual.den (radius I) (DepolarizingWitnessScalars.slope (size I) s*u) =
      u^2*DepolarizingWitnessScalars.rationalBound (size I) s u at hid
  rw [hid] at h
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (normalizer_pos hI u).le)
  apply (le_div_iff₀ (initialGap_positive F hI B u hu)).mpr
  rw [initialGap_factor,finalGap_factor]
  convert hm using 1
  all_goals ring

theorem rationalBound_le_coefficient (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (hsize : size I=(Fintype.card A : ℝ)^2)
    (N : QuantumChannel A A) (s : ℝ) (hs : 0≤s) (hb : (size I-1)*s≤1)
    (hN : ∀ X, N.map X=((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1:Matrix A A ℂ))-s • X) (u : ℝ) (hu : 0<u) :
    DepolarizingWitnessScalars.rationalBound (size I) s u ≤ conditionalCoefficient N 1 := by
  have hr : finalGap N 1 (rho F hI B u) (sigma F hI B u) /
      initialGap 1 (rho F hI B u) (sigma F hI B u) ∈ conditionalRatioSet N 1 := by
    refine ⟨⟨Ref I×A,inferInstance,inferInstance⟩,rho F hI B u,sigma F hI B u,
      initialGap_positive F hI B u hu,rfl⟩
  exact (rationalBound_le_ratio F hI B hsize N s hs hb hN u hu).trans
    (le_csSup (conditionalRatioSet_bddAbove N 1) hr)

/-- The bound is attained as a supremum of actual finite-reference normalized
state-pair ratios, for every supplied genuine frame and Bell family. -/
theorem sharpBound_le_conditionalCoefficient (F : Frame I) (hI : 4 ≤ Fintype.card I)
    (B : BellFamily I A) (hsize : size I=(Fintype.card A : ℝ)^2)
    (N : QuantumChannel A A) (s : ℝ) (hs : 0≤s) (hb : (size I-1)*s≤1)
    (hN : ∀ X, N.map X=((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1:Matrix A A ℂ))-s • X) :
    DepolarizingEffects.sharpBound (size I) s ≤ conditionalCoefficient N 1 := by
  apply le_of_tendsto (DepolarizingWitnessScalars.rationalBound_limit (size I) s (size_ge_four hI))
  apply Filter.Eventually.of_forall
  intro k
  exact rationalBound_le_coefficient F hI B hsize N s hs hb hN _ (by positivity)

end
end DepolarizingSharp
