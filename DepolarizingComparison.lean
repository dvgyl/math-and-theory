module
public import DepolarizingClosedBounds


@[expose] public section

/-! Supporting exact Doeblin and equal-reference trace values for the actual
all-dimensional negative depolarizing channel. These standard supporting
calculations are not independent novelty claims. -/

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey GeneralContraction

namespace DepolarizingComparison
noncomputable section

variable {A R : Type} [Fintype A] [DecidableEq A]
  [Fintype R] [DecidableEq R]

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

theorem choi_formula [Nonempty A] (s : ℝ) (hs : 0≤s)
    (hb : ((Fintype.card A : ℝ)^2-1)*s≤1) :
    ChannelKraus.choiMatrix (DepolarizingChannel.channel s hs hb) =
      ((1+s)/(Fintype.card A : ℝ)) • (1 : Matrix (A×A) (A×A) ℂ) -
        s • BellSupport.outer (ChannelKraus.omega (A:=A)) := by
  have htr (a c : A) : (Matrix.stdBasisMatrix a c (1 : ℂ)).trace =
      if a=c then 1 else 0 := by
    by_cases hac : a=c
    · subst c
      simp [Matrix.trace, Matrix.stdBasisMatrix]
    · simp only [if_neg hac, Matrix.trace]
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬(a=i ∧ c=i) := by
        rintro ⟨ha,hc⟩
        exact hac (ha.trans hc.symm)
      simp [Matrix.diag, Matrix.stdBasisMatrix,hn]
  ext ⟨a,b⟩ ⟨c,d⟩
  change ((DepolarizingChannel.channel s hs hb).map
    (Matrix.stdBasisMatrix a c 1)) b d = _
  rw [DepolarizingChannel.channel_map, htr]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  by_cases hac : a=c <;> by_cases hbd : b=d <;>
    by_cases hab : a=b <;> by_cases hcd : c=d <;>
    simp only [Matrix.stdBasisMatrix, Matrix.of_apply, Matrix.one_apply,
      BellSupport.outer, ChannelKraus.omega, Prod.mk.injEq,
      hac,hbd,hab,hcd,ite_true,ite_false,and_self,true_and,false_and,
      and_true,and_false,star_one,star_zero,mul_one,one_mul,
      mul_zero,zero_mul,sub_zero,zero_sub]

theorem omega_norm :
    star (ChannelKraus.omega (A:=A)) ⬝ᵥ ChannelKraus.omega =
      (Fintype.card A : ℂ) := by
  simp [ChannelKraus.omega, dotProduct, Fintype.sum_prod_type]

theorem omega_outer_quad :
    star (ChannelKraus.omega (A:=A)) ⬝ᵥ
      (BellSupport.outer ChannelKraus.omega *ᵥ ChannelKraus.omega) =
      (Fintype.card A : ℂ)^2 := by
  simp [ChannelKraus.omega, BellSupport.outer, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, pow_two]

theorem omega_replacer_quad (P : Matrix A A ℂ) :
    star (ChannelKraus.omega (A:=A)) ⬝ᵥ
      (((1 : Matrix A A ℂ) ⊗ₖ P) *ᵥ ChannelKraus.omega) = P.trace := by
  simp [ChannelKraus.omega, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.trace]

theorem omega_choi_quad [Nonempty A] (s : ℝ) (hs : 0≤s)
    (hb : ((Fintype.card A : ℝ)^2-1)*s≤1) :
    (star (ChannelKraus.omega (A:=A)) ⬝ᵥ
      (ChannelKraus.choiMatrix (DepolarizingChannel.channel s hs hb) *ᵥ
        ChannelKraus.omega)).re = 1-((Fintype.card A : ℝ)^2-1)*s := by
  have hd := (DepolarizingChannel.cardReal_pos (A:=A)).ne'
  rw [choi_formula]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, omega_norm, omega_outer_quad,
    Complex.sub_re, Complex.smul_re, smul_eq_mul]
  norm_num [pow_two, Complex.mul_re]
  ring

def optimalReplacer (s : ℝ) : Matrix A A ℂ :=
  ((1-((Fintype.card A : ℝ)^2-1)*s)/(Fintype.card A : ℝ)) • 1

theorem optimalReplacer_trace [Nonempty A] (s : ℝ) :
    (optimalReplacer (A:=A) s).trace.re = 1-((Fintype.card A : ℝ)^2-1)*s := by
  have hd := (DepolarizingChannel.cardReal_pos (A:=A)).ne'
  simp only [optimalReplacer, Matrix.trace_smul, Matrix.trace_one,
    Complex.smul_re, smul_eq_mul]
  norm_num

theorem optimalReplacer_feasible [Nonempty A] (s : ℝ) (hs : 0≤s)
    (hb : ((Fintype.card A : ℝ)^2-1)*s≤1) :
    PositiveReplacerSDP.Feasible (DepolarizingChannel.channel s hs hb)
      (optimalReplacer (A:=A) s) := by
  have hd := DepolarizingChannel.cardReal_pos (A:=A)
  constructor
  · exact posSemidef_real_smul _ Matrix.PosSemidef.one _
      (div_nonneg (sub_nonneg.mpr hb) hd.le)
  · have hc : (1+s)/(Fintype.card A : ℝ) =
        (1-((Fintype.card A : ℝ)^2-1)*s)/(Fintype.card A : ℝ) +
          s*(Fintype.card A : ℝ) := by
      field_simp
      ring
    have heq : ChannelKraus.choiMatrix (DepolarizingChannel.channel s hs hb) -
        (1 : Matrix A A ℂ) ⊗ₖ optimalReplacer s =
        s • ((Fintype.card A : ℝ) • (1 : Matrix (A×A) (A×A) ℂ) -
          BellSupport.outer (ChannelKraus.omega (A:=A))) := by
      rw [choi_formula, optimalReplacer, Matrix.kronecker_smul,
        Matrix.one_kronecker_one, hc]
      module
    rw [heq]
    exact posSemidef_real_smul _ DepolarizingReduction.reduction_gram_positive s hs

theorem replacer_domination_trace_le [Nonempty A] (s : ℝ) (hs : 0≤s)
    (hb : ((Fintype.card A : ℝ)^2-1)*s≤1) (P : Matrix A A ℂ)
    (hJ : (ChannelKraus.choiMatrix (DepolarizingChannel.channel s hs hb) -
      (1 : Matrix A A ℂ) ⊗ₖ P).PosSemidef) :
    P.trace.re ≤ 1-((Fintype.card A : ℝ)^2-1)*s := by
  have h := hJ.re_dotProduct_nonneg (ChannelKraus.omega (A:=A))
  change 0 ≤ (star (ChannelKraus.omega (A:=A)) ⬝ᵥ
    ((ChannelKraus.choiMatrix (DepolarizingChannel.channel s hs hb) -
      (1 : Matrix A A ℂ) ⊗ₖ P) *ᵥ ChannelKraus.omega)).re at h
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
    omega_choi_quad, omega_replacer_quad] at h
  linarith

theorem alphaPlus_channel [Nonempty A] (s : ℝ) (hs : 0≤s)
    (hb : ((Fintype.card A : ℝ)^2-1)*s≤1) :
    PositiveReplacerSDP.alphaPlus (DepolarizingChannel.channel s hs hb) =
      1-((Fintype.card A : ℝ)^2-1)*s := by
  apply le_antisymm
  · apply csSup_le (PositiveReplacerSDP.weightSet_nonempty _)
    rintro x ⟨P,hP,rfl⟩
    exact replacer_domination_trace_le s hs hb P hP.2
  · apply le_csSup (PositiveReplacerSDP.weightSet_bddAbove _)
    exact ⟨optimalReplacer s,optimalReplacer_feasible s hs hb,
      (optimalReplacer_trace s).symm⟩

theorem equal_reference_hockey (N : QuantumChannel A A) (s : ℝ) (hs : 0≤s)
    (hN : ∀ X, N.map X = ((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1:Matrix A A ℂ))-s • X)
    (ρ σ : Density (R×A))
    (href : partialTraceMatrix ρ.mat = partialTraceMatrix σ.mat) :
    hockeyStick 1 (N.outputDensity ρ) (N.outputDensity σ) = s*hockeyStick 1 ρ σ := by
  have hx : (ρ.mat-σ.mat).IsHermitian := ρ.positive.1.sub σ.positive.1
  have ho : (N.outputDensity ρ).mat-(N.outputDensity σ).mat = -(s • (ρ.mat-σ.mat)) := by
    change amplify N.map ρ.mat-amplify N.map σ.mat = _
    rw [← amplify_sub, DepolarizingBounds.amplified_formula_of_map N s hN,
      partialTraceMatrix_sub, href, sub_self]
    simp [NegativeDepolarizingBounds.referenceLift]
  have ht := traceNorm_neg (s • (ρ.mat-σ.mat)) (hermitian_real_smul _ hx s)
  rw [traceNorm_real_smul _ hx s hs] at ht
  have ht' : traceNorm ((N.outputDensity ρ).mat-(N.outputDensity σ).mat)
      ((N.outputDensity ρ).positive.1.sub (N.outputDensity σ).positive.1) =
      s * traceNorm (ρ.mat-σ.mat) hx := by
    simpa only [← ho] using ht
  rw [hockeyStick_one_eq_traceDistance, hockeyStick_one_eq_traceDistance, ht']
  ring

theorem exists_distinct_reference_pair (hdim : 2 ≤ Fintype.card A) :
    ∃ ρ σ : Density (Unit×A),
      partialTraceMatrix ρ.mat = partialTraceMatrix σ.mat ∧ 0 < hockeyStick 1 ρ σ := by
  letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,b,hab⟩ := exists_pair_ne A
  let ρ := basisDensity ((),a)
  let σ := basisDensity ((),b)
  have href : partialTraceMatrix ρ.mat = partialTraceMatrix σ.mat := by
    ext r t
    cases r
    cases t
    simp [ρ,σ,basisDensity,partialTraceMatrix,Prod.ext_iff]
  have hne : ρ.mat-σ.mat ≠ 0 := by
    intro h
    have he := congrArg (fun X : Matrix (Unit×A) (Unit×A) ℂ => X ((),a) ((),a)) h
    simp [ρ,σ,basisDensity,hab] at he
  have hn := (traceNorm_eq_zero_iff (ρ.mat-σ.mat) (ρ.positive.1.sub σ.positive.1)).not.mpr hne
  have hp : 0 < traceNorm (ρ.mat-σ.mat) (ρ.positive.1.sub σ.positive.1) :=
    lt_of_le_of_ne (traceNorm_nonneg _ _) (Ne.symm hn)
  refine ⟨ρ,σ,href,?_⟩
  rw [hockeyStick_one_eq_traceDistance]
  exact div_pos hp (by norm_num)

theorem complete_trace_eq (N : QuantumChannel A A) (hdim : 2 ≤ Fintype.card A)
    (s : ℝ) (hs : 0≤s)
    (hN : ∀ X, N.map X = ((1+s)/(Fintype.card A : ℝ)) •
      (X.trace • (1:Matrix A A ℂ))-s • X) :
    completeCoefficient N 1 = s := by
  obtain ⟨ρ,σ,href,hpos⟩ := exists_distinct_reference_pair (A:=A) hdim
  have hm : s ∈ completeRatioSet N 1 := by
    refine ⟨⟨Unit,inferInstance,inferInstance⟩,ρ,σ,href,hpos,?_⟩
    rw [equal_reference_hockey N s hs hN ρ σ href]
    exact (mul_div_cancel_right₀ s hpos.ne').symm
  apply le_antisymm
  · apply csSup_le ⟨s,hm⟩
    rintro r ⟨R,ρ,σ,href,hpos,rfl⟩
    rw [equal_reference_hockey N s hs hN ρ σ href]
    exact le_of_eq (mul_div_cancel_right₀ s hpos.ne')
  · exact le_csSup (completeRatioSet_bddAbove N 1) hm

theorem channel_complete_trace_eq [Nonempty A] (hdim : 2 ≤ Fintype.card A)
    (s : ℝ) (hs : 0≤s) (hb : ((Fintype.card A : ℝ)^2-1)*s≤1) :
    completeCoefficient (DepolarizingChannel.channel s hs hb) 1 = s :=
  complete_trace_eq _ hdim s hs (DepolarizingChannel.channel_map s hs hb)

end
end DepolarizingComparison
