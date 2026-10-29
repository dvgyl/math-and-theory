import NegativeDepolarizingChannel
import PositiveReplacerSDP

/-! Exact positive Doeblin coefficient of the negative qubit depolarizing family. -/

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey

namespace NegativeDepolarizingDoeblin
noncomputable section

abbrev Q := Fin 2
abbrev Ω : Q × Q → ℂ := ChannelKraus.omega

theorem choi_formula (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 1/3) :
    ChannelKraus.choiMatrix (NegativeDepolarizingChannel.channel s hs hs3) =
      ((1+s)/2 : ℝ) • (1 : Matrix (Q × Q) (Q × Q) ℂ) - s • BellSupport.outer Ω := by
  have htr (a c : Q) : (Matrix.stdBasisMatrix a c (1 : ℂ)).trace =
      if a = c then 1 else 0 := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    fin_cases a <;> fin_cases c <;>
      norm_num [Matrix.stdBasisMatrix]
  ext ⟨a,b⟩ ⟨c,d⟩
  change ((NegativeDepolarizingChannel.channel s hs hs3).map
    (Matrix.stdBasisMatrix a c 1)) b d = _
  rw [NegativeDepolarizingChannel.channel_map, htr]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  by_cases hac : a = c <;> by_cases hbd : b = d <;>
    by_cases hab : a = b <;> by_cases hcd : c = d <;>
    simp only [Matrix.stdBasisMatrix, Matrix.of_apply, Matrix.one_apply, BellSupport.outer, ChannelKraus.omega,
      Prod.mk.injEq, hac, hbd, hab, hcd, ite_true, ite_false, and_self, true_and,
      false_and, and_true, and_false, star_one, star_zero, mul_one, one_mul,
      mul_zero, zero_mul, sub_zero, zero_sub]

theorem omega_norm : star Ω ⬝ᵥ Ω = (2 : ℂ) := by
  norm_num [ChannelKraus.omega, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem omega_outer_trace : (BellSupport.outer Ω).trace.re = 2 := by
  norm_num [ChannelKraus.omega, BellSupport.outer, Matrix.trace,
    Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem omega_outer_quad : star Ω ⬝ᵥ (BellSupport.outer Ω *ᵥ Ω) = (4 : ℂ) := by
  norm_num [ChannelKraus.omega, BellSupport.outer, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem omega_replacer_quad (P : Matrix Q Q ℂ) :
    star Ω ⬝ᵥ (((1 : Matrix Q Q ℂ) ⊗ₖ P) *ᵥ Ω) = P.trace := by
  simp [ChannelKraus.omega, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.trace]

theorem omega_choi_quad (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 1/3) :
    (star Ω ⬝ᵥ (ChannelKraus.choiMatrix
      (NegativeDepolarizingChannel.channel s hs hs3) *ᵥ Ω)).re = 1-3*s := by
  rw [choi_formula]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, omega_norm, omega_outer_quad,
    Complex.sub_re, Complex.smul_re, smul_eq_mul]
  norm_num
  ring

def optimalReplacer (s : ℝ) : Matrix Q Q ℂ := ((1-3*s)/2 : ℝ) • 1

theorem optimalReplacer_trace (s : ℝ) : (optimalReplacer s).trace.re = 1-3*s := by
  simp [optimalReplacer, Matrix.trace, Fin.sum_univ_succ,
    Matrix.smul_apply, Complex.real_smul]
  ring

theorem optimalReplacer_feasible (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 1/3) :
    PositiveReplacerSDP.Feasible (NegativeDepolarizingChannel.channel s hs hs3)
      (optimalReplacer s) := by
  constructor
  · exact posSemidef_real_smul _ Matrix.PosSemidef.one ((1-3*s)/2) (by linarith)
  · have hdom := KrausSaturation.posSemidef_trace_domination
      (BellSupport.outer Ω) (BellSupport.outer_posSemidef Ω)
    rw [omega_outer_trace] at hdom
    have heq : ChannelKraus.choiMatrix (NegativeDepolarizingChannel.channel s hs hs3) -
        (1 : Matrix Q Q ℂ) ⊗ₖ optimalReplacer s =
      s • ((2 : ℝ) • (1 : Matrix (Q × Q) (Q × Q) ℂ) - BellSupport.outer Ω) := by
      rw [choi_formula, optimalReplacer, Matrix.kronecker_smul, Matrix.one_kronecker_one]
      module
    rw [heq]
    exact posSemidef_real_smul _ hdom s hs

theorem replacer_domination_trace_le (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 1/3)
    (P : Matrix Q Q ℂ)
    (hJ : (ChannelKraus.choiMatrix (NegativeDepolarizingChannel.channel s hs hs3) -
      (1 : Matrix Q Q ℂ) ⊗ₖ P).PosSemidef) :
    P.trace.re ≤ 1-3*s := by
  have h := hJ.re_dotProduct_nonneg Ω
  change 0 ≤ (star Ω ⬝ᵥ ((ChannelKraus.choiMatrix
    (NegativeDepolarizingChannel.channel s hs hs3) -
      (1 : Matrix Q Q ℂ) ⊗ₖ P) *ᵥ Ω)).re at h
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
    omega_choi_quad, omega_replacer_quad] at h
  linarith

theorem feasible_trace_le (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 1/3)
    (P : Matrix Q Q ℂ)
    (hP : PositiveReplacerSDP.Feasible (NegativeDepolarizingChannel.channel s hs hs3) P) :
    P.trace.re ≤ 1-3*s :=
  replacer_domination_trace_le s hs hs3 P hP.2

/-- Exact SDP value on the full completely-positive negative depolarizing range. -/
theorem alphaPlus_channel (s : ℝ) (hs : 0 ≤ s) (hs3 : s ≤ 1/3) :
    PositiveReplacerSDP.alphaPlus (NegativeDepolarizingChannel.channel s hs hs3) = 1-3*s := by
  apply le_antisymm
  · apply csSup_le (PositiveReplacerSDP.weightSet_nonempty _)
    rintro x ⟨P,hP,rfl⟩
    exact feasible_trace_le s hs hs3 P hP
  · apply le_csSup (PositiveReplacerSDP.weightSet_bddAbove _)
    exact ⟨optimalReplacer s,optimalReplacer_feasible s hs hs3,
      (optimalReplacer_trace s).symm⟩

theorem universal_not_alphaPlus_zero :
    PositiveReplacerSDP.alphaPlus
      (NegativeDepolarizingChannel.channel (1/3) (by norm_num) (by norm_num)) = 0 := by
  rw [alphaPlus_channel]
  norm_num

end
end NegativeDepolarizingDoeblin
