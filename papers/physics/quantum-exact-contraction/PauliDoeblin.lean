import PauliChannel
import PositiveReplacerSDP

/-!
# Exact positive replacer coefficient of every Pauli channel

The usual value is four times the least Pauli weight.  This is a supporting
prior-work calculation, not an independent novelty claim.  The proof uses
actual Bell vectors and the actual finite Choi semidefinite program.
-/

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey

namespace PauliDoeblin
noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

abbrev Q := Fin 2

attribute [local simp] Prod.ext_iff

def bellKet (i : Fin 4) : Q × Q → ℂ := fun p => PauliChannel.pauli i p.2 p.1
def bellRaw (i : Fin 4) : Matrix (Q × Q) (Q × Q) ℂ := BellSupport.outer (bellKet i)

theorem bellRaw_positive (i : Fin 4) : (bellRaw i).PosSemidef :=
  BellSupport.outer_posSemidef _

theorem choi_formula (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    ChannelKraus.choiMatrix (PauliChannel.channel w hw hsum) =
      ∑ i, w i • bellRaw i := by
  ext ⟨a,b⟩ ⟨c,d⟩
  change PauliChannel.linear w (Matrix.stdBasisMatrix a c 1) b d = _
  rw [PauliChannel.map_entries]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [bellRaw, BellSupport.outer, bellKet, PauliChannel.pauli,
      ADSeparation.pauliX, ADSeparation.pauliZ, Matrix.stdBasisMatrix,
      Matrix.one_apply, Fin.sum_univ_succ, Complex.real_smul,
      Matrix.cons_val_two, Matrix.cons_val_three] <;>
    push_cast <;> ring

theorem bell_resolution :
    (∑ i : Fin 4, bellRaw i) = (2 : ℝ) • (1 : Matrix (Q × Q) (Q × Q) ℂ) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [bellRaw, BellSupport.outer, bellKet, PauliChannel.pauli,
      ADSeparation.pauliX, ADSeparation.pauliZ, Matrix.one_apply,
      Fin.sum_univ_succ, Complex.real_smul,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff]

theorem bell_outer_quad (i j : Fin 4) :
    star (bellKet i) ⬝ᵥ (bellRaw j *ᵥ bellKet i) =
      (if i = j then 4 else 0 : ℂ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [bellRaw, BellSupport.outer, bellKet, PauliChannel.pauli,
      ADSeparation.pauliX, ADSeparation.pauliZ, Matrix.mulVec, dotProduct,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem bell_replacer_quad (i : Fin 4) (P : Matrix Q Q ℂ) :
    star (bellKet i) ⬝ᵥ (((1 : Matrix Q Q ℂ) ⊗ₖ P) *ᵥ bellKet i) = P.trace := by
  fin_cases i <;>
    norm_num [bellKet, PauliChannel.pauli, ADSeparation.pauliX,
      ADSeparation.pauliZ, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Matrix.kroneckerMap_apply, Matrix.trace, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

theorem bell_choi_quad (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (i : Fin 4) :
    (star (bellKet i) ⬝ᵥ (ChannelKraus.choiMatrix
      (PauliChannel.channel w hw hsum) *ᵥ bellKet i)).re = 4 * w i := by
  rw [choi_formula]
  simp only [Fin.sum_univ_succ, Matrix.add_mulVec, Matrix.zero_mulVec,
    Matrix.smul_mulVec_assoc, dotProduct_add, dotProduct_zero, dotProduct_smul]
  fin_cases i <;>
    norm_num [bell_outer_quad, Complex.smul_re, smul_eq_mul, Fin.ext_iff] <;> ring
  all_goals rfl

/-- Every Hermitian or positive feasible replacer is bounded by every Pauli
weight. Positivity of the replacer itself is unnecessary for this inequality. -/
theorem replacer_domination_trace_le (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (i : Fin 4) (P : Matrix Q Q ℂ)
    (hJ : (ChannelKraus.choiMatrix (PauliChannel.channel w hw hsum) -
      (1 : Matrix Q Q ℂ) ⊗ₖ P).PosSemidef) :
    P.trace.re ≤ 4 * w i := by
  have h := hJ.re_dotProduct_nonneg (bellKet i)
  change 0 ≤ (star (bellKet i) ⬝ᵥ
    ((ChannelKraus.choiMatrix (PauliChannel.channel w hw hsum) -
      (1 : Matrix Q Q ℂ) ⊗ₖ P) *ᵥ bellKet i)).re at h
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
    bell_choi_quad, bell_replacer_quad] at h
  linarith

def optimalReplacer (w : Fin 4 → ℝ) (i : Fin 4) : Matrix Q Q ℂ :=
  (2 * w i) • 1

theorem optimalReplacer_trace (w : Fin 4 → ℝ) (i : Fin 4) :
    (optimalReplacer w i).trace.re = 4 * w i := by
  norm_num [optimalReplacer, Matrix.trace, Matrix.smul_apply,
    Complex.real_smul, Fin.sum_univ_succ]
  ring

theorem optimalReplacer_feasible (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (i : Fin 4) (hi : ∀ j, w i ≤ w j) :
    PositiveReplacerSDP.Feasible (PauliChannel.channel w hw hsum)
      (optimalReplacer w i) := by
  constructor
  · exact posSemidef_real_smul _ Matrix.PosSemidef.one (2 * w i)
      (mul_nonneg (by norm_num) (hw i))
  · have heq : ChannelKraus.choiMatrix (PauliChannel.channel w hw hsum) -
        (1 : Matrix Q Q ℂ) ⊗ₖ optimalReplacer w i =
        ∑ j, (w j - w i) • bellRaw j := by
      rw [choi_formula, optimalReplacer, Matrix.kronecker_smul,
        Matrix.one_kronecker_one]
      simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
        bell_resolution]
      module
    rw [heq]
    exact Finset.sum_induction _ _ (fun P Q hP hQ => hP.add hQ)
      Matrix.PosSemidef.zero (fun j _ => posSemidef_real_smul _
        (bellRaw_positive j) (w j - w i) (sub_nonneg.mpr (hi j)))

/-- Exact positive-Doeblin SDP value for every Pauli channel, with any selected
least-weight label. -/
theorem alphaPlus_channel (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (i : Fin 4) (hi : ∀ j, w i ≤ w j) :
    PositiveReplacerSDP.alphaPlus (PauliChannel.channel w hw hsum) = 4 * w i := by
  apply le_antisymm
  · apply csSup_le (PositiveReplacerSDP.weightSet_nonempty _)
    rintro x ⟨P,hP,rfl⟩
    exact replacer_domination_trace_le w hw hsum i P hP.2
  · apply le_csSup (PositiveReplacerSDP.weightSet_bddAbove _)
    exact ⟨optimalReplacer w i, optimalReplacer_feasible w hw hsum i hi,
      (optimalReplacer_trace w i).symm⟩

end
end PauliDoeblin
