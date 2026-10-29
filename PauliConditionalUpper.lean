module
public import PauliChannel
public import CoefficientConvexity
public import NegativeDepolarizingExact


@[expose] public section

/-! Matching arbitrary-reference upper bound for every Pauli channel. -/
open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey

namespace PauliConditionalUpper
noncomputable section
set_option maxHeartbeats 2000000
abbrev Q := Fin 2

theorem core_bound_identity (a b : ℝ) (hm : a+3*b ≠ 0) (hab : a+b ≠ 0) :
    (a+3*b) * (((b-a)/(a+3*b)) * (1+3*((b-a)/(a+3*b))) /
      (1-(b-a)/(a+3*b))) = a+3*b-8*a*b/(a+b) := by
  have hd : 1-(b-a)/(a+3*b) = 2*(a+b)/(a+3*b) := by
    apply (eq_div_iff hm).2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hm]
    ring
  rw [hd]
  field_simp [hm, hab]
  ring

/-- The two smallest weights may be placed at labels zero and three. No
ordering is required between the remaining two weights. -/
theorem coefficient_le_pairBound (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (h03 : w 0 ≤ w 3)
    (h31 : w 3 ≤ w 1) (h32 : w 3 ≤ w 2) :
    conditionalCoefficient (PauliChannel.channel w hw hsum) 1 ≤
      1-8*w 0*w 3/(w 0+w 3) := by
  let m := w 0+3*w 3
  have hw0 := hw 0
  have hw3 := hw 3
  have hweights : w 0+w 1+w 2+w 3 = 1 := by
    have hh := hsum
    norm_num [Fin.sum_univ_succ] at hh
    change w 0 + (w 1 + (w 2 + w 3)) = 1 at hh
    linarith
  by_cases hm : m = 0
  · have ha : w 0 = 0 := by dsimp [m] at hm; linarith
    have hb : w 3 = 0 := by dsimp [m] at hm; linarith
    simpa [ha,hb] using GeneralContraction.conditionalCoefficient_le_one
      (PauliChannel.channel w hw hsum) 1
  · have hmpos : 0 < m := by dsimp [m] at hm ⊢; positivity
    have hab : w 0+w 3 ≠ 0 := by intro h; dsimp [m] at hm; apply hm; linarith
    let s := (w 3-w 0)/m
    have hs : 0 ≤ s := div_nonneg (sub_nonneg.mpr h03) hmpos.le
    have hs3 : s ≤ 1/3 := by
      apply (div_le_iff₀ hmpos).mpr
      dsimp [m]
      linarith
    let Ns : Fin 3 → QuantumChannel Q Q :=
      ![NegativeDepolarizingChannel.channel s hs hs3, PauliChannel.single 1,
        PauliChannel.single 2]
    let p : Fin 3 → ℝ := ![m,w 1-w 3,w 2-w 3]
    have hp : ∀ i, 0 ≤ p i := by
      intro i
      fin_cases i <;> simp [p] <;> linarith
    have hpsum : ∑ i, p i = 1 := by
      norm_num [p,m,Fin.sum_univ_succ]
      linarith
    have hmap : ∀ X, (PauliChannel.channel w hw hsum).map X =
        ∑ i, p i • (Ns i).map X := by
      intro X
      simp only [p,Ns,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
        Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Fin.sum_univ_zero,add_zero,
        PauliChannel.channel_map]
      have hc := PauliChannel.core_identity (w 0) (w 3) hm X
      change m • (NegativeDepolarizingChannel.channel s hs hs3).map X =
        PauliChannel.linear ![w 0,w 3,w 3,w 3] X at hc
      rw [hc]
      simpa only [add_assoc] using PauliChannel.core_decomposition w X
    have hb := CoefficientConvexity.coefficient_mixture_le
      (PauliChannel.channel w hw hsum) Ns p hp hpsum hmap 1
    simp only [p,Ns,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
      Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Fin.sum_univ_zero,add_zero,
      NegativeDepolarizingExact.conditional_trace_eq] at hb
    have h1 := mul_le_mul_of_nonneg_left
      (GeneralContraction.conditionalCoefficient_le_one (PauliChannel.single 1) 1)
      (sub_nonneg.mpr h31)
    have h2 := mul_le_mul_of_nonneg_left
      (GeneralContraction.conditionalCoefficient_le_one (PauliChannel.single 2) 1)
      (sub_nonneg.mpr h32)
    have hc := core_bound_identity (w 0) (w 3) hm hab
    change m*(s*(1+3*s)/(1-s)) = m-8*w 0*w 3/(w 0+w 3) at hc
    rw [hc] at hb
    dsimp [m] at hb
    linarith

end
end PauliConditionalUpper
