module
public import THGStrong.History
public import THGStrong.CutsFin

@[expose] public section

noncomputable section
open scoped BigOperators
open Finset

namespace THGStrong

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

lemma ordered_history_mixed_formula (u s v t : ι → ℝ) (μ h : ℝ)
    (i j : ι) (hij : i < j) :
    historyCoefficient (orderedWeight u s v t) orderMask μ h i j +
      historyCoefficient (orderedWeight u s v t) orderMask μ h j i =
      u i*v j+s i*t j +
        h*(s i*cutAfter t j+μ*u i*cutAfter v j-
          cutPrefix u i*v j-μ*cutPrefix s i*t j) -
        μ*h^2*(cutPrefix u i*cutAfter v j+cutPrefix s i*cutAfter t j) := by
  have hq := orderedWeight_quadratic_cut u s v t i j hij.le
  have hq' : (∑ k, ∑ l, orderedWeight u s v t k l *
      (orderMask k j-orderMask l j)*(orderMask k i-orderMask l i)) =
      cutPrefix u i*cutAfter v j+cutPrefix s i*cutAfter t j := by
    rw [← hq]
    apply sum_congr rfl
    intro k hk
    apply sum_congr rfl
    intro l hl
    ring
  simp only [historyCoefficient]
  rw [orderedWeight_linear_after u s v t μ i j hij.le,
    orderedWeight_linear_before u s v t μ i j hij, hq, hq']
  simp only [orderedWeight, if_pos hij, if_neg (not_lt_of_ge hij.le)]
  ring

lemma ordered_history_diagonal_formula (u s v t : ι → ℝ) (μ h : ℝ) (i : ι) :
    2*historyCoefficient (orderedWeight u s v t) orderMask μ h i i -
      (∑ j, (orderedWeight u s v t i j+orderedWeight u s v t j i)) =
      2*h*(s i*cutAfter t i+μ*u i*cutAfter v i) -
        μ*h^2*(cutPrefix u i*cutAfter v i+cutPrefix s i*cutAfter t i) -
        (u i*cutAfter v i+t i*cutBefore s i+
          v i*cutBefore u i+s i*cutAfter t i) := by
  simp only [historyCoefficient]
  rw [orderedWeight_self, orderedWeight_linear_after u s v t μ i i le_rfl,
    orderedWeight_quadratic_cut u s v t i i le_rfl, orderedWeight_sum_both]
  ring

def historyWeight (N : ℕ) (U B V D : ℕ → ℝ) : Fin (N+1) → Fin (N+1) → ℝ :=
  orderedWeight (fun i => U (i.val+1)-U i.val) (fun i => B (i.val+1)-B i.val)
    (fun j => V j.val-V (j.val+1)) (fun j => D j.val-D (j.val+1))

lemma historyWeight_divergence (N : ℕ) (U B V D : ℕ → ℝ)
    (hU0 : U 0 = 0) (hB0 : B 0 = 0) (hV : V (N+1) = 0) (hD : D (N+1) = 0)
    (i : Fin (N+1)) :
    (∑ j, (historyWeight N U B V D i j-historyWeight N U B V D j i)) =
      (U (i.val+1)*V (i.val+1)-B (i.val+1)*D (i.val+1)) -
        (U i.val*V i.val-B i.val*D i.val) := by
  unfold historyWeight
  rw [orderedWeight_divergence]
  simp only [cutBefore_forward_difference, cutAfter_backward_difference,
    hU0, hB0, hV, hD, sub_zero]
  ring

lemma historyWeight_mixed_zero (N : ℕ) (U B V D : ℕ → ℝ) (μ h a : ℝ)
    (ha : a = 1-μ*h)
    (hU0 : U 0 = 0) (hB0 : B 0 = 0) (hV : V (N+1) = 0) (hD : D (N+1) = 0)
    (hforward : ∀ i < N, a*B (i+1)-B i = (h-1)*U (i+1)+U i)
    (htail : ∀ j, 0 < j → j ≤ N → V j-a*V (j+1) = D j+(h-1)*D (j+1)) :
    ∀ i j : Fin (N+1), i ≠ j →
      historyCoefficient (historyWeight N U B V D) orderMask μ h i j +
        historyCoefficient (historyWeight N U B V D) orderMask μ h j i = 0 := by
  have hless (i j : Fin (N+1)) (hij : i < j) :
      historyCoefficient (historyWeight N U B V D) orderMask μ h i j +
        historyCoefficient (historyWeight N U B V D) orderMask μ h j i = 0 := by
    have hij' : i.val < j.val := hij
    have hiN : i.val < N := by have := j.isLt; omega
    have hj0 : 0 < j.val := by omega
    have hjN : j.val ≤ N := Nat.le_of_lt_succ j.isLt
    unfold historyWeight
    rw [ordered_history_mixed_formula _ _ _ _ μ h i j hij]
    simp only [cutPrefix_forward_difference, cutAfter_backward_difference,
      hU0, hB0, hV, hD, sub_zero]
    exact mixed_coefficient_algebra (U (i.val+1)) (U i.val)
      (B (i.val+1)) (B i.val) (V j.val) (V (j.val+1)) (D j.val) (D (j.val+1))
      μ h a ha (hforward i.val hiN) (htail j.val hj0 hjN)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hless i j h
  · simpa only [add_comm] using hless j i h

lemma historyWeight_diagonal_interior (N : ℕ) (U B V D : ℕ → ℝ) (μ h a : ℝ)
    (ha : a = 1-μ*h)
    (hU0 : U 0 = 0) (hB0 : B 0 = 0) (hV : V (N+1) = 0) (hD : D (N+1) = 0)
    (i : Fin (N+1))
    (hforward : a*B (i.val+1)-B i.val = (h-1)*U (i.val+1)+U i.val)
    (htail : U i.val*(V i.val-a*V (i.val+1)-D i.val-(h-1)*D (i.val+1)) = 0)
    (hwronskian : 2*((h-1)^2*U (i.val+1)*D (i.val+1)-U i.val*D i.val) = 1-(h-1)^2)
    (hprogress : a*(U (i.val+1)*V (i.val+1)-B (i.val+1)*D (i.val+1))-
      (U i.val*V i.val-B i.val*D i.val) = h) :
    2*historyCoefficient (historyWeight N U B V D) orderMask μ h i i -
      (∑ j, (historyWeight N U B V D i j+historyWeight N U B V D j i)) =
      -(h-1)*(∑ j, (historyWeight N U B V D i j-historyWeight N U B V D j i)) := by
  unfold historyWeight
  rw [ordered_history_diagonal_formula, orderedWeight_divergence]
  simp only [cutPrefix_forward_difference, cutBefore_forward_difference,
    cutAfter_backward_difference, hU0, hB0, hV, hD, sub_zero]
  exact diagonal_coefficient_zero_weighted (U (i.val+1)) (U i.val)
    (B (i.val+1)) (B i.val) (V i.val) (V (i.val+1)) (D i.val) (D (i.val+1))
    μ h a ha hforward htail hwronskian hprogress

lemma historyWeight_diagonal_terminal (N : ℕ) (U B V D : ℕ → ℝ) (μ h S : ℝ)
    (hU0 : U 0 = 0) (hB0 : B 0 = 0) (hV : V (N+1) = 0) (hD : D (N+1) = 0)
    (hcut : U N*V N-B N*D N = S) (hproduct : B N*D N = S^2/2) :
    2*historyCoefficient (historyWeight N U B V D) orderMask μ h (Fin.last N) (Fin.last N) -
      (∑ j, (historyWeight N U B V D (Fin.last N) j+
        historyWeight N U B V D j (Fin.last N))) = -S*(S+1) := by
  unfold historyWeight
  rw [ordered_history_diagonal_formula]
  simp only [cutPrefix_forward_difference, cutBefore_forward_difference,
    cutAfter_backward_difference, Fin.val_last, hU0, hB0, hV, hD,
    sub_zero, zero_sub, mul_zero, zero_mul, add_zero, sub_self]
  nlinarith only [hcut, hproduct]

#print axioms historyWeight_mixed_zero
#print axioms historyWeight_diagonal_interior
#print axioms historyWeight_diagonal_terminal

end THGStrong
