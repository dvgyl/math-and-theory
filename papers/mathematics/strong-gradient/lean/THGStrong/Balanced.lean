import THGStrong.Coefficients
import THGStrong.Scalars
import THGStrong.CertificateAPI

noncomputable section
open scoped BigOperators InnerProductSpace
open Finset

namespace THGStrong

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The explicit scalar factors give a nonnegative finite interpolation certificate.
All recurrence and coefficient hypotheses have been discharged here. -/
theorem balanced_history_bound : BalancedHistoryBound E := by
  intro N h a μ x g f hN hh1 hh2 hra ha hbal hstep hQ
  have hr : 0 < h-1 := by linarith
  have hr1 : h-1 < 1 := by linarith
  have hrel : h = (h-1)+1 := by ring
  have ha0 : 0 < a := lt_trans hr hra
  let U : ℕ → ℝ := upperFactor h a (h-1)
  let B : ℕ → ℝ := lowerFactor h a (h-1)
  let V : ℕ → ℝ := reverseFactor h a (h-1) N
  let D : ℕ → ℝ := tailFactor h a (h-1) N
  let w := historyWeight N U B V D
  have hU0 : U 0 = 0 := upperFactor_zero h a (h-1)
  have hB0 : B 0 = 0 := lowerFactor_zero h a (h-1)
  have hV : V (N+1) = 0 := reverseFactor_terminal h a (h-1) N
  have hD : D (N+1) = 0 := tailFactor_terminal h a (h-1) N
  have hforward (i : ℕ) (hi : i < N) :
      a*B (i+1)-B i = (h-1)*U (i+1)+U i :=
    forwardFactor_recurrence hrel hr hr1 hra hbal hi
  have htail (j : ℕ) (hj : 0 < j) (hjN : j ≤ N) :
      V j-a*V (j+1) = D j+(h-1)*D (j+1) :=
    tailFactor_recurrence hrel hr hr1 hra hbal hj hjN
  have hcut (j : ℕ) (hj : j ≤ N) :
      U j*V j-B j*D j = progressSum h a j := by
    by_cases hj0 : j = 0
    · subst j; simp only [hU0, hB0, zero_mul, sub_zero, progressSum_zero]
    · exact cut_product hrel hr hr1 hra hbal (Nat.pos_of_ne_zero hj0) hj
  have hprod (j : ℕ) (hj : j ≤ N) : U j*D j = halfPower (h-1) j := by
    by_cases hj0 : j = 0
    · subst j; simp [hU0, halfPower]
    · exact upper_tail_product hrel hr hr1 hra hbal (Nat.pos_of_ne_zero hj0) hj
  have hoff : ∀ i j : Fin (N+1), i ≠ j →
      historyCoefficient w (fun i j => if j < i then 1 else 0) μ h i j +
        historyCoefficient w (fun i j => if j < i then 1 else 0) μ h j i = 0 :=
    historyWeight_mixed_zero N U B V D μ h a ha hU0 hB0 hV hD hforward htail
  have hdiv (i : Fin (N+1)) : (∑ j, (w i j-w j i)) =
      if i.val < N then h*invPower a (i.val+1) else -progressSum h a N := by
    change (∑ j, (historyWeight N U B V D i j-historyWeight N U B V D j i)) = _
    rw [historyWeight_divergence N U B V D hU0 hB0 hV hD]
    by_cases hi : i.val < N
    · rw [if_pos hi, hcut (i.val+1) (by omega), hcut i.val (by omega),
        progressSum_increment]
    · have hiN : i.val = N := by have := i.isLt; omega
      rw [if_neg hi, hiN, hV, hD, mul_zero, mul_zero, sub_self, hcut N le_rfl]
      ring
  have hdiag (i : Fin (N+1)) :
      2*historyCoefficient w (fun i j => if j < i then 1 else 0) μ h i i -
      (∑ j, (w i j+w j i)) =
      if i.val < N then -(h-1)*(h*invPower a (i.val+1)) else
        -progressSum h a N*(progressSum h a N+1) := by
    by_cases hi : i.val < N
    · have htailweighted : U i.val*(V i.val-a*V (i.val+1)-D i.val-(h-1)*D (i.val+1)) = 0 := by
        by_cases hi0 : i.val = 0
        · simp only [hi0, hU0, zero_mul]
        · have ht := htail i.val (Nat.pos_of_ne_zero hi0) (le_of_lt hi)
          have ht0 : V i.val-a*V (i.val+1)-D i.val-(h-1)*D (i.val+1) = 0 := by
            linarith only [ht]
          rw [ht0, mul_zero]
      have hwron : 2*((h-1)^2*U (i.val+1)*D (i.val+1)-U i.val*D i.val) = 1-(h-1)^2 := by
        rw [mul_assoc, hprod (i.val+1) (by omega), hprod i.val (by omega)]
        have hp := halfPower_recurrence (ne_of_gt hr) i.val
        linarith only [hp]
      have hprogress : a*(U (i.val+1)*V (i.val+1)-B (i.val+1)*D (i.val+1))-
          (U i.val*V i.val-B i.val*D i.val) = h := by
        rw [hcut (i.val+1) (by omega), hcut i.val (by omega)]
        have hp := progressSum_recurrence (ne_of_gt ha0) h i.val
        linarith only [hp]
      have hc := historyWeight_diagonal_interior N U B V D μ h a ha hU0 hB0 hV hD i
        (hforward i.val hi) htailweighted hwron hprogress
      change 2*historyCoefficient w (fun i j => if j < i then 1 else 0) μ h i i -
        (∑ j, (w i j+w j i)) = -(h-1)*(∑ j, (w i j-w j i)) at hc
      rw [hdiv i, if_pos hi] at hc
      rw [if_pos hi]
      exact hc
    · have hiN : i = Fin.last N := by
        apply Fin.ext
        change i.val = N
        have := i.isLt
        omega
      subst i
      rw [if_neg hi]
      exact historyWeight_diagonal_terminal N U B V D μ h (progressSum h a N)
        hU0 hB0 hV hD (hcut N le_rfl)
        (terminal_lower_tail_product hrel hr hr1 hra hN hbal)
  have hUdiff (i : ℕ) (hi : i < N) : 0 ≤ U (i+1)-U i := by
    cases i with
    | zero => simp [U]
    | succ i =>
      exact sub_nonneg.mpr (le_of_lt (upperFactor_lt_succ hrel hr hr1 hra hbal hi))
  have hBdiff (i : ℕ) (hi : i < N) : 0 ≤ B (i+1)-B i :=
    sub_nonneg.mpr (le_of_lt (lowerFactor_lt_succ hrel hr hr1 hra hbal hi))
  have hVdiff (j : ℕ) (hj : 0 < j) (hjN : j ≤ N) : 0 ≤ V j-V (j+1) :=
    sub_nonneg.mpr (le_of_lt (reverseFactor_succ_lt hrel hr hr1 hra hbal hj hjN))
  have hDdiff (j : ℕ) (hj : 0 < j) (hjN : j ≤ N) : 0 ≤ D j-D (j+1) :=
    sub_nonneg.mpr (le_of_lt (tailFactor_succ_lt hrel hr hr1 hra hbal hj hjN))
  have hwpos (i j : Fin (N+1)) : 0 ≤ w i j := by
    change 0 ≤ orderedWeight _ _ _ _ i j
    unfold orderedWeight
    split_ifs with hij hji
    · have hij' : i.val < j.val := hij
      have hiN : i.val < N := by have := j.isLt; omega
      have hj0 : 0 < j.val := by omega
      exact mul_nonneg (hUdiff i.val hiN) (hVdiff j.val hj0 (Nat.le_of_lt_succ j.isLt))
    · have hji' : j.val < i.val := hji
      have hjN : j.val < N := by have := i.isLt; omega
      have hi0 : 0 < i.val := by omega
      exact mul_nonneg (hBdiff j.val hjN) (hDdiff i.val hi0 (Nat.le_of_lt_succ i.isLt))
    · exact le_rfl
  have hWpos : 0 ≤ ∑ i : Fin (N+1), ∑ j : Fin (N+1),
      w i j*Q μ (x i) (x j) (g i) (g j) (f i) (f j) := by
    apply sum_nonneg
    intro i hi
    apply sum_nonneg
    intro j hj
    exact mul_nonneg (hwpos i j)
      (hQ i.val (Nat.le_of_lt_succ i.isLt) j.val (Nat.le_of_lt_succ j.isLt))
  have hα0 : invPower a 0 = 1 := invPower_zero a
  have hα (i : ℕ) (_hi : i < N) : invPower a i = (1-μ*h)*invPower a (i+1) := by
    rw [← ha]
    exact (invPower_recurrence (ne_of_gt ha0) i).symm
  have hid := balanced_weighted_identity N μ h (progressSum h a N) w x g f
    (invPower a) hα0 hα hstep hoff hdiv hdiag
  change invPower a N*sq (x N) + 2*(1-μ)*progressSum h a N*f N +
    progressSum h a N*(progressSum h a N+1)*sq (g N) +
    (∑ i ∈ range N, h*invPower a (i+1)*Q μ 0 (x i) 0 (g i) 0 (f i)) ≤ sq (x 0)
  linarith only [hid, hWpos]

#print axioms balanced_history_bound

end THGStrong
