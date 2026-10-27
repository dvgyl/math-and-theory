import DominationULC.Sequences
import DominationULC.MonotoneRatios

open scoped BigOperators

namespace DominationULC

noncomputable def cutoff (w : Seq) (L : ℤ) : Seq :=
  w.filter (fun s => s ≤ L)

theorem cutoff_apply (w : Seq) (L s : ℤ) :
    cutoff w L s = if s ≤ L then w s else 0 := rfl

theorem cutoff_convolution_apply (w q : Seq) (N L : ℤ) :
    (cutoff w L * q) N =
      ∑ i ∈ w.support.filter (fun i => i ≤ L), w i * q (N-i) := by
  classical
  rw [convolution_apply]
  change (∑ i ∈ (w.filter (fun i => i ≤ L)).support,
    cutoff w L i * q (N-i)) = _
  rw [Finsupp.support_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cutoff_apply, if_pos (Finset.mem_filter.mp hi).2]

/-- Adding an extra positive bounded part makes the sum of a fixed group of
parts stochastically smaller, with every comparison expressed without division. -/
theorem conditional_coefficient_mono (w q : Seq) (hw : Nonnegative w)
    (hq : TP2 q) (b : ℕ) (N L : ℤ) :
    (cutoff w L * q) N * (w * (q * part b)) N ≤
      (cutoff w L * (q * part b)) N * (w * q) N := by
  rw [cutoff_convolution_apply, cutoff_convolution_apply,
    convolution_apply w (q * part b), convolution_apply w q]
  apply conditional_lowerTail_cross_mul
  · intro i hi
    exact hw i
  · intro u v huv
    exact part_mlr hq b huv.le

end DominationULC
