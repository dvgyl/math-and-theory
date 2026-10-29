module
public import DepolarizingChannel
public import PositiveDepolarizing


@[expose] public section

/-! Actual CPTP depolarizing channels on the entire physical parameter interval. -/
open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey GeneralContraction

namespace FullDepolarizingChannel
noncomputable section
variable {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]

def positive (l : ℝ) (hl : 0≤l) (hl1 : l≤1) : QuantumChannel A A where
  map := DepolarizingChannel.linear (-l)
  trace_preserving := DepolarizingChannel.linear_trace (-l)
  completely_positive R _ _ X hX := by
    rw [DepolarizingChannel.amplified_formula]
    simp only [neg_smul,sub_neg_eq_add,sub_eq_add_neg,neg_neg]
    exact (posSemidef_real_smul _
      (kronecker_positive _ _ (partialTraceMatrix_posSemidef X hX) Matrix.PosSemidef.one)
      _ (div_nonneg (sub_nonneg.mpr hl1) (by positivity))).add
      (posSemidef_real_smul X hX l hl)

@[simp] theorem positive_map (l : ℝ) (hl : 0≤l) (hl1 : l≤1) (X : Matrix A A ℂ) :
    (positive l hl hl1).map X = l • X+
      ((1-l)/(Fintype.card A:ℝ)) • (X.trace • (1:Matrix A A ℂ)) := by
  change DepolarizingChannel.linear (-l) X=_
  simp only [DepolarizingChannel.linear_formula,neg_smul,sub_neg_eq_add,sub_eq_add_neg,neg_neg]
  module

/-- The lower parameter inequality is written without division. For d>=2 it
is exactly lambda>=-1/(d^2-1). -/
def channel (l : ℝ) (hlow : -1≤((Fintype.card A:ℝ)^2-1)*l) (hhigh : l≤1) :
    QuantumChannel A A :=
  if h : 0≤l then positive l h hhigh
  else DepolarizingChannel.channel (-l) (by linarith)
    (by nlinarith : ((Fintype.card A:ℝ)^2-1)*(-l)≤1)

@[simp] theorem channel_map (l : ℝ) (hlow : -1≤((Fintype.card A:ℝ)^2-1)*l)
    (hhigh : l≤1) (X : Matrix A A ℂ) :
    (channel l hlow hhigh).map X = l • X+
      ((1-l)/(Fintype.card A:ℝ)) • (X.trace • (1:Matrix A A ℂ)) := by
  unfold channel
  split_ifs with h
  · exact positive_map l h hhigh X
  · rw [DepolarizingChannel.channel_map]
    simp only [neg_smul,sub_neg_eq_add,sub_eq_add_neg,neg_neg]
    module

end
end FullDepolarizingChannel
