module
public import DepolarizingSharp
public import WeylFrame
public import DepolarizingClosedBounds
public import DepolarizingComparison
public import FullDepolarizingChannel


@[expose] public section

/-! Exact actual-channel conditional contraction in every finite dimension.
The concrete Fourier Bell family and balanced frame discharge every geometric
hypothesis of the lower bound. References remain unrestricted in the upper. -/
open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey

namespace DepolarizingExact
noncomputable section
variable {d : ℕ} [NeZero d]

abbrev A (d : ℕ) := WeylBell.A d
abbrev I (d : ℕ) := A d × A d

def bells (d : ℕ) [NeZero d] : DepolarizingSharp.BellFamily (I d) (A d) where
  mat := WeylBell.projector
  positive := WeylBell.projector_positive
  trace_one := WeylBell.projector_trace
  orthogonal := WeylBell.projector_multiply
  resolution := WeylBell.projector_resolution
  marginal i := by
    simpa only [BellEncoding.mixedMarginal,A,WeylBell.A,ZMod.card] using
      WeylBell.projector_marginal i

theorem size_eq : TightFrameGeometry.size (I d)=(d:ℝ)^2 := by
  simp [TightFrameGeometry.size,I,A,WeylBell.A,ZMod.card,pow_two]

theorem label_card_ge_four (hd : 2≤d) : 4≤Fintype.card (I d) := by
  simp only [I,A,WeylBell.A,Fintype.card_prod,ZMod.card]
  nlinarith

/-- Exact negative-depolarizing formula for any actual channel with the map,
on the canonical d-dimensional basis, including both physical endpoints. -/
theorem conditionalCoefficient_negative (hd : 2≤d) (N : QuantumChannel (A d) (A d))
    (s : ℝ) (hs : 0≤s) (hb : ((d:ℝ)^2-1)*s≤1)
    (hN : ∀ X, N.map X=((1+s)/(d:ℝ)) •
      (X.trace • (1:Matrix (A d) (A d) ℂ))-s • X)
    (γ : ℝ) (hγ : 1≤γ) :
    conditionalCoefficient N γ=DepolarizingEffects.sharpBound ((d:ℝ)^2) s := by
  have hc : Fintype.card (A d)=d := ZMod.card d
  have hN' : ∀ X, N.map X=((1+s)/(Fintype.card (A d):ℝ)) •
      (X.trace • (1:Matrix (A d) (A d) ℂ))-s • X := by simpa only [hc] using hN
  rw [conditionalCoefficient_parameter_independent N γ hγ]
  apply le_antisymm
  · simpa only [hc] using DepolarizingBounds.conditionalCoefficient_le_closed
      N (by simpa only [hc] using hd) s hs (by simpa only [hc] using hb) hN' 1
  · have hl := DepolarizingSharp.sharpBound_le_conditionalCoefficient
      (WeylFrame.bellFrame d hd) (label_card_ge_four hd) (bells d)
      (by rw [size_eq,hc]) N s hs (by simpa only [size_eq] using hb) hN'
    simpa only [size_eq] using hl

/-- Specialization to the explicitly constructed CPTP negative channel. -/
theorem channel_conditionalCoefficient_negative (hd : 2≤d) (s : ℝ) (hs : 0≤s)
    (hb : ((Fintype.card (A d):ℝ)^2-1)*s≤1) (γ : ℝ) (hγ : 1≤γ) :
    conditionalCoefficient (DepolarizingChannel.channel (A:=A d) s hs hb) γ=
      DepolarizingEffects.sharpBound ((d:ℝ)^2) s := by
  apply conditionalCoefficient_negative hd _ s hs
    (by simpa only [A,WeylBell.A,ZMod.card] using hb) _ γ hγ
  intro X
  simpa only [A,WeylBell.A,ZMod.card] using
    DepolarizingChannel.channel_map (A:=A d) s hs hb X

/-- A single exact expression for the entire physical parameter interval. -/
theorem conditionalCoefficient_full (hd : 2≤d) (N : QuantumChannel (A d) (A d))
    (l : ℝ) (hlow : -1≤((d:ℝ)^2-1)*l) (hhigh : l≤1)
    (hN : ∀ X, N.map X=l • X+((1-l)/(d:ℝ)) •
      (X.trace • (1:Matrix (A d) (A d) ℂ))) (γ : ℝ) (hγ : 1≤γ) :
    conditionalCoefficient N γ=
      if 0≤l then l else DepolarizingEffects.sharpBound ((d:ℝ)^2) (-l) := by
  have hc : Fintype.card (A d)=d := ZMod.card d
  by_cases hl : 0≤l
  · rw [if_pos hl]
    apply PositiveDepolarizing.conditionalCoefficient_eq N
      (by simpa only [hc] using hd) l hl hhigh _ γ hγ
    simpa only [hc] using hN
  · rw [if_neg hl]
    apply conditionalCoefficient_negative hd N (-l) (by linarith)
      (by nlinarith) _ γ hγ
    intro X
    rw [hN]
    simp only [neg_smul,sub_neg_eq_add,sub_eq_add_neg,neg_neg]
    module

/-- Exact coefficient of the constructed physical channel, not an abstract
coefficient satisfying a surrogate inequality. -/
theorem actual_full_channel (hd : 2≤d) (l : ℝ)
    (hlow : -1≤((Fintype.card (A d):ℝ)^2-1)*l) (hhigh : l≤1)
    (γ : ℝ) (hγ : 1≤γ) :
    conditionalCoefficient (FullDepolarizingChannel.channel (A:=A d) l hlow hhigh) γ=
      if 0≤l then l else DepolarizingEffects.sharpBound ((d:ℝ)^2) (-l) := by
  apply conditionalCoefficient_full hd _ l
    (by simpa only [A,WeylBell.A,ZMod.card] using hlow) hhigh _ γ hγ
  intro X
  simpa only [A,WeylBell.A,ZMod.card] using
    FullDepolarizingChannel.channel_map (A:=A d) l hlow hhigh X

end
end DepolarizingExact
