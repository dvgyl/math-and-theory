import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
open Set

namespace DiscreteNesterov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A vector-valued first-order remainder estimate with a constant reference
derivative. Only the derivative on the actual interval is used. -/
lemma norm_taylor_remainder_le {f f' : ℝ → E} {a b C : ℝ} {v : E}
    (hab : a ≤ b)
    (hf : ∀ s ∈ Icc a b, HasDerivAt f (f' s) s)
    (hbound : ∀ s ∈ Icc a b, ‖f' s - v‖ ≤ C) :
    ‖f b - f a - (b - a) • v‖ ≤ C * (b - a) := by
  have hd : ∀ s ∈ Icc a b,
      HasDerivWithinAt (fun t => f t - t • v) (f' s - v) (Icc a b) s := by
    intro s hs
    convert ((hf s hs).sub ((hasDerivAt_id s).smul_const v)).hasDerivWithinAt using 1
    simp
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (fun s hs => hbound s (Ico_subset_Icc_self hs)) b ⟨hab, le_rfl⟩
  convert h using 1
  congr 1
  module

/-- Continuous derivatives on a compact interval give uniform forward and
backward first-order remainders on its positive-time subintervals. -/
theorem uniform_taylor_remainders {f f' : ℝ → E} {T η : ℝ}
    (hc : ContinuousOn f' (Icc 0 T))
    (hd : ∀ t > 0, t ≤ T → HasDerivAt f (f' t) t)
    (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ T → b - a ≤ δ →
        ‖f b - f a - (b - a) • f' a‖ ≤ η * (b - a) ∧
        ‖f b - f a - (b - a) • f' b‖ ≤ η * (b - a) := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hc
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff_le.mp hu η hη
  refine ⟨δ, hδ, ?_⟩
  intro a b ha hab hb hba
  have haT : a ≤ T := hab.trans hb
  have hd' : ∀ s ∈ Icc a b, HasDerivAt f (f' s) s := by
    intro s hs
    exact hd s (ha.trans_le hs.1) (hs.2.trans hb)
  constructor
  · apply norm_taylor_remainder_le hab hd'
    intro s hs
    have hdist : dist s a ≤ δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
      linarith only [hs.2, hba]
    have hm := hmod s ⟨ha.le.trans hs.1, hs.2.trans hb⟩ a ⟨ha.le, haT⟩ hdist
    simpa only [dist_eq_norm] using hm
  · apply norm_taylor_remainder_le hab hd'
    intro s hs
    have hdist : dist s b ≤ δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2)]
      linarith only [hs.1, hba]
    have hm := hmod s ⟨ha.le.trans hs.1, hs.2.trans hb⟩ b ⟨ha.le.trans hab, hb⟩ hdist
    simpa only [dist_eq_norm] using hm

end DiscreteNesterov
