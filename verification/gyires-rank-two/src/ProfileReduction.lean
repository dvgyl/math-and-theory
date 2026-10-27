module

public import LawDeficitConnection
public import ConvexLawMaximizer

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.Gyires.RankTwo

open Bernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def EqualInterior (p : ι → ℝ) : Prop :=
  ∀ i j, (0 < p i ∧ p i < 1) → (0 < p j ∧ p j < 1) → p i = p j

/-- This reduction retains the separate profile inequality as an explicit obligation. -/
theorem lawDeficit_nonpos_of_profiles (hn : 2 ≤ Fintype.card ι)
    (μ θ σ : ℝ) (hmean : μ = (Fintype.card ι : ℝ) * θ) (hσ : 0 ≤ σ)
    (hprofile : ∀ p ∈ parameters (ι := ι) μ, ∀ q ∈ parameters μ,
      EqualInterior p → EqualInterior q →
        lawDeficit (Fintype.card ι) θ σ (law p) (law q) ≤ 0)
    (p q : ι → ℝ) (hp : p ∈ parameters μ) (hq : q ∈ parameters μ) :
    lawDeficit (Fintype.card ι) θ σ (law p) (law q) ≤ 0 := by
  let D := convexHull ℝ (law '' parameters (ι := ι) μ)
  have hD : Convex ℝ D := convex_convexHull ℝ _
  have hvariance : ∀ Q ∈ D, 0 ≤ varianceLaw (Fintype.card ι) θ σ Q :=
    varianceLaw_nonneg_on_hull hn μ θ σ hmean hσ
  have hQmem : law q ∈ D := subset_convexHull ℝ _ ⟨q, hq, rfl⟩
  obtain ⟨p', hp', hpmax, hpequal⟩ := exists_convex_law_maximizer
    (fun P => lawDeficit (Fintype.card ι) θ σ P (law q)) μ
    (continuous_lawDeficit_left _ θ σ (law q))
    (lawDeficit_convex_left _ θ σ hσ D hD (law q) (hvariance _ hQmem)) ⟨p, hp⟩
  obtain ⟨q', hq', hqmax, hqequal⟩ := exists_convex_law_maximizer
    (fun Q => lawDeficit (Fintype.card ι) θ σ (law p') Q) μ
    (continuous_lawDeficit_right _ θ σ (law p'))
    (lawDeficit_convex_right _ θ σ hσ D hD hvariance (law p')) ⟨q, hq⟩
  exact (hpmax p hp).trans ((hqmax q hq).trans (hprofile p' hp' q' hq' hpequal hqequal))

end MathAndTheory.Gyires.RankTwo
