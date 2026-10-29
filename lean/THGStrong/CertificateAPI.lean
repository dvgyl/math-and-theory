module
public import THGStrong.Core
public import THGStrong.ScalarBase

@[expose] public section

noncomputable section
open scoped BigOperators

namespace THGStrong

/-- The explicit balanced certificate, with its star residual retained.  This is
an interface used to separate the finite certificate from the rate reduction.
It is not an axiom: the final theorem must supply a proof of this proposition. -/
def BalancedHistoryBound (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : Prop :=
  ∀ (N : ℕ) (h a μ : ℝ) (x g : ℕ → E) (f : ℕ → ℝ),
    0 < N → 1 < h → h < 2 → h - 1 < a → a = 1 - μ * h →
    invPower (h - 1) N = 1 + progressSum h a N →
    (∀ i < N, x (i+1) = x i - h • g i) →
    (∀ i ≤ N, ∀ j ≤ N, 0 ≤ Q μ (x i) (x j) (g i) (g j) (f i) (f j)) →
    invPower a N * sq (x N) +
        2 * (1 - μ) * progressSum h a N * f N +
        progressSum h a N * (progressSum h a N + 1) * sq (g N) +
        (∑ i ∈ Finset.range N, h * (a⁻¹)^(i+1) * Q μ 0 (x i) 0 (g i) 0 (f i))
      ≤ sq (x 0)

end THGStrong
