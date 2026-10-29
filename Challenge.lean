module
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Strong

/-! The exact final-gradient bound uses actual functions on complete real
inner-product spaces. The attainment statement has L = R = 1. -/
@[expose] public section

noncomputable section
namespace THGStrong

def gradientRate (μ h : ℝ) (N : ℕ) : ℝ :=
  max (if μ = 0 then (1+(N:ℝ)*h)⁻¹ else
    μ*(1-μ*h)^N/(1-(1-μ)*(1-μ*h)^N)) (|1-h|^N)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem taylor_hendrickx_glineur_conjecture3
    (f : E → ℝ) (g : E → E) (x : ℕ → E) (xstar : E)
    (μ L h : ℝ) (N : ℕ)
    (hμ0 : 0 ≤ μ) (hμL : μ ≤ L) (hL : 0 < L) (hh : 0 ≤ h) (hh2 : h ≤ 2)
    (hf : StrongConvexOn Set.univ μ f)
    (hg : ∀ z, HasGradientAt f (g z) z)
    (hLip : ∀ y z, ‖g y-g z‖ ≤ L*‖y-z‖)
    (hmin : ∀ z, f xstar ≤ f z)
    (hstep : ∀ i < N, x (i+1) = x i-(h/L) • g (x i)) :
    ‖g (x N)‖ ≤ L*gradientRate (μ/L) h N*‖x 0-xstar‖ := by
  sorry

namespace Sharpness

def NormalizedAttainment (μ h : ℝ) (N : ℕ) (c : ℝ) : Prop :=
  ∃ (f g : ℝ → ℝ) (x : ℕ → ℝ),
    StrongConvexOn Set.univ μ f ∧
    (∀ z, HasGradientAt f (g z) z) ∧
    (∀ y z, ‖g y-g z‖ ≤ ‖y-z‖) ∧
    (∀ z, f 0 ≤ f z) ∧ x 0 = 1 ∧
    (∀ i < N, x (i+1) = x i-h*g (x i)) ∧
    ‖g (x N)‖ = c

theorem attain_rate {μ h : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hh : 0 ≤ h) (hh2 : h ≤ 2) (N : ℕ) :
    NormalizedAttainment μ h N (gradientRate μ h N) := by
  sorry

end Sharpness
end THGStrong
