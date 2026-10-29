import THGStrong.Balanced
import THGStrong.AnalyticFinal

noncomputable section
namespace THGStrong

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Taylor--Hendrickx--Glineur Conjecture 3, with all closed parameter
boundaries included and the rate written continuously at `1 - μ*h/L = 0`.

This theorem has no interpolation, certificate, or auxiliary trajectory
assumption: its hypotheses are ordinary strong convexity, actual gradients,
a Lipschitz bound, an actual minimizer, and constant-step gradient descent. -/
theorem taylor_hendrickx_glineur_conjecture3
    (f : E → ℝ) (g : E → E) (x : ℕ → E) (xstar : E)
    (μ L h : ℝ) (N : ℕ)
    (hμ0 : 0 ≤ μ) (hμL : μ ≤ L) (hL : 0 < L) (hh : 0 ≤ h) (hh2 : h ≤ 2)
    (hf : StrongConvexOn Set.univ μ f)
    (hg : ∀ z, HasGradientAt f (g z) z)
    (hLip : ∀ y z, ‖g y-g z‖ ≤ L*‖y-z‖)
    (hmin : ∀ z, f xstar ≤ f z)
    (hstep : ∀ i < N, x (i+1) = x i-(h/L) • g (x i)) :
    ‖g (x N)‖ ≤ L*gradientRate (μ/L) h N*‖x 0-xstar‖ :=
  analytic_gradient_rate_of_certificate balanced_history_bound f g x xstar
    μ L h N hμ0 hμL hL hh hh2 hf hg hLip hmin hstep

#print axioms taylor_hendrickx_glineur_conjecture3

theorem taylor_hendrickx_glineur_conjecture3_with_radius
    (f : E → ℝ) (g : E → E) (x : ℕ → E) (xstar : E)
    (μ L h R : ℝ) (N : ℕ)
    (hμ0 : 0 ≤ μ) (hμL : μ ≤ L) (hL : 0 < L) (hh : 0 ≤ h) (hh2 : h ≤ 2)
    (hf : StrongConvexOn Set.univ μ f)
    (hg : ∀ z, HasGradientAt f (g z) z)
    (hLip : ∀ y z, ‖g y-g z‖ ≤ L*‖y-z‖)
    (hmin : ∀ z, f xstar ≤ f z)
    (hstep : ∀ i < N, x (i+1) = x i-(h/L) • g (x i))
    (hR : ‖x 0-xstar‖ ≤ R) :
    ‖g (x N)‖ ≤ L*gradientRate (μ/L) h N*R :=
  le_trans (taylor_hendrickx_glineur_conjecture3 f g x xstar μ L h N
    hμ0 hμL hL hh hh2 hf hg hLip hmin hstep)
    (mul_le_mul_of_nonneg_left hR
      (mul_nonneg (le_of_lt hL) (gradientRate_nonneg (μ/L) h N)))

#print axioms taylor_hendrickx_glineur_conjecture3_with_radius

end THGStrong
