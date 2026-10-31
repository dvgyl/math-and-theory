import NearSharpRankDeficient

/- Adapted from the user's prior FullRankAllSteps.lean.  Continuous left inverses
transfer the certified affine-image limits to the original primal variables. -/

set_option autoImplicit false

open Filter Topology ADMM74

namespace ADMMNearSharpAllSteps

variable {U V E : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If the affine maps have continuous left inverses (in particular for
finite-dimensional full-column-rank affine constraints), the original primal
variables themselves converge to the same original saddle as the multiplier.
This is a direct corollary of the arbitrary-rank theorem, with no new algorithm
or new restriction on the positive constant step up to 377359/200000. -/
theorem fullRank_original_admm_converges [FiniteDimensional ℝ E]
    (C : Set U) (D : Set V) (f : U → ℝ) (g : V → ℝ)
    (A : U →ᵃ[ℝ] E) (B : V →ᵃ[ℝ] E)
    (L : E → U) (R : E → V)
    (hLA : Function.LeftInverse L A) (hRB : Function.LeftInverse R B)
    (hL : Continuous L) (hR : Continuous R)
    (ρ : ℝ) (hρ : 0 < ρ) (τ : ℝ) (htau : 0 < τ) (hhi : τ ≤ 377359/200000)
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpx : ∀ c, ∃ x, IsAffineProx C f A ρ c x)
    (hpy : ∀ c, ∃ y, IsAffineProx D g B ρ c y)
    (x : ℕ → U) (y : ℕ → V) (u : ℕ → E)
    (hx : ∀ n, IsAffineProx C f A ρ (B (y n) - u n) (x (n+1)))
    (hy : ∀ n, IsAffineProx D g B ρ (A (x (n+1)) + u n) (y (n+1)))
    (hu : ∀ n, u (n+1) = u n + τ • (A (x (n+1)) - B (y (n+1))))
    (x₀ : U) (y₀ : V) (w₀ : E)
    (hsaddle : IsAffineSaddle C D f g A B x₀ y₀ w₀) :
    ∃ xLim yLim wLim,
      IsAffineSaddle C D f g A B xLim yLim wLim ∧
      Tendsto x atTop (𝓝 xLim) ∧
      Tendsto y atTop (𝓝 yLim) ∧
      Tendsto (fun n => ρ • u n) atTop (𝓝 wLim) ∧
      Tendsto (fun n => f (x n) + g (y n)) atTop (𝓝 (f xLim + g yLim)) ∧
      (∀ a ∈ C, ∀ b ∈ D, A a = B b → f xLim + g yLim ≤ f a + g b) := by
  obtain ⟨a,b,w,hs,htx,hty,htu,htval,hopt⟩ :=
    rankDeficient_original_admm_converges C D f g A B ρ hρ τ htau hhi
      hf hg hpx hpy x y u hx hy hu x₀ y₀ w₀ hsaddle
  refine ⟨a,b,w,hs,?_,?_,htu,htval,hopt⟩
  · have hh := hL.continuousAt.tendsto.comp htx
    rw [hLA a] at hh
    convert hh using 1
    funext n
    exact (hLA (x n)).symm
  · have hh := hR.continuousAt.tendsto.comp hty
    rw [hRB b] at hh
    convert hh using 1
    funext n
    exact (hRB (y n)).symm

#print axioms fullRank_original_admm_converges

end ADMMNearSharpAllSteps
