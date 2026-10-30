import SaddleLifting
import NearSharpAllSteps

/- Adapted from the user's prior RankDeficientAllSteps.lean.  The image-function,
attainment, and saddle-lifting proofs are unchanged; only the proven stepsize
range supplied by NearSharpAllSteps is enlarged. -/

set_option autoImplicit false
set_option maxHeartbeats 0

open Filter Topology ADMM74

namespace ADMMNearSharpAllSteps

variable {U V E : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- ADMM convergence for every constant step in (0,943/500] for arbitrary affine maps and arbitrary choices
of original subproblem minimizers. The conclusion concerns constraint images,
the scaled multiplier, and the actual original objective. -/
theorem rankDeficient_admm_allsteps_converges [FiniteDimensional ℝ E]
    (C : Set U) (D : Set V) (f : U → ℝ) (g : V → ℝ)
    (A : U →ᵃ[ℝ] E) (B : V →ᵃ[ℝ] E) (ρ : ℝ) (hρ : 0 < ρ)
    (τ : ℝ) (htau : 0 < τ) (hhi : τ ≤ 943/500)
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpx : ∀ c, ∃ x, IsAffineProx C f A ρ c x)
    (hpy : ∀ c, ∃ y, IsAffineProx D g B ρ c y)
    (x : ℕ → U) (y : ℕ → V) (u : ℕ → E)
    (hx : ∀ n, IsAffineProx C f A ρ (B (y n) - u n) (x (n+1)))
    (hy : ∀ n, IsAffineProx D g B ρ (A (x (n+1)) + u n) (y (n+1)))
    (hu : ∀ n, u (n+1) = u n + τ • (A (x (n+1)) - B (y (n+1))))
    (x₀ : U) (y₀ : V) (w₀ : E)
    (hsaddle : IsAffineSaddle C D f g A B x₀ y₀ w₀) :
    ∃ z v,
      IsSaddle (A '' C) (B '' D)
        (fun t => imageInf C f A t / ρ) (fun t => imageInf D g B t / ρ) z v ∧
      Tendsto (fun n => A (x n)) atTop (𝓝 z) ∧
      Tendsto (fun n => B (y n)) atTop (𝓝 z) ∧
      Tendsto u atTop (𝓝 v) ∧
      Tendsto (fun n => f (x n) + g (y n)) atTop (𝓝 (f x₀ + g y₀)) ∧
      (∀ a ∈ C, ∀ b ∈ D, A a = B b → f x₀ + g y₀ ≤ f a + g b) := by
  classical
  let F : E → ℝ := fun z => imageInf C f A z / ρ
  let G : E → ℝ := fun z => imageInf D g B z / ρ
  have hbF : ∀ v ∈ A '' C, BddBelow (fiberValues C f A v) :=
    fiber_bddBelow_of_affine_support hsaddle.2.2.2.1
  have hbG : ∀ v ∈ B '' D, BddBelow (fiberValues D g B v) :=
    fiber_bddBelow_of_affine_support hsaddle.2.2.2.2
  have hF : ConvexOn ℝ (A '' C) F := convexOn_div_pos (convexOn_imageInf A hf hbF) hρ
  have hG : ConvexOn ℝ (B '' D) G := convexOn_div_pos (convexOn_imageInf B hg hbG) hρ
  let px : E → U := fun c => Classical.choose (hpx c)
  let py : E → V := fun c => Classical.choose (hpy c)
  have hpx' : ∀ c, IsAffineProx C f A ρ c (px c) := fun c => Classical.choose_spec (hpx c)
  have hpy' : ∀ c, IsAffineProx D g B ρ c (py c) := fun c => Classical.choose_spec (hpy c)
  let pf : E → E := fun c => A (px c)
  let pg : E → E := fun c => B (py c)
  have hpf : ∀ c, IsProx (A '' C) F c (pf c) :=
    fun c => imageInf_affineProx_to_prox hρ hbF (hpx' c)
  have hpg : ∀ c, IsProx (B '' D) G c (pg c) :=
    fun c => imageInf_affineProx_to_prox hρ hbG (hpy' c)
  have hAx : ∀ n, pf (B (y n) - u n) = A (x (n+1)) := by
    intro n
    exact isProx_unique hF (hpf _) (imageInf_affineProx_to_prox hρ hbF (hx n))
  have hBy : ∀ n, pg (A (x (n+1)) + u n) = B (y (n+1)) := by
    intro n
    exact isProx_unique hG (hpg _) (imageInf_affineProx_to_prox hρ hbG (hy n))
  let s : ℕ → E × E := fun n => (B (y n),u n)
  have hs : ∀ n, s (n+1) = ADMMInterval.originalMap τ pf pg (s n) := by
    intro n
    dsimp [s,ADMMInterval.originalMap]
    rw [hAx n,hBy n,hu n]
  have hinit : IsSaddle (A '' C) (B '' D) F G (A x₀) (ρ⁻¹ • w₀) :=
    affineSaddle_to_imageSaddle hρ hsaddle
  obtain ⟨z,v,hsv,hmem,hmin,htx,htz,htu,hval⟩ :=
    original_admm_objective_converges τ htau hhi hF hG hpf hpg
      ⟨A x₀,ρ⁻¹ • w₀,hinit⟩ s hs
  have htx' : Tendsto (fun n => A (x n)) atTop (𝓝 z) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa only [s,hAx] using htx
  have heqmin : F z + G z = F (A x₀) + G (A x₀) := by
    apply le_antisymm
    · exact hmin (A x₀) (saddle_minimizes hinit).1
    · exact (saddle_minimizes hinit).2 z hmem
  have hinitial_value : F (A x₀) + G (A x₀) = (f x₀ + g y₀) / ρ := by
    dsimp [F,G]
    rw [imageInf_eq_of_affine_support hsaddle.1 hsaddle.2.2.2.1,
      hsaddle.2.2.1,
      imageInf_eq_of_affine_support hsaddle.2.1 hsaddle.2.2.2.2]
    ring
  have hval' : Tendsto (fun n => (f (x (n+1)) + g (y (n+1))) / ρ) atTop
      (𝓝 ((f x₀ + g y₀) / ρ)) := by
    rw [heqmin,hinitial_value] at hval
    convert hval using 1
    funext n
    dsimp [F,G,s]
    rw [hAx n, imageInf_eq_of_affineProx hbF (hx n),
      imageInf_eq_of_affineProx hbG (hy n)]
    ring
  have hval'' : Tendsto (fun n => f (x (n+1)) + g (y (n+1))) atTop
      (𝓝 (f x₀ + g y₀)) := by
    have hh := hval'.mul_const ρ
    simpa only [div_mul_cancel₀ _ (ne_of_gt hρ)] using hh
  exact ⟨z,v,hsv,htx',htz,htu,(tendsto_add_atTop_iff_nat 1).1 hval'',
    affineSaddle_minimizes hsaddle⟩

/-- The original rank-deficient constrained problem and its original multiplier.
For every constant multiplier step 0 < τ ≤ 943/500, the actual affine-image
iterates converge to those of an original saddle, the unscaled multipliers
converge to its multiplier, and the actual original objective values converge
to its globally optimal value. No choice of unique primal minimizers is needed. -/
theorem rankDeficient_original_admm_converges [FiniteDimensional ℝ E]
    (C : Set U) (D : Set V) (f : U → ℝ) (g : V → ℝ)
    (A : U →ᵃ[ℝ] E) (B : V →ᵃ[ℝ] E) (ρ : ℝ) (hρ : 0 < ρ)
    (τ : ℝ) (htau : 0 < τ) (hhi : τ ≤ 943/500)
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
      Tendsto (fun n => A (x n)) atTop (𝓝 (A xLim)) ∧
      Tendsto (fun n => B (y n)) atTop (𝓝 (B yLim)) ∧
      Tendsto (fun n => ρ • u n) atTop (𝓝 wLim) ∧
      Tendsto (fun n => f (x n) + g (y n)) atTop (𝓝 (f xLim + g yLim)) ∧
      (∀ a ∈ C, ∀ b ∈ D, A a = B b → f xLim + g yLim ≤ f a + g b) := by
  obtain ⟨z,v,hsv,htx,hty,htu,htval,_⟩ :=
    rankDeficient_admm_allsteps_converges C D f g A B ρ hρ τ htau hhi
      hf hg hpx hpy x y u hx hy hu x₀ y₀ w₀ hsaddle
  obtain ⟨a,b,hsab,ha,hb⟩ := imageSaddle_to_affineSaddle hρ hf hg
    (fiber_bddBelow_of_affine_support hsaddle.2.2.2.1)
    (fiber_bddBelow_of_affine_support hsaddle.2.2.2.2) hpx hpy hsv
  have heq : f a + g b = f x₀ + g y₀ := by
    apply le_antisymm
    · exact affineSaddle_minimizes hsab x₀ hsaddle.1 y₀ hsaddle.2.1 hsaddle.2.2.1
    · exact affineSaddle_minimizes hsaddle a hsab.1 b hsab.2.1 hsab.2.2.1
  refine ⟨a,b,ρ • v,hsab,?_,?_,?_,?_,affineSaddle_minimizes hsab⟩
  · simpa only [ha] using htx
  · simpa only [hb] using hty
  · exact tendsto_const_nhds.smul htu
  · simpa only [heq] using htval

#print axioms rankDeficient_admm_allsteps_converges
#print axioms rankDeficient_original_admm_converges

end ADMMNearSharpAllSteps
