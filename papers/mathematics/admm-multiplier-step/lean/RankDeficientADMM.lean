import InfimalImage

set_option autoImplicit false
set_option maxHeartbeats 0

open Filter Topology

namespace ADMM74

variable {U V E : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine primal-dual saddle for the original affine equality constrained
problem. The multiplier here is unscaled; no injectivity of A or B is assumed. -/
def IsAffineSaddle (C : Set U) (D : Set V) (f : U → ℝ) (g : V → ℝ)
    (A : U →ᵃ[ℝ] E) (B : V →ᵃ[ℝ] E) (x₀ : U) (y₀ : V) (w₀ : E) : Prop :=
  x₀ ∈ C ∧ y₀ ∈ D ∧ A x₀ = B y₀ ∧
    (∀ x ∈ C, f x₀ + inner (-w₀) (A x - A x₀) ≤ f x) ∧
    (∀ y ∈ D, g y₀ + inner w₀ (B y - B y₀) ≤ g y)

theorem supports_div_pos {S : Set E} {f : E → ℝ} {z a : E}
    (hs : Supports S f z a) {ρ : ℝ} (hρ : 0 < ρ) :
    Supports S (fun v => f v / ρ) z (ρ⁻¹ • a) := by
  refine ⟨hs.1, fun y hy => ?_⟩
  have hh := div_le_div_of_nonneg_right (hs.2 y hy) (le_of_lt hρ)
  simpa only [real_inner_smul_left, add_div, div_eq_mul_inv, mul_comm, add_mul] using hh

theorem affineSaddle_to_imageSaddle {C : Set U} {D : Set V}
    {f : U → ℝ} {g : V → ℝ} {A : U →ᵃ[ℝ] E} {B : V →ᵃ[ℝ] E}
    {x₀ : U} {y₀ : V} {w₀ : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hs : IsAffineSaddle C D f g A B x₀ y₀ w₀) :
    IsSaddle (A '' C) (B '' D)
      (fun z => imageInf C f A z / ρ) (fun z => imageInf D g B z / ρ)
      (A x₀) (ρ⁻¹ • w₀) := by
  have hf := supports_div_pos (imageInf_support hs.1 hs.2.2.2.1) hρ
  have hg := supports_div_pos (imageInf_support hs.2.1 hs.2.2.2.2) hρ
  constructor
  · simpa only [smul_neg] using hf
  · simpa only [hs.2.2.1] using hg

theorem affineSaddle_minimizes {C : Set U} {D : Set V}
    {f : U → ℝ} {g : V → ℝ} {A : U →ᵃ[ℝ] E} {B : V →ᵃ[ℝ] E}
    {x₀ : U} {y₀ : V} {w₀ : E}
    (hs : IsAffineSaddle C D f g A B x₀ y₀ w₀) :
    ∀ x ∈ C, ∀ y ∈ D, A x = B y → f x₀ + g y₀ ≤ f x + g y := by
  intro x hx y hy hxy
  have hf := hs.2.2.2.1 x hx
  have hg := hs.2.2.2.2 y hy
  rw [inner_neg_left, hxy, hs.2.2.1] at hf
  linarith

/-- Multiplier-only two-block ADMM at 7/4 for arbitrary affine constraint maps.
Only the constraint images are asserted to converge. The original minimizers
may be nonunique and can vary arbitrarily along their fibers. The theorem
contains the actual original subproblem inequalities and objective values.

Global subproblem solvability and an original saddle are explicit. There are
no injectivity, strong convexity, or pre-assumed summability hypotheses. -/
theorem rankDeficient_admm_converges [ProperSpace E]
    (C : Set U) (D : Set V) (f : U → ℝ) (g : V → ℝ)
    (A : U →ᵃ[ℝ] E) (B : V →ᵃ[ℝ] E) (ρ : ℝ) (hρ : 0 < ρ)
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpx : ∀ c, ∃ x, IsAffineProx C f A ρ c x)
    (hpy : ∀ c, ∃ y, IsAffineProx D g B ρ c y)
    (x : ℕ → U) (y : ℕ → V) (u : ℕ → E)
    (hx : ∀ n, IsAffineProx C f A ρ (B (y n) - u n) (x (n+1)))
    (hy : ∀ n, IsAffineProx D g B ρ (A (x (n+1)) + u n) (y (n+1)))
    (hu : ∀ n, u (n+1) = u n + (7 / 4 : ℝ) • (A (x (n+1)) - B (y (n+1))))
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
  have hs : ∀ n, s (n+1) = admmMap pf pg (s n) := by
    intro n
    dsimp [s,admmMap]
    rw [hAx n,hBy n,hu n]
  have hinit : IsSaddle (A '' C) (B '' D) F G (A x₀) (ρ⁻¹ • w₀) :=
    affineSaddle_to_imageSaddle hρ hsaddle
  obtain ⟨z,v,hsv,ht,htx,hval,hmem,hmin⟩ :=
    admm_objective_converges hF hG hpf hpg s hs ⟨A x₀,ρ⁻¹ • w₀,hinit⟩
  have htz : Tendsto (fun n => B (y n)) atTop (𝓝 z) := by
    simpa only [s,Function.comp_def] using (continuous_fst.tendsto (z,v)).comp ht
  have htu : Tendsto u atTop (𝓝 v) := by
    simpa only [s,Function.comp_def] using (continuous_snd.tendsto (z,v)).comp ht
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

#print axioms rankDeficient_admm_converges

end ADMM74
