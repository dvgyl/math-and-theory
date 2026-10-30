import ADMMConvergence
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

set_option autoImplicit false

open Filter Topology

namespace ADMM74

variable {U V E : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual proximal minimization after an affine constraint map.  A positive
penalty `ρ` is included, so the original objective is not silently normalized. -/
def IsAffineProx (C : Set U) (f : U → ℝ) (A : U →ᵃ[ℝ] E)
    (ρ : ℝ) (c : E) (x : U) : Prop :=
  x ∈ C ∧ ∀ y ∈ C,
    f x + (ρ / 2) * ‖A x - c‖ ^ 2 ≤ f y + (ρ / 2) * ‖A y - c‖ ^ 2

theorem convexOn_div_pos {C : Set U} {f : U → ℝ}
    (hf : ConvexOn ℝ C f) {ρ : ℝ} (hρ : 0 < ρ) :
    ConvexOn ℝ C (fun x => f x / ρ) := by
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hf.smul (le_of_lt (inv_pos.mpr hρ))

theorem convexOn_affine_image {C : Set U} {f : U → ℝ}
    (hf : ConvexOn ℝ C f) (A : U →ᵃ[ℝ] E) (L : E →ᵃ[ℝ] U)
    (hLA : Function.LeftInverse L A) :
    ConvexOn ℝ (A '' C) (fun v => f (L v)) := by
  apply (hf.comp_affineMap L).subset
  · rintro v ⟨x,hx,rfl⟩
    simpa only [Set.mem_preimage, hLA x] using hx
  · exact hf.1.affine_image A

theorem affineProx_to_prox {C : Set U} {f : U → ℝ}
    (A : U →ᵃ[ℝ] E) (L : E →ᵃ[ℝ] U)
    (hLA : Function.LeftInverse L A) {ρ : ℝ} (hρ : 0 < ρ)
    {c : E} {x : U} (hx : IsAffineProx C f A ρ c x) :
    IsProx (A '' C) (fun v => f (L v) / ρ) c (A x) := by
  refine ⟨⟨x,hx.1,rfl⟩, ?_⟩
  rintro v ⟨y,hy,rfl⟩
  dsimp only
  rw [hLA x,hLA y]
  have hh := (div_le_div_iff_of_pos_right hρ).2 (hx.2 y hy)
  have hr : ρ ≠ 0 := ne_of_gt hρ
  convert hh using 1 <;> field_simp <;> ring

/-- Exact reduction of affine equality constraints `A x = B y` to consensus
ADMM.  Taking `B y = b - B₀ y` gives the usual `A x + B₀ y = b` form.

The affine left inverses express injectivity of the constraint maps.  In finite
dimensions they exist and are continuous for full-column-rank linear maps.
Both original block minimizations, the penalty, and the multiplier update are
explicit assumptions; the conclusion concerns the original primal iterates. -/
theorem affine_admm_converges [ProperSpace E]
    (C : Set U) (D : Set V) (f : U → ℝ) (g : V → ℝ)
    (A : U →ᵃ[ℝ] E) (B : V →ᵃ[ℝ] E)
    (L : E →ᵃ[ℝ] U) (R : E →ᵃ[ℝ] V)
    (hLA : Function.LeftInverse L A) (hRB : Function.LeftInverse R B)
    (hL : Continuous L) (hR : Continuous R)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (px : E → U) (py : E → V)
    (hpx : ∀ c, IsAffineProx C f A ρ c (px c))
    (hpy : ∀ c, IsAffineProx D g B ρ c (py c))
    (x : ℕ → U) (y : ℕ → V) (u : ℕ → E)
    (hx : ∀ n, x (n+1) = px (B (y n) - u n))
    (hy : ∀ n, y (n+1) = py (A (x (n+1)) + u n))
    (hu : ∀ n, u (n+1) = u n + (7 / 4 : ℝ) • (A (x (n+1)) - B (y (n+1))))
    (hex : ∃ z v, IsSaddle (A '' C) (B '' D)
      (fun w => f (L w) / ρ) (fun w => g (R w) / ρ) z v) :
    ∃ z v,
      IsSaddle (A '' C) (B '' D)
        (fun w => f (L w) / ρ) (fun w => g (R w) / ρ) z v ∧
      Tendsto x atTop (𝓝 (L z)) ∧ Tendsto y atTop (𝓝 (R z)) ∧
      Tendsto u atTop (𝓝 v) := by
  let F : E → ℝ := fun w => f (L w) / ρ
  let G : E → ℝ := fun w => g (R w) / ρ
  let pf : E → E := fun c => A (px c)
  let pg : E → E := fun c => B (py c)
  have hF : ConvexOn ℝ (A '' C) F :=
    convexOn_affine_image (convexOn_div_pos hf hρ) A L hLA
  have hG : ConvexOn ℝ (B '' D) G :=
    convexOn_affine_image (convexOn_div_pos hg hρ) B R hRB
  have hpf : ∀ c, IsProx (A '' C) F c (pf c) :=
    fun c => affineProx_to_prox A L hLA hρ (hpx c)
  have hpg : ∀ c, IsProx (B '' D) G c (pg c) :=
    fun c => affineProx_to_prox B R hRB hρ (hpy c)
  let s : ℕ → E × E := fun n => (B (y n),u n)
  have hs : ∀ n, s (n+1) = admmMap pf pg (s n) := by
    intro n
    apply Prod.ext
    · change B (y (n+1)) = B (py (A (px (B (y n) - u n)) + u n))
      rw [hy n,hx n]
    · change u (n+1) = u n + (7/4 : ℝ) •
        (A (px (B (y n) - u n)) - B (py (A (px (B (y n) - u n)) + u n)))
      rw [hu n,hy n,hx n]
  obtain ⟨z,v,hsv,ht⟩ := admm_converges hF hG hpf hpg s hs hex
  have htz : Tendsto (fun n => B (y n)) atTop (𝓝 z) := by
    simpa only [s,Function.comp_def] using (continuous_fst.tendsto (z,v)).comp ht
  have htu : Tendsto u atTop (𝓝 v) := by
    simpa only [s,Function.comp_def] using (continuous_snd.tendsto (z,v)).comp ht
  have hty : Tendsto y atTop (𝓝 (R z)) := by
    have hh := hR.continuousAt.tendsto.comp htz
    convert hh using 1
    funext n
    exact (hRB (y n)).symm
  have hfx : pf (z-v) = z := by
    apply isProx_unique hF (hpf (z-v))
    apply isProx_of_supports
    simpa only [sub_sub_cancel_left] using hsv.1
  have htx1 : Tendsto (fun n => x (n+1)) atTop (𝓝 (L z)) := by
    have hh := hL.continuousAt.tendsto.comp
      ((continuous_prox hF hpf).continuousAt.tendsto.comp (htz.sub htu))
    rw [hfx] at hh
    convert hh using 1
    funext n
    simp only [Function.comp_def,pf,hx n]
    exact (hLA _).symm
  exact ⟨z,v,hsv,(tendsto_add_atTop_iff_nat 1).1 htx1,hty,htu⟩

end ADMM74
