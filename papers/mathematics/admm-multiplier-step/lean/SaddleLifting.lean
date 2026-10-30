import RankDeficientADMM

set_option autoImplicit false
set_option maxHeartbeats 0

namespace ADMM74

variable {U V E : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem imageSupport_to_affineSupport {C : Set U} {f : U → ℝ}
    {A : U →ᵃ[ℝ] E} {ρ : ℝ} (hρ : 0 < ρ)
    (hb : ∀ v ∈ A '' C, BddBelow (fiberValues C f A v))
    {x : U} {z a : E} (hAx : A x = z)
    (hval : imageInf C f A z = f x)
    (hs : Supports (A '' C) (fun v => imageInf C f A v / ρ) z a) :
    ∀ y ∈ C, f x + inner (ρ • a) (A y - A x) ≤ f y := by
  intro y hy
  have hh := hs.2 (A y) ⟨y,hy,rfl⟩
  dsimp only at hh
  rw [hval] at hh
  have hr : ρ ≠ 0 := ne_of_gt hρ
  have hh' := (mul_le_mul_left hρ).2 hh
  rw [mul_add, mul_div_cancel₀ _ hr, mul_div_cancel₀ _ hr] at hh'
  rw [real_inner_smul_left,hAx]
  exact hh'.trans (imageInf_le hb hy)

/-- Every image saddle lifts to an actual original saddle when the original
quadratic subproblems are solvable everywhere. The original variables need
not be unique and neither affine map needs to be injective. -/
theorem imageSaddle_to_affineSaddle {C : Set U} {D : Set V}
    {f : U → ℝ} {g : V → ℝ} {A : U →ᵃ[ℝ] E} {B : V →ᵃ[ℝ] E}
    {ρ : ℝ} (hρ : 0 < ρ) (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hbF : ∀ v ∈ A '' C, BddBelow (fiberValues C f A v))
    (hbG : ∀ v ∈ B '' D, BddBelow (fiberValues D g B v))
    (hpx : ∀ c, ∃ x, IsAffineProx C f A ρ c x)
    (hpy : ∀ c, ∃ y, IsAffineProx D g B ρ c y)
    {z v : E}
    (hs : IsSaddle (A '' C) (B '' D)
      (fun t => imageInf C f A t / ρ) (fun t => imageInf D g B t / ρ) z v) :
    ∃ x y, IsAffineSaddle C D f g A B x y (ρ • v) ∧ A x = z ∧ B y = z := by
  obtain ⟨x,hx⟩ := hpx (z-v)
  obtain ⟨y,hy⟩ := hpy (z+v)
  have hF := convexOn_div_pos (convexOn_imageInf A hf hbF) hρ
  have hG := convexOn_div_pos (convexOn_imageInf B hg hbG) hρ
  have hAx : A x = z := by
    apply isProx_unique hF (imageInf_affineProx_to_prox hρ hbF hx)
    apply isProx_of_supports
    simpa only [sub_sub_cancel_left] using hs.1
  have hBy : B y = z := by
    apply isProx_unique hG (imageInf_affineProx_to_prox hρ hbG hy)
    apply isProx_of_supports
    simpa only [add_sub_cancel_left] using hs.2
  have hfv : imageInf C f A z = f x := by
    rw [←hAx]
    exact imageInf_eq_of_affineProx hbF hx
  have hgv : imageInf D g B z = g y := by
    rw [←hBy]
    exact imageInf_eq_of_affineProx hbG hy
  refine ⟨x,y,⟨hx.1,hy.1,hAx.trans hBy.symm,?_,?_⟩,hAx,hBy⟩
  · simpa only [smul_neg] using imageSupport_to_affineSupport hρ hbF hAx hfv hs.1
  · exact imageSupport_to_affineSupport hρ hbG hBy hgv hs.2

#print axioms imageSaddle_to_affineSaddle

end ADMM74
