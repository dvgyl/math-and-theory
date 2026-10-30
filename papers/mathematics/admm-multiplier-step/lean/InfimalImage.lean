import LinearReduction
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option autoImplicit false
set_option maxHeartbeats 0

namespace ADMM74

variable {U E : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def fiberValues (C : Set U) (f : U → ℝ) (A : U →ᵃ[ℝ] E) (v : E) : Set ℝ :=
  {r | ∃ x ∈ C, A x = v ∧ f x = r}

noncomputable def imageInf (C : Set U) (f : U → ℝ) (A : U →ᵃ[ℝ] E) (v : E) : ℝ :=
  sInf (fiberValues C f A v)

theorem fiberValues_nonempty {C : Set U} {f : U → ℝ} {A : U →ᵃ[ℝ] E} {v : E}
    (hv : v ∈ A '' C) : (fiberValues C f A v).Nonempty := by
  obtain ⟨x,hx,rfl⟩ := hv
  exact ⟨f x,x,hx,rfl,rfl⟩

theorem imageInf_le {C : Set U} {f : U → ℝ} {A : U →ᵃ[ℝ] E}
    (hb : ∀ v ∈ A '' C, BddBelow (fiberValues C f A v)) {x : U} (hx : x ∈ C) :
    imageInf C f A (A x) ≤ f x := by
  exact csInf_le (hb (A x) ⟨x,hx,rfl⟩) ⟨x,hx,rfl,rfl⟩

theorem imageInf_approx {C : Set U} {f : U → ℝ} {A : U →ᵃ[ℝ] E} {v : E}
    (hv : v ∈ A '' C) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ C, A x = v ∧ f x < imageInf C f A v + ε := by
  obtain ⟨r,⟨x,hx,hAx,hfx⟩,hr⟩ :=
    exists_lt_of_csInf_lt (fiberValues_nonempty hv)
      (show sInf (fiberValues C f A v) < imageInf C f A v + ε by
        unfold imageInf; linarith)
  exact ⟨x,hx,hAx,by simpa only [hfx] using hr⟩

theorem convexOn_imageInf {C : Set U} {f : U → ℝ} (A : U →ᵃ[ℝ] E)
    (hf : ConvexOn ℝ C f)
    (hb : ∀ v ∈ A '' C, BddBelow (fiberValues C f A v)) :
    ConvexOn ℝ (A '' C) (imageInf C f A) := by
  refine ⟨hf.1.affine_image A, ?_⟩
  intro v hv w hw a b ha hbb hab
  simp only [smul_eq_mul]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x,hx,hAx,hfx⟩ := imageInf_approx (f := f) hv hε
  obtain ⟨y,hy,hAy,hfy⟩ := imageInf_approx (f := f) hw hε
  have hxy : a • x + b • y ∈ C := hf.1 hx hy ha hbb hab
  have hc := hf.2 hx hy ha hbb hab
  have hi := imageInf_le hb hxy
  have hA : A (a • x + b • y) = a • v + b • w := by
    rw [Convex.combo_affine_apply hab, hAx, hAy]
  rw [hA] at hi
  simp only [smul_eq_mul] at hc
  have h1 := mul_le_mul_of_nonneg_left (le_of_lt hfx) ha
  have h2 := mul_le_mul_of_nonneg_left (le_of_lt hfy) hbb
  nlinarith

theorem fiber_bddBelow_of_affine_support {C : Set U} {f : U → ℝ}
    {A : U →ᵃ[ℝ] E} {x₀ : U} {a : E}
    (hs : ∀ x ∈ C, f x₀ + inner a (A x - A x₀) ≤ f x) :
    ∀ v ∈ A '' C, BddBelow (fiberValues C f A v) := by
  intro v _
  refine ⟨f x₀ + inner a (v - A x₀), ?_⟩
  rintro r ⟨x,hx,hAx,rfl⟩
  simpa only [hAx] using hs x hx

theorem imageInf_eq_of_affineProx {C : Set U} {f : U → ℝ}
    {A : U →ᵃ[ℝ] E} {ρ : ℝ} {c : E} {x : U}
    (hb : ∀ v ∈ A '' C, BddBelow (fiberValues C f A v))
    (hx : IsAffineProx C f A ρ c x) : imageInf C f A (A x) = f x := by
  apply le_antisymm (imageInf_le hb hx.1)
  apply le_csInf (fiberValues_nonempty ⟨x,hx.1,rfl⟩)
  rintro r ⟨y,hy,hAy,rfl⟩
  have hh := hx.2 y hy
  rw [hAy] at hh
  linarith

theorem imageInf_affineProx_to_prox {C : Set U} {f : U → ℝ}
    {A : U →ᵃ[ℝ] E} {ρ : ℝ} (hρ : 0 < ρ) {c : E} {x : U}
    (hb : ∀ v ∈ A '' C, BddBelow (fiberValues C f A v))
    (hx : IsAffineProx C f A ρ c x) :
    IsProx (A '' C) (fun v => imageInf C f A v / ρ) c (A x) := by
  refine ⟨⟨x,hx.1,rfl⟩, ?_⟩
  intro v hv
  have hl : f x + (ρ / 2) * ‖A x - c‖ ^ 2 - (ρ / 2) * ‖v - c‖ ^ 2 ≤
      imageInf C f A v := by
    apply le_csInf (fiberValues_nonempty hv)
    rintro r ⟨y,hy,hAy,rfl⟩
    have hh := hx.2 y hy
    rw [hAy] at hh
    linarith
  dsimp only
  rw [imageInf_eq_of_affineProx hb hx]
  have hh := (div_le_div_iff_of_pos_right hρ).2
    (show f x + (ρ / 2) * ‖A x - c‖ ^ 2 ≤
        imageInf C f A v + (ρ / 2) * ‖v - c‖ ^ 2 by linarith)
  have hn : ρ ≠ 0 := ne_of_gt hρ
  convert hh using 1 <;> field_simp <;> ring

theorem imageInf_eq_of_affine_support {C : Set U} {f : U → ℝ}
    {A : U →ᵃ[ℝ] E} {x₀ : U} {a : E} (hx₀ : x₀ ∈ C)
    (hs : ∀ x ∈ C, f x₀ + inner a (A x - A x₀) ≤ f x) :
    imageInf C f A (A x₀) = f x₀ := by
  apply le_antisymm (imageInf_le (fiber_bddBelow_of_affine_support hs) hx₀)
  apply le_csInf (fiberValues_nonempty ⟨x₀,hx₀,rfl⟩)
  rintro r ⟨x,hx,hAx,rfl⟩
  have hh := hs x hx
  simpa only [hAx, sub_self, inner_zero_right, add_zero] using hh

theorem imageInf_support {C : Set U} {f : U → ℝ}
    {A : U →ᵃ[ℝ] E} {x₀ : U} {a : E} (hx₀ : x₀ ∈ C)
    (hs : ∀ x ∈ C, f x₀ + inner a (A x - A x₀) ≤ f x) :
    Supports (A '' C) (imageInf C f A) (A x₀) a := by
  refine ⟨⟨x₀,hx₀,rfl⟩, ?_⟩
  intro v hv
  rw [imageInf_eq_of_affine_support hx₀ hs]
  apply le_csInf (fiberValues_nonempty hv)
  rintro r ⟨x,hx,hAx,rfl⟩
  simpa only [hAx] using hs x hx

end ADMM74
