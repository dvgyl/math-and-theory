import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

set_option autoImplicit false

namespace ADMM74

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

/-- A supporting affine functional for a convex function on its effective domain. -/
def Supports (C : Set E) (f : E → ℝ) (x a : E) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, f x + ⟪a, y - x⟫ ≤ f y

/-- An actual global minimum of the proximal objective on its effective domain. -/
def IsProx (C : Set E) (f : E → ℝ) (c x : E) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, f x + (1 / 2 : ℝ) * ‖x - c‖ ^ 2 ≤
    f y + (1 / 2 : ℝ) * ‖y - c‖ ^ 2

theorem isProx_of_supports {C : Set E} {f : E → ℝ} {c x : E}
    (h : Supports C f x (c - x)) : IsProx C f c x := by
  refine ⟨h.1, fun y hy => ?_⟩
  have hs := h.2 y hy
  have he : y - c = (x - c) + (y - x) := by abel
  have hn := norm_nonneg (y - x)
  rw [he, norm_add_sq_real]
  have hi : ⟪c - x, y - x⟫ = -⟪x - c, y - x⟫ := by
    simp only [inner_sub_left]
    ring
  rw [hi] at hs
  nlinarith [sq_nonneg ‖y - x‖]

theorem supports_of_isProx {C : Set E} {f : E → ℝ} {c x : E}
    (hf : ConvexOn ℝ C f) (h : IsProx C f c x) : Supports C f x (c - x) := by
  refine ⟨h.1, fun y hy => ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  let t : ℝ := min (1 / 2) (ε / (‖y - x‖ ^ 2 + 1))
  have hden : 0 < ‖y - x‖ ^ 2 + 1 := by positivity
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε hden)
  have ht_half : t ≤ 1 / 2 := min_le_left _ _
  have ht_one : t ≤ 1 := by linarith
  have ht_eps : t * (‖y - x‖ ^ 2 + 1) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hw : (1 - t) • x + t • y ∈ C :=
    hf.1 h.1 hy (by linarith) (le_of_lt ht) (by ring)
  have hm := h.2 ((1 - t) • x + t • y) hw
  have hc := hf.2 h.1 hy (show 0 ≤ 1 - t by linarith) (le_of_lt ht)
    (show (1 - t) + t = 1 by ring)
  simp only [smul_eq_mul] at hc
  have he : (1 - t) • x + t • y - c = (x - c) + t • (y - x) := by module
  rw [he, norm_add_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht, mul_pow] at hm
  have hi : ⟪c - x, y - x⟫ = -⟪x - c, y - x⟫ := by
    simp only [inner_sub_left]
    ring
  rw [hi]
  have hstep : t * (f x - ⟪x - c, y - x⟫ - f y) ≤
      (t ^ 2 / 2) * ‖y - x‖ ^ 2 := by nlinarith [hm, hc]
  have hdiv : f x - ⟪x - c, y - x⟫ - f y ≤ (t / 2) * ‖y - x‖ ^ 2 := by
    apply (mul_le_mul_left ht).mp
    nlinarith [hstep]
  nlinarith [sq_nonneg ‖y - x‖]

theorem supports_iff_isProx {C : Set E} {f : E → ℝ} {c x : E}
    (hf : ConvexOn ℝ C f) : Supports C f x (c - x) ↔ IsProx C f c x :=
  ⟨isProx_of_supports, supports_of_isProx hf⟩

theorem norm_sub_le_of_supports {C : Set E} {f : E → ℝ} {c d x y : E}
    (hx : Supports C f x (c - x)) (hy : Supports C f y (d - y)) :
    ‖x - y‖ ≤ ‖c - d‖ := by
  have hxy := hx.2 y hy.1
  have hyx := hy.2 x hx.1
  have hi : ‖x - y‖ ^ 2 ≤ ⟪c - d, x - y⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right] at hxy hyx ⊢
    simp only [real_inner_comm y x] at hxy hyx ⊢
    linarith
  have hcs := real_inner_le_norm (c - d) (x - y)
  by_cases hzero : ‖x - y‖ = 0
  · rw [hzero]
    exact norm_nonneg _
  have hpos : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  apply (mul_le_mul_right hpos).mp
  nlinarith [hi, hcs]

theorem isProx_unique {C : Set E} {f : E → ℝ} {c x y : E}
    (hf : ConvexOn ℝ C f) (hx : IsProx C f c x) (hy : IsProx C f c y) : x = y := by
  have hn := norm_sub_le_of_supports (supports_of_isProx hf hx) (supports_of_isProx hf hy)
  simp only [sub_self, norm_zero] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

theorem lipschitz_prox {C : Set E} {f : E → ℝ} {p : E → E}
    (hf : ConvexOn ℝ C f) (hp : ∀ c, IsProx C f c (p c)) : LipschitzWith 1 p := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
    norm_sub_le_of_supports (supports_of_isProx hf (hp c)) (supports_of_isProx hf (hp d))

theorem continuous_prox {C : Set E} {f : E → ℝ} {p : E → E}
    (hf : ConvexOn ℝ C f) (hp : ∀ c, IsProx C f c (p c)) : Continuous p :=
  (lipschitz_prox hf hp).continuous

/-- The standard ADMM update; only the multiplier step is relaxed. -/
noncomputable def admmMap (pf pg : E → E) (s : E × E) : E × E :=
  let x := pf (s.1 - s.2)
  let z' := pg (x + s.2)
  (z', s.2 + (7 / 4 : ℝ) • (x - z'))

theorem continuous_admmMap {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c)) :
    Continuous (admmMap pf pg) := by
  have hcf := continuous_prox hf hpf
  have hcg := continuous_prox hg hpg
  unfold admmMap
  fun_prop

/-- A saddle pair for the original sum objective and equality constraint. -/
def IsSaddle (C D : Set E) (f g : E → ℝ) (z u : E) : Prop :=
  Supports C f z (-u) ∧ Supports D g z u

theorem admmMap_fixed_of_saddle {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    {z u : E} (hs : IsSaddle C D f g z u) : admmMap pf pg (z, u) = (z, u) := by
  have hfx : pf (z - u) = z := by
    apply isProx_unique hf (hpf (z - u))
    apply isProx_of_supports
    simpa only [sub_sub_cancel_left] using hs.1
  have hgz : pg (z + u) = z := by
    apply isProx_unique hg (hpg (z + u))
    apply isProx_of_supports
    simpa only [add_sub_cancel_left] using hs.2
  simp only [admmMap, hfx, hgz, sub_self, smul_zero, add_zero]

theorem saddle_of_admmMap_fixed {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    {z u : E} (hs : admmMap pf pg (z, u) = (z, u)) : IsSaddle C D f g z u := by
  have hz : pg (pf (z - u) + u) = z := congrArg Prod.fst hs
  have hu : u + (7 / 4 : ℝ) • (pf (z - u) - pg (pf (z - u) + u)) = u :=
    congrArg Prod.snd hs
  rw [hz] at hu
  have hx : pf (z - u) = z := by
    have ht : (7 / 4 : ℝ) • (pf (z - u) - z) = 0 := add_left_cancel (hu.trans (add_zero u).symm)
    have hd : pf (z - u) - z = 0 := (smul_eq_zero.mp ht).resolve_left (by norm_num)
    exact sub_eq_zero.mp hd
  constructor
  · have h := supports_of_isProx hf (hpf (z - u))
    rw [hx] at h
    simpa only [sub_sub_cancel_left] using h
  · have h := supports_of_isProx hg (hpg (pf (z - u) + u))
    rw [hz, hx] at h
    simpa only [add_sub_cancel_left] using h

theorem admmMap_fixed_iff_saddle {C D : Set E} {f g : E → ℝ} {pf pg : E → E}
    (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ D g)
    (hpf : ∀ c, IsProx C f c (pf c)) (hpg : ∀ c, IsProx D g c (pg c))
    {z u : E} : admmMap pf pg (z, u) = (z, u) ↔ IsSaddle C D f g z u :=
  ⟨saddle_of_admmMap_fixed hf hg hpf hpg, admmMap_fixed_of_saddle hf hg hpf hpg⟩

end ADMM74
