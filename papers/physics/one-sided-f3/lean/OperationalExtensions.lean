import ThreeDimensional
import RootExtremizers
import Mathlib.Analysis.Convex.Basic

/-! Exact radius-constrained optimization, quantitative certificates, and
convex postselection sublevel sets. These are mathematical extensions of the
original optimization result, not assumptions about quantum filters. The
physical interpretation is established in the accompanying quantum modules
and manuscript. -/

noncomputable section
open scoped BigOperators
namespace FilteredF3

section Radius
variable {ι : Type*} [Fintype ι]

theorem radiusSq_scale (R : ℝ) (x : ι → ℝ) :
    radiusSq (fun i => R * x i) = R ^ 2 * radiusSq x := by
  simp only [radiusSq, mul_pow, Finset.mul_sum]

theorem diagObjective_scale (τ R : ℝ) (h g x : ι → ℝ) :
    diagObjective τ h g (fun i => R * x i) =
      diagObjective τ (fun i => R ^ 2 * h i) (fun i => R * g i) x := by
  unfold diagObjective
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

variable [DecidableEq ι] [Nonempty ι]

/-- An unconditional algebraic maximum formula on a ball of arbitrary positive
radius. In the canonical quantum state this is the success-probability frontier. -/
theorem exact_positive_radius (τ R : ℝ) (h g : ι → ℝ) (hR : 0 < R) :
    IsGreatest {v : ℝ | ∃ x : ι → ℝ, radiusSq x ≤ R ^ 2 ∧
        diagObjective τ h g x = v}
      (secularValue τ (fun i => R ^ 2 * h i) (fun i => R * g i)
        (max 0 (largestRealRoot (fun i => R ^ 2 * h i) (fun i => R * g i)))) := by
  have hm := closed_form_diagonal τ (fun i => R ^ 2 * h i) (fun i => R * g i)
  constructor
  · obtain ⟨x, hx, hv⟩ := hm.1
    refine ⟨fun i => R * x i, ?_, ?_⟩
    · rw [radiusSq_scale]
      nlinarith [sq_nonneg R]
    · rw [diagObjective_scale]
      exact hv
  · rintro v ⟨x, hx, rfl⟩
    let y : ι → ℝ := fun i => x i / R
    have hxy : (fun i => R * y i) = x := by
      funext i
      dsimp [y]
      field_simp
    have hy : radiusSq y ≤ 1 := by
      have he := radiusSq_scale R y
      rw [hxy] at he
      have hp : 0 < R ^ 2 := sq_pos_of_pos hR
      nlinarith
    have he := diagObjective_scale τ R h g y
    rw [hxy] at he
    rw [he]
    exact hm.2 ⟨y, hy, rfl⟩

theorem canonical_probability_radius (p r : ℝ) (hp : 0 < p) :
    p * (1 + r) ≤ 1 ↔ r ≤ (1 - p) / p := by
  rw [le_div_iff₀ hp]
  constructor <;> intro h <;> nlinarith

end Radius

section Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Coercivity of the exact certificate controls distance to its unique
optimizer quantitatively. -/
theorem coercive_gap (τ μ m : ℝ) (g p x : E) (H : E →ₗ[ℝ] E)
    (hsym : ∀ u v, inner (𝕜 := ℝ) u (H v) = inner (𝕜 := ℝ) v (H u))
    (hstation : H p = μ • p - g) (hμ : 0 ≤ μ)
    (hcoercive : ∀ y, m * inner (𝕜 := ℝ) y y ≤
      inner (𝕜 := ℝ) y (μ • y - H y))
    (hx : inner (𝕜 := ℝ) x x ≤ 1) :
    m * inner (𝕜 := ℝ) (x-p) (x-p) ≤
      (τ+μ+inner (𝕜 := ℝ) g p) - objective τ g H x := by
  have he := exact_gap τ μ g p x H hsym hstation
  have hc := hcoercive (x-p)
  have hn : 0 ≤ μ * (1-inner (𝕜 := ℝ) x x) :=
    mul_nonneg hμ (sub_nonneg.mpr hx)
  linarith

theorem near_optimal_distance (τ μ m ε : ℝ) (g p x : E) (H : E →ₗ[ℝ] E)
    (hsym : ∀ u v, inner (𝕜 := ℝ) u (H v) = inner (𝕜 := ℝ) v (H u))
    (hstation : H p = μ • p - g) (hμ : 0 ≤ μ) (hm : 0 < m)
    (hcoercive : ∀ y, m * inner (𝕜 := ℝ) y y ≤
      inner (𝕜 := ℝ) y (μ • y - H y))
    (hx : inner (𝕜 := ℝ) x x ≤ 1)
    (hε : (τ+μ+inner (𝕜 := ℝ) g p)-objective τ g H x ≤ ε) :
    inner (𝕜 := ℝ) (x-p) (x-p) ≤ ε/m := by
  apply (le_div_iff₀ hm).mpr
  have hc := coercive_gap τ μ m g p x H hsym hstation hμ hcoercive hx
  nlinarith

/-- Positive-multiplier near-extremizers must approach the sphere. -/
theorem near_optimal_boundary (τ μ ε : ℝ) (g p x : E) (H : E →ₗ[ℝ] E)
    (hsym : ∀ u v, inner (𝕜 := ℝ) u (H v) = inner (𝕜 := ℝ) v (H u))
    (hstation : H p = μ • p - g) (hμ : 0 < μ)
    (hpsd : ∀ y, 0 ≤ inner (𝕜 := ℝ) y (μ • y-H y))
    (hε : (τ+μ+inner (𝕜 := ℝ) g p)-objective τ g H x ≤ ε) :
    1-inner (𝕜 := ℝ) x x ≤ ε/μ := by
  apply (le_div_iff₀ hμ).mpr
  have he := exact_gap τ μ g p x H hsym hstation
  have hn := hpsd (x-p)
  nlinarith

theorem effect_condition_ratio (μ ε r : ℝ) (hμ : 0 < μ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hgap : μ*(1-r^2) ≤ ε) :
    (1-r)/(1+r) ≤ ε/μ := by
  have hp : 0 < 1+r := by linarith
  have hsq : r^2 ≤ 1 := by nlinarith
  have hbase : (1-r)/(1+r) ≤ 1-r^2 := by
    apply (div_le_iff₀ hp).mpr
    have hn := mul_nonneg (sub_nonneg.mpr hr1) (show 0 ≤ r^2+2*r by nlinarith)
    nlinarith
  apply hbase.trans
  apply (le_div_iff₀ hμ).mpr
  nlinarith

end Stability

section Postselection
variable {X E : Type*}
variable [AddCommGroup X] [Module ℝ X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A conic numerator/success sublevel condition is preserved by positive
mixing, including zero-success terms. -/
theorem postselection_mixture_bound (v a b p q : ℝ) (u w : E)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : ‖u‖ ≤ v*p) (hw : ‖w‖ ≤ v*q) :
    ‖a • u+b • w‖ ≤ v*(a*p+b*q) := by
  calc
    ‖a • u+b • w‖ ≤ ‖a • u‖+‖b • w‖ := norm_add_le _ _
    _ = a*‖u‖+b*‖w‖ := by simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ a*(v*p)+b*(v*q) := add_le_add (mul_le_mul_of_nonneg_left hu ha)
      (mul_le_mul_of_nonneg_left hw hb)
    _ = v*(a*p+b*q) := by ring

/-- Intersecting all filter inequalities gives a convex sublevel set. This
abstract linear-map theorem is the quasiconvexity mechanism for filtered F3. -/
theorem convex_postselection_sublevel {κ : Type*}
    (N : κ → X →ₗ[ℝ] E) (P : κ → X →ₗ[ℝ] ℝ) (v : ℝ) :
    Convex ℝ {x : X | ∀ k, ‖N k x‖ ≤ v * P k x} := by
  intro x hx y hy a b ha hb hab k
  simp only [map_add,map_smul,smul_eq_mul]
  exact postselection_mixture_bound v a b (P k x) (P k y) (N k x) (N k y) ha hb (hx k) (hy k)

end Postselection
end FilteredF3
