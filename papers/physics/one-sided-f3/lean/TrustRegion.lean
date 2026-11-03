import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Algebraic trust-region optimality and extremizers

This module proves a full exact-gap certificate over an arbitrary real inner
product space, then constructs/checks the regular and singular diagonal secular
branches in any finite dimension. The input quadratic is explicit. The
Bloch-state reduction and the identification of a particular companion-matrix
root are separate mathematical statements and are NOT asserted by this module.
-/

noncomputable section
open scoped BigOperators

namespace FilteredF3

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Canonical one-sided-filter objective once the Bloch reduction is established. -/
def objective (τ : ℝ) (g : E) (H : E →ₗ[ℝ] E) (x : E) : ℝ :=
  τ + 2 * inner (𝕜 := ℝ) g x + inner (𝕜 := ℝ) x (H x)

/-- The exact certificate gap. No positivity or feasibility assumptions are
needed for this algebraic identity. -/
theorem exact_gap (τ μ : ℝ) (g p x : E) (H : E →ₗ[ℝ] E)
    (hsym : ∀ u v, inner (𝕜 := ℝ) u (H v) = inner (𝕜 := ℝ) v (H u))
    (hstation : H p = μ • p - g) :
    (τ + μ + inner (𝕜 := ℝ) g p) - objective τ g H x =
      inner (𝕜 := ℝ) (x - p) (μ • (x - p) - H (x - p)) +
        μ * (1 - inner (𝕜 := ℝ) x x) := by
  have hxp := hsym x p
  have hcross : inner (𝕜 := ℝ) x (H p) = μ * inner (𝕜 := ℝ) x p - inner (𝕜 := ℝ) x g := by
    rw [hstation, inner_sub_right, real_inner_smul_right]
  have hself : inner (𝕜 := ℝ) p (H p) = μ * inner (𝕜 := ℝ) p p - inner (𝕜 := ℝ) p g := by
    rw [hstation, inner_sub_right, real_inner_smul_right]
  unfold objective
  simp only [map_sub, inner_sub_left, inner_sub_right, real_inner_smul_right]
  rw [← hxp, hcross, hself]
  rw [real_inner_comm p x, real_inner_comm p g, real_inner_comm x g]
  nlinarith

/-- Every feasible point lies below the certificate value. -/
theorem global_upper_bound (τ μ : ℝ) (g p : E) (H : E →ₗ[ℝ] E)
    (hsym : ∀ u v, inner (𝕜 := ℝ) u (H v) = inner (𝕜 := ℝ) v (H u))
    (hstation : H p = μ • p - g)
    (hμ : 0 ≤ μ)
    (hpsd : ∀ y, 0 ≤ inner (𝕜 := ℝ) y (μ • y - H y))
    (x : E) (hx : inner (𝕜 := ℝ) x x ≤ 1) :
    objective τ g H x ≤ τ + μ + inner (𝕜 := ℝ) g p := by
  have hg := exact_gap τ μ g p x H hsym hstation
  have h₁ := hpsd (x - p)
  have h₂ : 0 ≤ μ * (1 - inner (𝕜 := ℝ) x x) := mul_nonneg hμ (sub_nonneg.mpr hx)
  linarith

/-- The certificate point attains the upper bound. -/
theorem value_at_certificate (τ μ : ℝ) (g p : E) (H : E →ₗ[ℝ] E)
    (hsym : ∀ u v, inner (𝕜 := ℝ) u (H v) = inner (𝕜 := ℝ) v (H u))
    (hstation : H p = μ • p - g)
    (hcomp : μ * (1 - inner (𝕜 := ℝ) p p) = 0) :
    objective τ g H p = τ + μ + inner (𝕜 := ℝ) g p := by
  have h := exact_gap τ μ g p p H hsym hstation
  simp only [sub_self, map_zero, smul_zero, inner_zero_left, zero_add] at h
  linarith

/-- A feasible certificate is a global maximizer; this is a maximum theorem,
not merely an upper bound. -/
theorem global_maximum (τ μ : ℝ) (g p : E) (H : E →ₗ[ℝ] E)
    (hsym : ∀ u v, inner (𝕜 := ℝ) u (H v) = inner (𝕜 := ℝ) v (H u))
    (hstation : H p = μ • p - g)
    (hcomp : μ * (1 - inner (𝕜 := ℝ) p p) = 0)
    (hμ : 0 ≤ μ)
    (hpsd : ∀ y, 0 ≤ inner (𝕜 := ℝ) y (μ • y - H y))
    (hp : inner (𝕜 := ℝ) p p ≤ 1) :
    IsGreatest {v : ℝ | ∃ x : E, inner (𝕜 := ℝ) x x ≤ 1 ∧ objective τ g H x = v}
      (τ + μ + inner (𝕜 := ℝ) g p) := by
  constructor
  · exact ⟨p, hp, value_at_certificate τ μ g p H hsym hstation hcomp⟩
  · rintro v ⟨x, hx, rfl⟩
    exact global_upper_bound τ μ g p H hsym hstation hμ hpsd x hx

/-- Complete equality characterization in terms of the two nonnegative gaps.
For a positive multiplier every maximizer lies on the sphere. -/
theorem equality_iff (τ μ : ℝ) (g p : E) (H : E →ₗ[ℝ] E)
    (hsym : ∀ u v, inner (𝕜 := ℝ) u (H v) = inner (𝕜 := ℝ) v (H u))
    (hstation : H p = μ • p - g)
    (hμ : 0 ≤ μ)
    (hpsd : ∀ y, 0 ≤ inner (𝕜 := ℝ) y (μ • y - H y))
    (x : E) (hx : inner (𝕜 := ℝ) x x ≤ 1) :
    objective τ g H x = τ + μ + inner (𝕜 := ℝ) g p ↔
      inner (𝕜 := ℝ) (x - p) (μ • (x - p) - H (x - p)) = 0 ∧
        μ * (1 - inner (𝕜 := ℝ) x x) = 0 := by
  have hg := exact_gap τ μ g p x H hsym hstation
  have h₁ := hpsd (x - p)
  have h₂ : 0 ≤ μ * (1 - inner (𝕜 := ℝ) x x) := mul_nonneg hμ (sub_nonneg.mpr hx)
  constructor
  · intro h
    constructor <;> linarith
  · rintro ⟨h₁', h₂'⟩
    linarith

end General

section Diagonal
variable {ι : Type*} [Fintype ι]

/-- Squared Euclidean radius, written without a type synonym. -/
def radiusSq (x : ι → ℝ) : ℝ := ∑ i, (x i) ^ 2

def diagObjective (τ : ℝ) (h g x : ι → ℝ) : ℝ :=
  τ + ∑ i, (2 * g i * x i + h i * (x i) ^ 2)

def diagValue (τ μ : ℝ) (g p : ι → ℝ) : ℝ :=
  τ + μ + ∑ i, g i * p i

/-- Coordinate exact gap. This explicitly permits repeated eigenvalues and
zero entries of the diagonal multiplier. -/
theorem diagonal_exact_gap (τ μ : ℝ) (h g p x : ι → ℝ)
    (hstation : ∀ i, (μ - h i) * p i = g i) :
    diagValue τ μ g p - diagObjective τ h g x =
      (∑ i, (μ - h i) * (x i - p i) ^ 2) + μ * (1 - radiusSq x) := by
  have heach : ∀ i,
      g i * p i - (2 * g i * x i + h i * (x i) ^ 2) =
      (μ - h i) * (x i - p i) ^ 2 - μ * (x i) ^ 2 := by
    intro i
    rw [← hstation i]
    ring
  unfold diagValue diagObjective radiusSq at *
  have hs : (∑ i, (g i * p i - (2 * g i * x i + h i * (x i) ^ 2))) =
      ∑ i, ((μ - h i) * (x i - p i) ^ 2 - μ * (x i) ^ 2) :=
    Finset.sum_congr rfl (fun i _ => heach i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simp only [Finset.sum_add_distrib]
  nlinarith

/-- Sharp global value of an explicit diagonal certificate. -/
theorem diagonal_maximum (τ μ : ℝ) (h g p : ι → ℝ)
    (hμ : 0 ≤ μ) (hdiag : ∀ i, h i ≤ μ)
    (hstation : ∀ i, (μ - h i) * p i = g i)
    (hp : radiusSq p ≤ 1) (hcomp : μ * (1 - radiusSq p) = 0) :
    IsGreatest {v : ℝ | ∃ x : ι → ℝ, radiusSq x ≤ 1 ∧ diagObjective τ h g x = v}
      (diagValue τ μ g p) := by
  have hat : diagObjective τ h g p = diagValue τ μ g p := by
    have hg := diagonal_exact_gap τ μ h g p p hstation
    simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, Finset.sum_const_zero,
      zero_add] at hg
    linarith
  constructor
  · exact ⟨p, hp, hat⟩
  · rintro v ⟨x, hx, rfl⟩
    have hg := diagonal_exact_gap τ μ h g p x hstation
    have hs : 0 ≤ ∑ i, (μ - h i) * (x i - p i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (sub_nonneg.mpr (hdiag i)) (sq_nonneg _))
    have hm : 0 ≤ μ * (1 - radiusSq x) := mul_nonneg hμ (sub_nonneg.mpr hx)
    linarith

/-- All diagonal maximizers, including singular directions, are classified. -/
theorem diagonal_equality_iff (τ μ : ℝ) (h g p x : ι → ℝ)
    (hμ : 0 ≤ μ) (hdiag : ∀ i, h i ≤ μ)
    (hstation : ∀ i, (μ - h i) * p i = g i)
    (hx : radiusSq x ≤ 1) :
    diagObjective τ h g x = diagValue τ μ g p ↔
      (∀ i, μ = h i ∨ x i = p i) ∧ μ * (1 - radiusSq x) = 0 := by
  have hg := diagonal_exact_gap τ μ h g p x hstation
  have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ (μ - h i) * (x i - p i) ^ 2 :=
    fun i _ => mul_nonneg (sub_nonneg.mpr (hdiag i)) (sq_nonneg _)
  have hs : 0 ≤ ∑ i, (μ - h i) * (x i - p i) ^ 2 := Finset.sum_nonneg hnonneg
  have hm : 0 ≤ μ * (1 - radiusSq x) := mul_nonneg hμ (sub_nonneg.mpr hx)
  constructor
  · intro heq
    have hz : (∑ i, (μ - h i) * (x i - p i) ^ 2) = 0 := by linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz
    refine ⟨?_, by linarith⟩
    intro i
    have hi := hall i (Finset.mem_univ i)
    rcases mul_eq_zero.mp hi with hd | hx'
    · exact Or.inl (sub_eq_zero.mp hd)
    · exact Or.inr (sub_eq_zero.mp (sq_eq_zero_iff.mp hx'))
  · rintro ⟨hall, hcomp'⟩
    have hz : (∑ i, (μ - h i) * (x i - p i) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rcases hall i with h₁ | h₂
      · simp [h₁]
      · simp [h₂]
    linarith

end Diagonal
end FilteredF3
