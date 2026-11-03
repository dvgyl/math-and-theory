import TrustRegion

/-! Explicit solution branches for the finite-dimensional diagonal quadratic.
Every theorem in this file is proved by Lean's kernel. Regular and singular
multiplier hypotheses are stated openly. -/

noncomputable section
open scoped BigOperators
namespace FilteredF3
variable {ι : Type*} [Fintype ι]

/-- Secular equation: division by zero uses Lean's total field convention.
At a singular diagonal entry the hard-branch hypotheses force g i = 0. -/
def secular (h g : ι → ℝ) (μ : ℝ) : ℝ :=
  ∑ i, (g i / (μ - h i)) ^ 2

def secularPoint (h g : ι → ℝ) (μ : ℝ) : ι → ℝ :=
  fun i => g i / (μ - h i)

def secularValue (τ : ℝ) (h g : ι → ℝ) (μ : ℝ) : ℝ :=
  τ + μ + ∑ i, (g i) ^ 2 / (μ - h i)

theorem radius_secularPoint (h g : ι → ℝ) (μ : ℝ) :
    radiusSq (secularPoint h g μ) = secular h g μ := rfl

theorem diagValue_secular (τ : ℝ) (h g : ι → ℝ) (μ : ℝ) :
    diagValue τ μ g (secularPoint h g μ) = secularValue τ h g μ := by
  unfold diagValue secularPoint secularValue
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Regular-root formula. A positive definite multiplier makes the global
maximizer unique; the value is explicit in the root μ. -/
theorem regular_branch (τ μ : ℝ) (h g : ι → ℝ)
    (hμ : 0 ≤ μ) (hstrict : ∀ i, h i < μ)
    (hsec : secular h g μ = 1) :
    IsGreatest {v : ℝ | ∃ x : ι → ℝ, radiusSq x ≤ 1 ∧ diagObjective τ h g x = v}
      (secularValue τ h g μ) ∧
    ∀ x : ι → ℝ, radiusSq x ≤ 1 →
      (diagObjective τ h g x = secularValue τ h g μ ↔ x = secularPoint h g μ) := by
  have hstation : ∀ i, (μ - h i) * secularPoint h g μ i = g i := by
    intro i
    exact mul_div_cancel₀ (g i) (ne_of_gt (sub_pos.mpr (hstrict i)))
  have hp : radiusSq (secularPoint h g μ) = 1 := hsec
  have hcomp : μ * (1 - radiusSq (secularPoint h g μ)) = 0 := by rw [hp]; ring
  have hdiag : ∀ i, h i ≤ μ := fun i => (hstrict i).le
  constructor
  · rw [← diagValue_secular]
    exact diagonal_maximum τ μ h g (secularPoint h g μ) hμ hdiag hstation hp.le hcomp
  · intro x hx
    rw [← diagValue_secular]
    constructor
    · intro heq
      have heq' := (diagonal_equality_iff τ μ h g (secularPoint h g μ) x
        hμ hdiag hstation hx).mp heq
      funext i
      rcases heq'.1 i with hbad | heq''
      · exact False.elim ((ne_of_gt (hstrict i)) hbad)
      · exact heq''
    · intro heq
      subst x
      have hg := diagonal_exact_gap τ μ h g (secularPoint h g μ) (secularPoint h g μ) hstation
      simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
        Finset.sum_const_zero, zero_add] at hg
      linarith

/-- Interior (or sphere-touching) unconstrained branch: μ=0, H≤0, g lies
in the range of -H, and the minimum-norm stationary point is feasible. -/
theorem zero_branch (τ : ℝ) (h g : ι → ℝ)
    (hdiag : ∀ i, h i ≤ 0)
    (hcompat : ∀ i, h i = 0 → g i = 0)
    (hsec : secular h g 0 ≤ 1) :
    IsGreatest {v : ℝ | ∃ x : ι → ℝ, radiusSq x ≤ 1 ∧ diagObjective τ h g x = v}
      (secularValue τ h g 0) ∧
    ∀ x : ι → ℝ, radiusSq x ≤ 1 →
      (diagObjective τ h g x = secularValue τ h g 0 ↔
        ∀ i, h i = 0 ∨ x i = secularPoint h g 0 i) := by
  have hstation : ∀ i, (0 - h i) * secularPoint h g 0 i = g i := by
    intro i
    by_cases hi : h i = 0
    · simp [secularPoint, hi, hcompat i hi]
    · exact mul_div_cancel₀ (g i) (by simpa using hi)
  constructor
  · rw [← diagValue_secular]
    exact diagonal_maximum τ 0 h g (secularPoint h g 0) le_rfl hdiag hstation hsec (by ring)
  · intro x hx
    rw [← diagValue_secular, diagonal_equality_iff τ 0 h g (secularPoint h g 0) x
      le_rfl hdiag hstation hx]
    simp only [zero_mul, and_true, eq_comm (a := (0 : ℝ))]

/-- Adding a vector in the singular eigenspace preserves stationarity. -/
theorem singular_stationarity (μ : ℝ) (h g w : ι → ℝ)
    (hcompat : ∀ i, h i = μ → g i = 0)
    (hw : ∀ i, (μ - h i) * w i = 0) :
    ∀ i, (μ - h i) * (secularPoint h g μ i + w i) = g i := by
  intro i
  by_cases hi : h i = μ
  · simp [hi, hcompat i hi]
  · have hne : μ - h i ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
    have hdiv := mul_div_cancel₀ (g i) hne
    dsimp [secularPoint]
    rw [mul_add, hw i, add_zero]
    exact hdiv

/-- The Moore-Penrose stationary point is orthogonal to every null direction. -/
theorem singular_orthogonal (μ : ℝ) (h g w : ι → ℝ)
    (hw : ∀ i, (μ - h i) * w i = 0) :
    ∀ i, secularPoint h g μ i * w i = 0 := by
  intro i
  by_cases hi : h i = μ
  · simp [secularPoint, hi]
  · have hne : μ - h i ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
    have hwi : w i = 0 := (mul_eq_zero.mp (hw i)).resolve_left hne
    rw [hwi, mul_zero]

theorem radius_add_orthogonal (p w : ι → ℝ)
    (horth : ∀ i, p i * w i = 0) :
    radiusSq (fun i => p i + w i) = radiusSq p + radiusSq w := by
  unfold radiusSq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  nlinarith [horth i]

/-- Exact singular-branch formula, with arbitrary kernel correction.
This theorem includes every repeated-eigenvalue hard case. -/
theorem singular_branch (τ μ : ℝ) (h g w : ι → ℝ)
    (hμ : 0 ≤ μ) (hdiag : ∀ i, h i ≤ μ)
    (hcompat : ∀ i, h i = μ → g i = 0)
    (hw : ∀ i, (μ - h i) * w i = 0)
    (hradius : secular h g μ + radiusSq w ≤ 1)
    (hcomp : μ * (1 - (secular h g μ + radiusSq w)) = 0) :
    IsGreatest {v : ℝ | ∃ x : ι → ℝ, radiusSq x ≤ 1 ∧ diagObjective τ h g x = v}
      (secularValue τ h g μ) := by
  have hp := radius_add_orthogonal (secularPoint h g μ) w (singular_orthogonal μ h g w hw)
  rw [radius_secularPoint] at hp
  have hstation := singular_stationarity μ h g w hcompat hw
  have hvalue : diagValue τ μ g (fun i => secularPoint h g μ i + w i) =
      secularValue τ h g μ := by
    rw [← diagValue_secular]
    unfold diagValue
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hgw : g i * w i = 0 := by
      rcases mul_eq_zero.mp (hw i) with hh | hh
      · have hg := hcompat i (sub_eq_zero.mp hh).symm
        rw [hg, zero_mul]
      · rw [hh, mul_zero]
    rw [mul_add, hgw, add_zero]
  rw [← hvalue]
  apply diagonal_maximum τ μ h g (fun i => secularPoint h g μ i + w i)
    hμ hdiag hstation
  · rwa [hp]
  · rwa [hp]

/-- A concrete hard-case correction exists whenever μ is an eigenvalue and
the pseudoinverse point lies in the ball. -/
theorem hard_case_attained [DecidableEq ι] (τ μ : ℝ) (h g : ι → ℝ)
    (hμ : 0 ≤ μ) (hdiag : ∀ i, h i ≤ μ)
    (hcompat : ∀ i, h i = μ → g i = 0)
    (hsec : secular h g μ ≤ 1) (k : ι) (hk : h k = μ) :
    IsGreatest {v : ℝ | ∃ x : ι → ℝ, radiusSq x ≤ 1 ∧ diagObjective τ h g x = v}
      (secularValue τ h g μ) := by
  let w : ι → ℝ := fun i => if i = k then Real.sqrt (1 - secular h g μ) else 0
  have hw : ∀ i, (μ - h i) * w i = 0 := by
    intro i
    by_cases hi : i = k
    · subst i
      simp [w, hk]
    · simp [w, hi]
  have hr : radiusSq w = 1 - secular h g μ := by
    unfold radiusSq
    simp [w, Real.sq_sqrt (sub_nonneg.mpr hsec)]
  apply singular_branch τ μ h g w hμ hdiag hcompat hw
  · rw [hr]; linarith
  · rw [hr]; ring

end FilteredF3
