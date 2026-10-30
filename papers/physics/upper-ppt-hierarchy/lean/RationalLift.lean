import Certificate
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.NormNum

namespace KappaCertificate

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def realVec (x : ι → ℚ) : ι → ℝ := fun i => (x i : ℝ)

def realMat (T : Matrix ι ι ℚ) : Matrix ι ι ℝ := fun i j => (T i j : ℝ)

omit [Fintype ι] in
@[simp] theorem realVec_add (x y : ι → ℚ) :
    realVec (x + y) = realVec x + realVec y := by
  ext i
  simp [realVec]

omit [Fintype ι] in
@[simp] theorem realVec_sub (x y : ι → ℚ) :
    realVec (x - y) = realVec x - realVec y := by
  ext i
  simp [realVec]

@[simp] theorem realVec_mulVec (T : Matrix ι ι ℚ) (x : ι → ℚ) :
    realVec (T *ᵥ x) = realMat T *ᵥ realVec x := by
  ext i
  simp [realVec, realMat, Matrix.mulVec, dotProduct]

@[simp] theorem realVec_pairing (x y : ι → ℚ) :
    pairing (realVec x) (realVec y) = ((pairing x y : ℚ) : ℝ) := by
  simp [pairing, realVec]

@[simp] theorem realVec_total (x : ι → ℚ) :
    total (realVec x) = ((total x : ℚ) : ℝ) := by
  simp [total, realVec]

theorem sandwich_real {T : Matrix ι ι ℚ} {x y : ι → ℚ}
    (h : sandwich T x y) : sandwich (realMat T) (realVec x) (realVec y) := by
  constructor
  · intro i
    rw [← realVec_mulVec]
    simp only [realVec]
    exact_mod_cast h.1 i
  · intro i
    rw [← realVec_mulVec]
    simp only [realVec]
    exact_mod_cast h.2 i

theorem feasible3_real {T : Matrix ι ι ℚ} {v s₀ s₁ s₂ : ι → ℚ}
    (h : feasible3 T v s₀ s₁ s₂) :
    feasible3 (realMat T) (realVec v) (realVec s₀) (realVec s₁) (realVec s₂) := by
  refine ⟨sandwich_real h.1, sandwich_real h.2.1, sandwich_real h.2.2.1, ?_⟩
  intro i
  rw [← realVec_mulVec]
  simp only [realVec]
  exact_mod_cast h.2.2.2 i

theorem feasible2_real {T : Matrix ι ι ℚ} {v s₀ s₁ : ι → ℚ}
    (h : feasible2 T v s₀ s₁) :
    feasible2 (realMat T) (realVec v) (realVec s₀) (realVec s₁) := by
  refine ⟨sandwich_real h.1, sandwich_real h.2.1, ?_⟩
  intro i
  rw [← realVec_mulVec]
  simp only [realVec]
  exact_mod_cast h.2.2 i

omit [Fintype ι] in
theorem realVec_nonneg {x : ι → ℚ} (h : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ realVec x i := by
  intro i
  simp only [realVec]
  exact_mod_cast h i

omit [Fintype ι] in
theorem realMat_symmetric {T : Matrix ι ι ℚ}
    (h : ∀ i j, T i j = T j i) : ∀ i j, realMat T i j = realMat T j i := by
  intro i j
  simp only [realMat, h i j]

theorem real_dual_link_zero {T : Matrix ι ι ℚ} {a b c d : ι → ℚ}
    (h : ∀ i, a i + b i ≤ (T *ᵥ (c - d)) i) :
    ∀ i, realVec a i + realVec b i ≤
      (realMat T *ᵥ (realVec c - realVec d)) i := by
  intro i
  rw [← realVec_sub, ← realVec_mulVec]
  simp only [realVec]
  exact_mod_cast h i

theorem real_dual_link_one {T : Matrix ι ι ℚ} {c d z : ι → ℚ}
    (h : ∀ i, c i + d i + (T *ᵥ z) i ≤ 1) :
    ∀ i, realVec c i + realVec d i + (realMat T *ᵥ realVec z) i ≤ 1 := by
  intro i
  rw [← realVec_mulVec]
  simp only [realVec]
  exact_mod_cast h i

end KappaCertificate
