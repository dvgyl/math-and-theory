import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Exact weak duality for two levels of the PPT-cost coefficient hierarchy.
This file alone is an LP lemma, not the quantum result. The actual matrix
correspondence and the explicit certificate are supplied in separate files.
-/

namespace KappaCertificate

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] {K : Type*}
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def pairing (x y : ι → K) : K := ∑ i, x i * y i

def total (x : ι → K) : K := ∑ i, x i

def sandwich (T : Matrix ι ι K) (x y : ι → K) : Prop :=
  (∀ i, (T *ᵥ x) i ≤ y i) ∧ (∀ i, -(T *ᵥ x) i ≤ y i)

def feasible2 (T : Matrix ι ι K) (v s₀ s₁ : ι → K) : Prop :=
  sandwich T v s₀ ∧ sandwich T s₀ s₁ ∧ (∀ i, 0 ≤ (T *ᵥ s₁) i)

def feasible3 (T : Matrix ι ι K) (v s₀ s₁ s₂ : ι → K) : Prop :=
  sandwich T v s₀ ∧ sandwich T s₀ s₁ ∧ sandwich T s₁ s₂ ∧
    (∀ i, 0 ≤ (T *ᵥ s₂) i)

theorem sandwich_nonneg {T : Matrix ι ι K} {x y : ι → K}
    (h : sandwich T x y) : ∀ i, 0 ≤ y i := by
  intro i
  have h₁ := h.1 i
  have h₂ := h.2 i
  linarith

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem pairing_swap (x y : ι → K) : pairing x y = pairing y x := by
  simp only [pairing, mul_comm]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem pairing_add (x y z : ι → K) :
    pairing (x + y) z = pairing x z + pairing y z := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem pairing_sub (x y z : ι → K) :
    pairing (x - y) z = pairing x z - pairing y z := by
  simp [pairing, sub_mul, Finset.sum_sub_distrib]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem pairing_selfadjoint {T : Matrix ι ι K}
    (hT : ∀ i j, T i j = T j i) (x y : ι → K) :
    pairing (T *ᵥ x) y = pairing x (T *ᵥ y) := by
  simp only [pairing, Matrix.mulVec, dotProduct, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hT j i]
  ring

theorem sandwich_pairing {T : Matrix ι ι K} {x y a b : ι → K}
    (h : sandwich T x y) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    pairing (a - b) (T *ᵥ x) ≤ pairing (a + b) y := by
  apply Finset.sum_le_sum
  intro i _
  have h₁ := mul_le_mul_of_nonneg_left (h.1 i) (ha i)
  have h₂ := mul_le_mul_of_nonneg_left (h.2 i) (hb i)
  change (a i - b i) * (T *ᵥ x) i ≤ (a i + b i) * y i
  nlinarith

theorem pairing_mono {x y z : ι → K}
    (h : ∀ i, x i ≤ y i) (hz : ∀ i, 0 ≤ z i) :
    pairing x z ≤ pairing y z := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (hz i)

theorem pairing_nonneg {x y : ι → K}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) : 0 ≤ pairing x y := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hx i) (hy i)

/-- Nonnegative rational vectors give a lower bound valid for every feasible
    two-level coefficient chain, without any assumption of optimality. -/
theorem weak_duality_two {T : Matrix ι ι K}
    (hT : ∀ i j, T i j = T j i)
    {v s₀ s₁ a b c d z : ι → K}
    (hf : feasible2 T v s₀ s₁)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i)
    (hz : ∀ i, 0 ≤ z i)
    (h₀ : ∀ i, a i + b i ≤ (T *ᵥ (c - d)) i)
    (h₁ : ∀ i, c i + d i + (T *ᵥ z) i ≤ 1) :
    pairing (a - b) (T *ᵥ v) ≤ total s₁ := by
  have hs₀ := sandwich_nonneg hf.1
  have hs₁ := sandwich_nonneg hf.2.1
  have step₀ := sandwich_pairing hf.1 ha hb
  have link₀ : pairing (a + b) s₀ ≤ pairing (T *ᵥ (c - d)) s₀ :=
    pairing_mono h₀ hs₀
  have step₁ := sandwich_pairing hf.2.1 hc hd
  have link₁ : pairing (c + d) s₁ ≤
      pairing ((fun _ => 1) - T *ᵥ z) s₁ := by
    apply pairing_mono _ hs₁
    intro i
    have h := h₁ i
    change c i + d i ≤ 1 - (T *ᵥ z) i
    linarith
  have hpos := pairing_nonneg hz hf.2.2
  have heq₀ := pairing_selfadjoint hT (c - d) s₀
  have heq₁ := pairing_selfadjoint hT z s₁
  have hone : pairing (fun _ : ι => (1 : K)) s₁ = total s₁ := by
    simp [pairing, total]
  rw [pairing_sub, hone, heq₁] at link₁
  linarith

end KappaCertificate
