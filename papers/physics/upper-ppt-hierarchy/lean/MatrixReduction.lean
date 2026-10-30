import BellBridge
import MatrixHierarchy
import RationalLift
import Mathlib.Tactic.LinearCombination

/-!
Both directions relating the coefficient constraints to the unrestricted
matrix constraints. In particular, extracting Bell expectations works for
arbitrary complex auxiliary matrices; no Bell-diagonal assumption is imposed
on an optimizer.
-/

namespace KappaMatrix

open BellBridge Matrix
open scoped BigOperators ComplexOrder

theorem extract_sandwich (n : ℕ) {X Y : CMatrix n} (h : sandwich n X Y) :
    KappaCertificate.sandwich (KappaCertificate.realMat (T n))
      (expect n X) (expect n Y) := by
  constructor
  · intro i
    have hp := expect_nonneg n (Y - pt n X) h.1 i
    rw [expect_sub, expect_pt] at hp
    change 0 ≤ expect n Y i - transform n (expect n X) i at hp
    change transform n (expect n X) i ≤ expect n Y i
    linarith
  · intro i
    have hp := expect_nonneg n (Y + pt n X) h.2 i
    rw [expect_add, expect_pt] at hp
    change 0 ≤ expect n Y i + transform n (expect n X) i at hp
    change -transform n (expect n X) i ≤ expect n Y i
    linarith

theorem extract_two (n : ℕ) {ρ S₀ S₁ : CMatrix n}
    (h : feasible2 n ρ S₀ S₁) :
    KappaCertificate.feasible2 (KappaCertificate.realMat (T n))
      (expect n ρ) (expect n S₀) (expect n S₁) := by
  refine ⟨extract_sandwich n h.1, extract_sandwich n h.2.1, ?_⟩
  intro i
  have hp := expect_nonneg n (pt n S₁) h.2.2 i
  rw [expect_pt] at hp
  exact hp

theorem extract_three (n : ℕ) {ρ S₀ S₁ S₂ : CMatrix n}
    (h : feasible3 n ρ S₀ S₁ S₂) :
    KappaCertificate.feasible3 (KappaCertificate.realMat (T n))
      (expect n ρ) (expect n S₀) (expect n S₁) (expect n S₂) := by
  refine ⟨extract_sandwich n h.1, extract_sandwich n h.2.1,
    extract_sandwich n h.2.2.1, ?_⟩
  intro i
  have hp := expect_nonneg n (pt n S₂) h.2.2.2 i
  rw [expect_pt] at hp
  exact hp

theorem synth_sandwich (n : ℕ) {x y : BIndex n → ℝ}
    (h : KappaCertificate.sandwich (KappaCertificate.realMat (T n)) x y) :
    sandwich n (synth n x) (synth n y) := by
  constructor
  · rw [pt_synth, ← synth_sub]
    apply synth_psd
    intro i
    have hp := h.1 i
    change transform n x i ≤ y i at hp
    change 0 ≤ y i - transform n x i
    linarith
  · rw [pt_synth, ← synth_add]
    apply synth_psd
    intro i
    have hp := h.2 i
    change -transform n x i ≤ y i at hp
    change 0 ≤ y i + transform n x i
    linarith

theorem synth_two (n : ℕ) {v s₀ s₁ : BIndex n → ℝ}
    (h : KappaCertificate.feasible2 (KappaCertificate.realMat (T n)) v s₀ s₁) :
    feasible2 n (synth n v) (synth n s₀) (synth n s₁) := by
  refine ⟨synth_sandwich n h.1, synth_sandwich n h.2.1, ?_⟩
  rw [pt_synth]
  exact synth_psd n _ h.2.2

theorem synth_three (n : ℕ) {v s₀ s₁ s₂ : BIndex n → ℝ}
    (h : KappaCertificate.feasible3 (KappaCertificate.realMat (T n)) v s₀ s₁ s₂) :
    feasible3 n (synth n v) (synth n s₀) (synth n s₁) (synth n s₂) := by
  refine ⟨synth_sandwich n h.1, synth_sandwich n h.2.1,
    synth_sandwich n h.2.2.1, ?_⟩
  rw [pt_synth]
  exact synth_psd n _ h.2.2.2

theorem feasible_three_objective_nonneg (n : ℕ) {ρ S₀ S₁ S₂ : CMatrix n}
    (h : feasible3 n ρ S₀ S₁ S₂) : 0 ≤ (Matrix.trace S₂).re := by
  rw [← sum_expect]
  have hs := KappaCertificate.sandwich_nonneg (extract_three n h).2.2.1
  exact Finset.sum_nonneg fun i _ => hs i

theorem values3_bounded_below (n : ℕ) (ρ : CMatrix n) : BddBelow (values3 n ρ) := by
  refine ⟨0, ?_⟩
  rintro r ⟨S₀, S₁, S₂, h, rfl⟩
  exact feasible_three_objective_nonneg n h

/-- The sandwich conditions themselves imply Hermiticity of every auxiliary. -/
theorem sandwich_hermitian (n : ℕ) {X Y : CMatrix n}
    (h : sandwich n X Y) : Y.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h₁ := h.1.isHermitian.apply i j
  have h₂ := h.2.isHermitian.apply i j
  simp only [Matrix.sub_apply, Matrix.add_apply, star_sub, star_add] at h₁ h₂
  linear_combination (1 / 2 : ℂ) * h₁ + (1 / 2 : ℂ) * h₂

/-- PSD of the auxiliaries is a consequence, not an added restriction. -/
theorem sandwich_psd (n : ℕ) {X Y : CMatrix n}
    (h : sandwich n X Y) : Y.PosSemidef := by
  refine ⟨sandwich_hermitian n h, ?_⟩
  intro u
  have h₁ := h.1.2 u
  have h₂ := h.2.2 u
  rw [Matrix.sub_mulVec, dotProduct_sub] at h₁
  rw [Matrix.add_mulVec, dotProduct_add] at h₂
  simp only [Complex.nonneg_iff, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im] at h₁ h₂
  apply Complex.nonneg_iff.mpr
  constructor
  · linarith [h₁.1, h₂.1]
  · linarith [h₁.2, h₂.2]

theorem sandwich_trace_im (n : ℕ) {X Y : CMatrix n}
    (h : sandwich n X Y) : (Matrix.trace Y).im = 0 := by
  simp only [Matrix.trace, Matrix.diag, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hdiag := (sandwich_hermitian n h).apply i i
  have hdiagIm := congrArg Complex.im hdiag
  change -(Y i i).im = (Y i i).im at hdiagIm
  linarith

/-- Re Tr in the real SDP objective is exactly the ordinary trace. -/
theorem sandwich_trace_eq_re (n : ℕ) {X Y : CMatrix n}
    (h : sandwich n X Y) : Matrix.trace Y = ((Matrix.trace Y).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using sandwich_trace_im n h

end KappaMatrix
