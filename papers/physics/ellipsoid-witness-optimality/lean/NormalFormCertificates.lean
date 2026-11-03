import EllipsoidCounterexample
import Mathlib.Tactic.FieldSimp

/-!
# Exact positive-remainder certificates for both Lorentz normal forms

These are concrete complex 4-by-4 matrix theorems, not normal-form existence
assumptions. The external theorem reducing an arbitrary witness to these forms
is not formalized in this module.
-/

namespace EllipsoidNormalForms

noncomputable section
open Matrix Complex EllipsoidCounterexample
open scoped ComplexConjugate

/-- `w I + x XX + y YY + z ZZ`, without trace normalization. -/
def bell (w x y z : ℝ) : M4 :=
  !![((w + z : ℝ) : ℂ), 0, 0, ((x - y : ℝ) : ℂ);
     0, ((w - z : ℝ) : ℂ), ((x + y : ℝ) : ℂ), 0;
     0, ((x + y : ℝ) : ℂ), ((w - z : ℝ) : ℂ), 0;
     ((x - y : ℝ) : ℂ), 0, 0, ((w + z : ℝ) : ℂ)]

lemma bell_hermitian (w x y z : ℝ) : Hermitian (bell w x y z) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [bell]

lemma bell_quad (w x y z : ℝ) (v : V4) :
    quad (bell w x y z) v =
      (w + z + x - y) / 2 * Complex.normSq (v 0 + v 3) +
      (w + z - x + y) / 2 * Complex.normSq (v 0 - v 3) +
      (w - z + x + y) / 2 * Complex.normSq (v 1 + v 2) +
      (w - z - x - y) / 2 * Complex.normSq (v 1 - v 2) := by
  simp [quad, bell, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem bell_psd_of_eigenvalues (w x y z : ℝ)
    (h₁ : 0 ≤ w + z + x - y) (h₂ : 0 ≤ w + z - x + y)
    (h₃ : 0 ≤ w - z + x + y) (h₄ : 0 ≤ w - z - x - y) :
    PSD (bell w x y z) := by
  refine ⟨bell_hermitian w x y z, ?_⟩
  intro v
  rw [bell_quad]
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (div_nonneg h₁ (by norm_num)) (Complex.normSq_nonneg _))
    (mul_nonneg (div_nonneg h₂ (by norm_num)) (Complex.normSq_nonneg _)))
    (mul_nonneg (div_nonneg h₃ (by norm_num)) (Complex.normSq_nonneg _)))
    (mul_nonneg (div_nonneg h₄ (by norm_num)) (Complex.normSq_nonneg _))

theorem bell_psd_iff (w x y z : ℝ) :
    PSD (bell w x y z) ↔
      0 ≤ w + z + x - y ∧ 0 ≤ w + z - x + y ∧
      0 ≤ w - z + x + y ∧ 0 ≤ w - z - x - y := by
  constructor
  · intro h
    have h₁ := h.2 ![1, 0, 0, 1]
    have h₂ := h.2 ![1, 0, 0, -1]
    have h₃ := h.2 ![0, 1, 1, 0]
    have h₄ := h.2 ![0, 1, -1, 0]
    simp [bell_quad, Complex.normSq_apply] at h₁ h₂ h₃ h₄
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact bell_psd_of_eigenvalues w x y z h₁ h₂ h₃ h₄

lemma quad_real_smul (r : ℝ) (A : M4) (v : V4) :
    quad ((r : ℂ) • A) v = r * quad A v := by
  simp [quad, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]
  ring

lemma psd_real_smul {r : ℝ} (hr : 0 ≤ r) {A : M4} (hA : PSD A) :
    PSD ((r : ℂ) • A) := by
  refine ⟨?_, ?_⟩
  · intro i j
    simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
      using congrArg (fun z : ℂ => (r : ℂ) * z) (hA.1 i j)
  · intro v
    rw [quad_real_smul]
    exact mul_nonneg hr (hA.2 v)

/-- The positive matrix in the diagonal Lorentz-normal-form argument. -/
def ordinaryR (w s₁ s₂ : ℝ) : M4 := bell w s₁ s₂ (-(s₁ + s₂ - w))

theorem ordinary_residual_psd {w s₁ s₂ : ℝ}
    (h₁ : s₁ ≤ w) (h₂ : s₂ ≤ w) (hs : 0 ≤ s₁ + s₂) :
    PSD (ordinaryR w s₁ s₂) := by
  apply bell_psd_of_eigenvalues <;> linarith

theorem ordinary_identity (w s₁ s₂ s₃ : ℝ) :
    ((s₁ + s₂ - w + s₃ : ℝ) : ℂ) • bell w s₁ s₂ (-s₃) -
      ((s₁ + s₂ - w - s₃ : ℝ) : ℂ) • bell w s₁ s₂ s₃ =
    ((2 * s₃ : ℝ) : ℂ) • ordinaryR w s₁ s₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bell, ordinaryR] <;> push_cast <;> ring

theorem ordinary_positive_certificate {w s₁ s₂ s₃ : ℝ}
    (h₁ : s₁ ≤ w) (h₂ : s₂ ≤ w) (hs : 0 ≤ s₁ + s₂)
    (hs₃ : 0 ≤ s₃) :
    PSD (((s₁ + s₂ - w + s₃ : ℝ) : ℂ) • bell w s₁ s₂ (-s₃) -
      ((s₁ + s₂ - w - s₃ : ℝ) : ℂ) • bell w s₁ s₂ s₃) := by
  rw [ordinary_identity]
  exact psd_real_smul (by linarith) (ordinary_residual_psd h₁ h₂ hs)

theorem ordinary_coefficient_bounds {w s₁ s₂ s₃ : ℝ}
    (hs₃ : 0 < s₃) (hwit : s₃ < s₁ + s₂ - w) :
    0 < (s₁ + s₂ - w - s₃) / (s₁ + s₂ - w + s₃) ∧
    (s₁ + s₂ - w - s₃) / (s₁ + s₂ - w + s₃) < 1 := by
  have hd : 0 < s₁ + s₂ - w + s₃ := by linarith
  exact ⟨div_pos (by linarith) hd, (div_lt_one hd).2 (by linarith)⟩

/-- Both local marginals are retained in the extraordinary form. -/
def extraordinary (w k u s : ℝ) : M4 :=
  !![((2 * w : ℝ) : ℂ), 0, 0, ((u - s : ℝ) : ℂ);
     0, ((4 * k : ℝ) : ℂ), ((u + s : ℝ) : ℂ), 0;
     0, ((u + s : ℝ) : ℂ), 0, 0;
     ((u - s : ℝ) : ℂ), 0, 0, ((2 * w : ℝ) : ℂ)]

def extraordinaryR (w k u : ℝ) : M4 := extraordinary w k u (-u)

lemma extraordinaryR_hermitian (w k u : ℝ) : Hermitian (extraordinaryR w k u) := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [extraordinaryR, extraordinary]

lemma extraordinaryR_quad (w k u : ℝ) (v : V4) :
    quad (extraordinaryR w k u) v =
      (w + u) * Complex.normSq (v 0 + v 3) +
      (w - u) * Complex.normSq (v 0 - v 3) +
      4 * k * Complex.normSq (v 1) := by
  simp [quad, extraordinaryR, extraordinary, Fin.sum_univ_succ,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem extraordinary_residual_psd {w k u : ℝ}
    (h₁ : 0 ≤ w + u) (h₂ : u ≤ w) (hk : 0 ≤ k) :
    PSD (extraordinaryR w k u) := by
  refine ⟨extraordinaryR_hermitian w k u, ?_⟩
  intro v
  rw [extraordinaryR_quad]
  exact add_nonneg (add_nonneg
    (mul_nonneg h₁ (Complex.normSq_nonneg _))
    (mul_nonneg (sub_nonneg.mpr h₂) (Complex.normSq_nonneg _)))
    (mul_nonneg (mul_nonneg (by norm_num) hk) (Complex.normSq_nonneg _))

theorem extraordinary_identity (w k u s : ℝ) :
    ((u + s : ℝ) : ℂ) • extraordinary w k u (-s) -
      ((u - s : ℝ) : ℂ) • extraordinary w k u s =
    ((2 * s : ℝ) : ℂ) • extraordinaryR w k u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [extraordinary, extraordinaryR] <;> push_cast <;> ring

theorem extraordinary_positive_certificate {w k u s : ℝ}
    (h₁ : 0 ≤ w + u) (h₂ : u ≤ w) (hk : 0 ≤ k) (hs : 0 ≤ s) :
    PSD (((u + s : ℝ) : ℂ) • extraordinary w k u (-s) -
      ((u - s : ℝ) : ℂ) • extraordinary w k u s) := by
  rw [extraordinary_identity]
  exact psd_real_smul (by linarith) (extraordinary_residual_psd h₁ h₂ hk)

theorem extraordinary_coefficient_bounds {u s : ℝ} (hs : 0 < s) (hu : s < u) :
    0 < (u - s) / (u + s) ∧ (u - s) / (u + s) < 1 := by
  have hd : 0 < u + s := by linarith
  exact ⟨div_pos (by linarith) hd, (div_lt_one hd).2 (by linarith)⟩

/-- Exact coercivity at the centre of the open counterexample neighbourhood. -/
theorem interior_remainder_quad (v : V4) :
    quad (bell (1/4) (3/16) (3/16) (-1/16) -
      (1/2 : ℂ) • bell (1/4) (3/16) (3/16) (1/16)) v =
    (1/32) * (Complex.normSq (v 0) + Complex.normSq (v 3)) +
    (13/64) * Complex.normSq (v 1 + v 2) +
    (1/64) * Complex.normSq (v 1 - v 2) := by
  simp [quad, bell, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

end
end EllipsoidNormalForms
