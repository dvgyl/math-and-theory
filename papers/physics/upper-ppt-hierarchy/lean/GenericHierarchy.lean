import MatrixReduction
import Mathlib.Data.Matrix.Kronecker

namespace KappaGeneric

open Matrix
open scoped BigOperators ComplexOrder Kronecker

abbrev GMatrix (Q : Type*) := Matrix (Q × Q) (Q × Q) ℂ

def gpt {Q : Type*} (X : GMatrix Q) : GMatrix Q :=
  fun a b => X (a.1,b.2) (b.1,a.2)

def gsandwich {Q : Type*} [Fintype Q] (X Y : GMatrix Q) : Prop :=
  (Y - gpt X).PosSemidef ∧ (Y + gpt X).PosSemidef

def gfeasible2 {Q : Type*} [Fintype Q] (ρ A B : GMatrix Q) : Prop :=
  gsandwich ρ A ∧ gsandwich A B ∧ (gpt B).PosSemidef

def gfeasible3 {Q : Type*} [Fintype Q] (ρ A B C : GMatrix Q) : Prop :=
  gsandwich ρ A ∧ gsandwich A B ∧ gsandwich B C ∧ (gpt C).PosSemidef

def gvalues2 {Q : Type*} [Fintype Q] (ρ : GMatrix Q) : Set ℝ :=
  {r | ∃ A B, gfeasible2 ρ A B ∧ (Matrix.trace B).re = r}

noncomputable def gkappa2 {Q : Type*} [Fintype Q] (ρ : GMatrix Q) : ℝ :=
  sInf (gvalues2 ρ)

def GState {Q : Type*} [Fintype Q] (ρ : GMatrix Q) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

@[simp] theorem gpt_gpt {Q : Type*} (X : GMatrix Q) : gpt (gpt X) = X := rfl

@[simp] theorem gpt_add {Q : Type*} (X Y : GMatrix Q) :
    gpt (X + Y) = gpt X + gpt Y := rfl

@[simp] theorem gpt_sub {Q : Type*} (X Y : GMatrix Q) :
    gpt (X - Y) = gpt X - gpt Y := rfl

@[simp] theorem trace_gpt {Q : Type*} [Fintype Q] (X : GMatrix Q) :
    Matrix.trace (gpt X) = Matrix.trace X := rfl

theorem gfeasible2_at_bits (n : ℕ) (ρ A B : BellBridge.CMatrix n) :
    gfeasible2 ρ A B ↔ KappaMatrix.feasible2 n ρ A B := Iff.rfl

theorem gfeasible3_at_bits (n : ℕ) (ρ A B C : BellBridge.CMatrix n) :
    gfeasible3 ρ A B C ↔ KappaMatrix.feasible3 n ρ A B C := Iff.rfl

theorem gkappa2_at_bits (n : ℕ) (ρ : BellBridge.CMatrix n) :
    gkappa2 ρ = KappaMatrix.kappa2 n ρ := rfl

theorem gstate_at_bits (n : ℕ) (ρ : BellBridge.CMatrix n) :
    GState ρ ↔ KappaMatrix.QuantumState n ρ := Iff.rfl

theorem gsandwich_hermitian {Q : Type*} [Fintype Q] {X Y : GMatrix Q}
    (h : gsandwich X Y) : Y.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h₁ := h.1.isHermitian.apply i j
  have h₂ := h.2.isHermitian.apply i j
  simp only [Matrix.sub_apply, Matrix.add_apply, star_sub, star_add] at h₁ h₂
  linear_combination (1 / 2 : ℂ) * h₁ + (1 / 2 : ℂ) * h₂

theorem gsandwich_psd {Q : Type*} [Fintype Q] {X Y : GMatrix Q}
    (h : gsandwich X Y) : Y.PosSemidef := by
  refine ⟨gsandwich_hermitian h, ?_⟩
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

theorem gsandwich_trace_eq_re {Q : Type*} [Fintype Q] {X Y : GMatrix Q}
    (h : gsandwich X Y) : Matrix.trace Y = ((Matrix.trace Y).re : ℂ) := by
  have him : (Matrix.trace Y).im = 0 := by
    simp only [Matrix.trace, Matrix.diag, Complex.im_sum]
    apply Finset.sum_eq_zero
    intro i _
    have hd := congrArg Complex.im ((gsandwich_hermitian h).apply i i)
    change -(Y i i).im = (Y i i).im at hd
    linarith
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using him

theorem psd_trace_nonnegative {I : Type*} [Fintype I]
    {X : Matrix I I ℂ} (h : X.PosSemidef) : 0 ≤ (Matrix.trace X).re := by
  classical
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  have hh := h.re_dotProduct_nonneg (Pi.single i 1)
  have hs : star (Pi.single i (1:ℂ) : I → ℂ) = (Pi.single i (1:ℂ) : I → ℂ) := by
    ext j
    by_cases hij : j = i <;> simp [Pi.single_apply, hij]
  rw [hs] at hh
  simpa using hh

theorem gsandwich_trace_mono {Q : Type*} [Fintype Q] {X Y : GMatrix Q}
    (h : gsandwich X Y) : (Matrix.trace X).re ≤ (Matrix.trace Y).re := by
  have hp := psd_trace_nonnegative h.1
  rw [Matrix.trace_sub, trace_gpt, Complex.sub_re] at hp
  linarith

theorem gkappa2_lower_trace {Q : Type*} [Fintype Q] (ρ : GMatrix Q)
    (hne : (gvalues2 ρ).Nonempty) : (Matrix.trace ρ).re ≤ gkappa2 ρ := by
  apply le_csInf hne
  rintro r ⟨A, B, hf, rfl⟩
  exact (gsandwich_trace_mono hf.1).trans (gsandwich_trace_mono hf.2.1)

theorem gvalues2_bounded_below {Q : Type*} [Fintype Q] (ρ : GMatrix Q) :
    BddBelow (gvalues2 ρ) := by
  refine ⟨0, ?_⟩
  rintro r ⟨A, B, hf, rfl⟩
  exact psd_trace_nonnegative (gsandwich_psd hf.2.1)

theorem gkappa2_le {Q : Type*} [Fintype Q] {ρ A B : GMatrix Q}
    (h : gfeasible2 ρ A B) : gkappa2 ρ ≤ (Matrix.trace B).re := by
  apply csInf_le (gvalues2_bounded_below ρ)
  exact ⟨A, B, h, rfl⟩

/-- Positivity of an actual Kronecker product, proved through Gram factors. -/
theorem psd_kronecker {I J : Type*} [Fintype I] [Fintype J]
    {X : Matrix I I ℂ} {Y : Matrix J J ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : (X ⊗ₖ Y).PosSemidef := by
  classical
  obtain ⟨A, rfl⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hX
  obtain ⟨B, rfl⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hY
  have ht : (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
    ext ⟨i,j⟩ ⟨k,l⟩
    simp [Matrix.conjTranspose_apply, StarMul.star_mul, mul_comm]
  rw [Matrix.mul_kronecker_mul, ← ht]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Bipartite tensor product grouped as (AA'):(BB'). -/
def btensor {Q R : Type*} (X : GMatrix Q) (Y : GMatrix R) : GMatrix (Q × R) :=
  fun a b => X (a.1.1,a.2.1) (b.1.1,b.2.1) *
    Y (a.1.2,a.2.2) (b.1.2,b.2.2)

theorem btensor_psd {Q R : Type*} [Fintype Q] [Fintype R]
    {X : GMatrix Q} {Y : GMatrix R}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : (btensor X Y).PosSemidef := by
  let f : (Q × R) × (Q × R) → (Q × Q) × (R × R) :=
    fun a => ((a.1.1,a.2.1),(a.1.2,a.2.2))
  exact (psd_kronecker hX hY).submatrix f

end KappaGeneric
