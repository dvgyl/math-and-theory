import CyclicRateBridge
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Perm.Fin

/-!
The finite-matrix bridge stated with arbitrary strictly positive original
clockwise and anticlockwise rates, rather than assumed spectral data.
The stationary-current and cumulant identification is a separate obligation.
-/

open scoped BigOperators
open Equiv

namespace UnicyclicDeterminant

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rateMatrix (σ : Perm ι) (u v : ι → ℝ) (s : ℝ) : Matrix ι ι ℝ :=
  ringMatrix σ (fun j => s + u j + v (σ⁻¹ j)) (fun j => -u j) (fun j => -v j)

def rateGradient (σ : Perm ι) (u v : ι → ℝ) : Matrix ι ι ℝ :=
  cycleGradient σ (fun j => Real.sqrt (u j)) (fun j => Real.sqrt (v j))

def rateGram (σ : Perm ι) (u v : ι → ℝ) : Matrix ι ι ℝ :=
  (rateGradient σ u v).transpose * rateGradient σ u v

omit [Fintype ι] [DecidableEq ι] in
theorem sqrt_product_square [Fintype ι] [DecidableEq ι] (u : ι → ℝ) (hu : ∀ j, 0 ≤ u j) :
    (∏ j, Real.sqrt (u j))^2 = ∏ j, u j := by
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  exact Real.sq_sqrt (hu j)

theorem rateGram_posDef (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (u v : ι → ℝ)
    (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j)
    (hUV : (∏ j, u j) ≠ ∏ j, v j) (i : ι) :
    (rateGram σ u v).PosDef := by
  unfold rateGram rateGradient
  apply cycleGradient_gram_posDef σ hc hn
    (fun j => Real.sqrt (u j)) (fun j => Real.sqrt (v j)) i
  intro h
  apply hUV
  have hh := congrArg (fun x : ℝ => x^2) h
  dsimp only at hh
  rw [sqrt_product_square u (fun j => (hu j).le),
    sqrt_product_square v (fun j => (hv j).le)] at hh
  exact hh

theorem rateGram_shifted_determinant (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (u v : ι → ℝ)
    (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j) (i : ι) (s : ℝ) :
    (s • (1 : Matrix ι ι ℝ) + rateGram σ u v).det =
      (rateMatrix σ u v s).det +
        ((∏ j, Real.sqrt (u j)) - ∏ j, Real.sqrt (v j))^2 := by
  have ha : ∀ j, Real.sqrt (u j) ≠ 0 := fun j => (Real.sqrt_pos.mpr (hu j)).ne'
  have hb : ∀ j, Real.sqrt (v j) ≠ 0 := fun j => (Real.sqrt_pos.mpr (hv j)).ne'
  have hh := squared_rate_shifted_gram_determinant σ hc hn
    (fun j => Real.sqrt (u j)) (fun j => Real.sqrt (v j)) ha hb i s
  have hsqu : ∀ j, (Real.sqrt (u j))^2 = u j := fun j => Real.sq_sqrt (hu j).le
  have hsqv : ∀ j, (Real.sqrt (v j))^2 = v j := fun j => Real.sq_sqrt (hv j).le
  simpa only [rateGram, rateGradient, rateMatrix, hsqu, hsqv] using hh

theorem rateMatrix_det_zero (σ : Perm ι) (u v : ι → ℝ)
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) (i : ι) :
    (rateMatrix σ u v 0).det = 0 := by
  have hh := squared_rate_det_zero σ
    (fun j => Real.sqrt (u j)) (fun j => Real.sqrt (v j)) i
  have hsqu : ∀ j, (Real.sqrt (u j))^2 = u j := fun j => Real.sq_sqrt (hu j)
  have hsqv : ∀ j, (Real.sqrt (v j))^2 = v j := fun j => Real.sq_sqrt (hv j)
  simpa only [rateMatrix, zero_add, hsqu, hsqv] using hh

omit [Fintype ι] [DecidableEq ι] in
theorem rateMatrix_add_scalar [Fintype ι] [DecidableEq ι] (σ : Perm ι) (u v : ι → ℝ) (s : ℝ) :
    s • (1 : Matrix ι ι ℝ) + rateMatrix σ u v 0 = rateMatrix σ u v s := by
  ext i j
  by_cases h : i = j <;>
    simp [rateMatrix, ringMatrix, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, h] ; ring

theorem rateMatrix_determinant_tilt (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (u v : ι → ℝ) (i : ι) (s q : ℝ) (hq : q ≠ 0) :
    (edgeTilt (rateMatrix σ u v s) i (σ i) q).det =
      (rateMatrix σ u v s).det - (∏ j, u j) * (q - 1) -
        (∏ j, v j) * (q⁻¹ - 1) := by
  have hf : ((Perm.sign σ : ℤ) : ℝ) *
      (∏ j, rateMatrix σ u v s (σ j) j) = -(∏ j, u j) := by
    simp only [rateMatrix, ringMatrix_forward σ hc hn]
    exact signed_negative_product σ hc hn u i
  have hr : ((Perm.sign σ⁻¹ : ℤ) : ℝ) *
      (∏ j, rateMatrix σ u v s (σ⁻¹ j) j) = -(∏ j, v j) := by
    simp only [rateMatrix, ringMatrix_backward σ hc hn]
    rw [signed_negative_product σ⁻¹ hc.inv hn (fun j => v (σ⁻¹ j)) i,
      Equiv.prod_comp σ⁻¹ v]
  rw [cyclic_determinant_tilt (rateMatrix σ u v s) σ hc hn
    (ringMatrix_support σ (fun j => s + u j + v (σ⁻¹ j))
      (fun j => -u j) (fun j => -v j)) i q hq]
  rw [mul_assoc, hf, mul_assoc, hr]
  ring

theorem finRotate_isCycleOn (n : ℕ) (hn : 2 ≤ n) :
    (finRotate n).IsCycleOn (Finset.univ : Finset (Fin n)) := by
  simpa only [← Perm.coe_support_eq_set_support, support_finRotate_of_le hn]
    using (isCycle_finRotate_of_le hn).isCycleOn

theorem fin_ring_rateGram_posDef (n : ℕ) (hn : 3 ≤ n) (u v : Fin n → ℝ)
    (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j)
    (hUV : (∏ j, u j) ≠ ∏ j, v j) :
    (rateGram (finRotate n) u v).PosDef := by
  apply rateGram_posDef (finRotate n) (finRotate_isCycleOn n (by omega))
    (by simpa using hn) u v hu hv hUV ⟨0, by omega⟩

theorem fin_ring_shifted_determinant (n : ℕ) (hn : 3 ≤ n) (u v : Fin n → ℝ)
    (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j) (s : ℝ) :
    (s • (1 : Matrix (Fin n) (Fin n) ℝ) + rateGram (finRotate n) u v).det =
      (rateMatrix (finRotate n) u v s).det +
        ((∏ j, Real.sqrt (u j)) - ∏ j, Real.sqrt (v j))^2 := by
  exact rateGram_shifted_determinant (finRotate n)
    (finRotate_isCycleOn n (by omega)) (by simpa using hn) u v hu hv ⟨0, by omega⟩ s

#print axioms rateGram_posDef
#print axioms rateGram_shifted_determinant
#print axioms rateMatrix_det_zero
#print axioms rateMatrix_determinant_tilt
#print axioms fin_ring_rateGram_posDef
#print axioms fin_ring_shifted_determinant

end

end UnicyclicDeterminant
