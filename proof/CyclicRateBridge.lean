module
public import PermutationCompat
public import CyclicMultiTilt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

/-!
Rate-level matrix identities, using u_i=a_i^2 and v_i=b_i^2.
This is a finite-matrix bridge only. Stochastic identification and the final
skewness inequality are not asserted by this file.
-/

open scoped BigOperators
open Equiv

namespace UnicyclicDeterminant

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def ringMatrix (σ : Perm ι) (d f g : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (if i = j then d j else 0) +
    (if i = σ j then f j else 0) + (if j = σ i then g i else 0)

omit [Fintype ι] [DecidableEq ι] in
theorem ringMatrix_support [Fintype ι] [DecidableEq ι] (σ : Perm ι) (d f g : ι → ℝ) :
    ∀ i j, i ≠ j → i ≠ σ j → i ≠ σ⁻¹ j → ringMatrix σ d f g i j = 0 := by
  intro i j hij hf hb
  have hb' : j ≠ σ i := by
    intro h
    apply hb
    simpa using (congrArg (fun k => σ⁻¹ k) h).symm
  simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, ringMatrix, hij, hf, hb']

theorem ringMatrix_forward (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (d f g : ι → ℝ) (j : ι) :
    ringMatrix σ d f g (σ j) j = f j := by
  simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, ringMatrix, cycle_no_fixed σ hc hn j, (cycle_no_two σ hc hn j).symm]

theorem ringMatrix_backward (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (d f g : ι → ℝ) (j : ι) :
    ringMatrix σ d f g (σ⁻¹ j) j = g (σ⁻¹ j) := by
  simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, ringMatrix, cycle_no_fixed σ⁻¹ hc.inv hn j,
    (cycle_forward_ne_backward σ hc hn j).symm]

theorem signed_negative_product (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (f : ι → ℝ) (i : ι) :
    ((Perm.sign σ : ℤ) : ℝ) * (∏ j, -f j) = -(∏ j, f j) := by
  rw [cycle_sign σ hc hn i, Finset.prod_neg]
  simp only [Finset.card_univ]
  rw [neg_mul, ← mul_assoc, ← mul_pow]
  norm_num

theorem balanced_ring_eq_multitilt (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (d a b : ι → ℝ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    cycleTilt (ringMatrix σ d (fun i => -(a i)^2) (fun i => -(b i)^2))
      σ (fun i => b i / a i) =
    ringMatrix σ d (fun i => -a i * b i) (fun i => -a i * b i) := by
  ext i j
  by_cases hf : i = σ j
  · subst i
    simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, cycleTilt, ringMatrix, cycle_no_fixed σ hc hn j,
      (cycle_no_two σ hc hn j).symm]
    field_simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, ha, hb] <;> ring
  by_cases hr : j = σ i
  · subst j
    simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, cycleTilt, ringMatrix, (cycle_no_fixed σ hc hn i).symm,
      (cycle_no_two σ hc hn i).symm, hf]
    field_simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, ha, hb] <;> ring
  · simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, cycleTilt, ringMatrix, hf, hr]

theorem balanced_ring_determinant_shift (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (d a b : ι → ℝ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (i : ι) :
    (ringMatrix σ d (fun i => -a i * b i) (fun i => -a i * b i)).det =
      (ringMatrix σ d (fun i => -(a i)^2) (fun i => -(b i)^2)).det +
        ((∏ j, a j) - ∏ j, b j)^2 := by
  have hq : ∀ j, b j / a j ≠ 0 := fun j => div_ne_zero (hb j) (ha j)
  have hap : (∏ j, a j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => ha j)
  have hbp : (∏ j, b j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hb j)
  let A := ringMatrix σ d (fun i => -(a i)^2) (fun i => -(b i)^2)
  have hf : ((Perm.sign σ : ℤ) : ℝ) * (∏ j, A (σ j) j) = -(∏ j, a j)^2 := by
    simp only [A, ringMatrix_forward σ hc hn]
    rw [signed_negative_product σ hc hn (fun j => (a j)^2) i, ← Finset.prod_pow]
  have hr : ((Perm.sign σ⁻¹ : ℤ) : ℝ) * (∏ j, A (σ⁻¹ j) j) = -(∏ j, b j)^2 := by
    simp only [A, ringMatrix_backward σ hc hn]
    rw [signed_negative_product σ⁻¹ hc.inv hn (fun j => (b (σ⁻¹ j))^2) i,
      Equiv.prod_comp σ⁻¹ (fun j => (b j)^2), Finset.prod_pow]
  rw [← balanced_ring_eq_multitilt σ hc hn d a b ha hb]
  rw [cyclic_determinant_multitilt A σ hc hn
    (ringMatrix_support σ d (fun i => -(a i)^2) (fun i => -(b i)^2))
    (fun i => b i / a i) hq i]
  rw [mul_assoc, hf, mul_assoc, hr, Finset.prod_div_distrib]
  field_simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, hap, hbp]
  ring

def cycleGradient (σ : Perm ι) (a b : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (if i = j then a j else 0) -
    (if i = σ⁻¹ j then b (σ⁻¹ j) else 0)

theorem cycleGradient_eq_bidiagonal (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (a b : ι → ℝ) :
    cycleGradient σ a b = cyclicBidiagonal σ⁻¹ a (fun j => b (σ⁻¹ j)) := by
  ext i j
  by_cases h : i = j
  · subst i
    simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, cycleGradient, cyclicBidiagonal, (cycle_no_fixed σ⁻¹ hc.inv hn j).symm]
  · by_cases h' : i = σ⁻¹ j <;>
      simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, cycleGradient, cyclicBidiagonal, h, h', cycle_no_fixed σ⁻¹ hc.inv hn j]

theorem cycleGradient_gram_posDef (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (a b : ι → ℝ) (i : ι)
    (hab : (∏ j, a j) ≠ ∏ j, b j) :
    ((cycleGradient σ a b).transpose * cycleGradient σ a b).PosDef := by
  rw [cycleGradient_eq_bidiagonal σ hc hn a b]
  apply cyclic_gram_posDef σ⁻¹ hc.inv hn a (fun j => b (σ⁻¹ j)) i
  simpa [Equiv.prod_comp] using hab

theorem cycleGradient_gram_entry (σ : Perm ι) (a b : ι → ℝ) (i j : ι) :
    ((cycleGradient σ a b).transpose * cycleGradient σ a b) i j =
      ((if i = j then a i * a j else 0) -
        (if i = σ⁻¹ j then a i * b (σ⁻¹ j) else 0)) -
      ((if σ⁻¹ i = j then b (σ⁻¹ i) * a j else 0) -
        (if σ⁻¹ i = σ⁻¹ j then b (σ⁻¹ i) * b (σ⁻¹ j) else 0)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cycleGradient,
    sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [eq_comm]
  ring

theorem cycleGradient_gram_eq (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (a b : ι → ℝ) :
    (cycleGradient σ a b).transpose * cycleGradient σ a b =
      ringMatrix σ (fun j => (a j)^2 + (b (σ⁻¹ j))^2)
        (fun j => -a j * b j) (fun j => -a j * b j) := by
  ext i j
  rw [cycleGradient_gram_entry]
  by_cases hij : i = j
  · subst i
    simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, ringMatrix, (cycle_no_fixed σ hc hn j).symm,
      cycle_no_fixed σ⁻¹ hc.inv hn j, (cycle_no_fixed σ⁻¹ hc.inv hn j).symm] <;> ring
  by_cases hf : i = σ j
  · subst i
    simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, ringMatrix, cycle_no_fixed σ hc hn j,
      (cycle_no_two σ hc hn j).symm, cycle_forward_ne_backward σ hc hn j,
      (cycle_no_fixed σ⁻¹ hc.inv hn j).symm] <;> ring
  by_cases hr : j = σ i
  · subst j
    simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, ringMatrix, (cycle_no_fixed σ hc hn i).symm,
      (cycle_no_two σ hc hn i).symm, (cycle_forward_ne_backward σ hc hn i).symm,
      cycle_no_fixed σ⁻¹ hc.inv hn i]
  · have hinv1 : i ≠ σ⁻¹ j := by
      intro h
      apply hr
      simpa using (congrArg σ h).symm
    have hinv2 : σ⁻¹ i ≠ j := by
      intro h
      apply hf
      simpa using congrArg σ h
    have hinv3 : σ⁻¹ i ≠ σ⁻¹ j := fun h => hij ((σ⁻¹).injective h)
    simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, ringMatrix, hij, hf, hr, hinv1, hinv2, hinv3]

theorem shifted_gram_eq_ring (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (a b : ι → ℝ) (s : ℝ) :
    s • (1 : Matrix ι ι ℝ) + (cycleGradient σ a b).transpose * cycleGradient σ a b =
      ringMatrix σ (fun j => s + (a j)^2 + (b (σ⁻¹ j))^2)
        (fun j => -a j * b j) (fun j => -a j * b j) := by
  rw [cycleGradient_gram_eq σ hc hn a b]
  ext i j
  by_cases h : i = j
  · subst i
    simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, ringMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      (cycle_no_fixed σ hc hn j).symm] <;> ring
  · simp [-Perm.coe_inv, UnicyclicPerm.inv_apply_apply, UnicyclicPerm.apply_inv_apply, ringMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, h]

theorem squared_rate_shifted_gram_determinant (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι))
    (hn : 3 ≤ Fintype.card ι) (a b : ι → ℝ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (i : ι) (s : ℝ) :
    (s • (1 : Matrix ι ι ℝ) +
      (cycleGradient σ a b).transpose * cycleGradient σ a b).det =
      (ringMatrix σ (fun j => s + (a j)^2 + (b (σ⁻¹ j))^2)
        (fun j => -(a j)^2) (fun j => -(b j)^2)).det +
          ((∏ j, a j) - ∏ j, b j)^2 := by
  rw [shifted_gram_eq_ring σ hc hn a b s]
  exact balanced_ring_determinant_shift σ hc hn
    (fun j => s + (a j)^2 + (b (σ⁻¹ j))^2) a b ha hb i

theorem ringMatrix_column_sum (σ : Perm ι) (d f g : ι → ℝ) (j : ι) :
    (∑ i, ringMatrix σ d f g i j) = d j + f j + g (σ⁻¹ j) := by
  have hrev (i : ι) : j = σ i ↔ i = σ⁻¹ j := by
    constructor
    · intro h
      simpa using (congrArg (fun k => σ⁻¹ k) h).symm
    · intro h
      simpa using (congrArg σ h).symm
  simp only [ringMatrix, Finset.sum_add_distrib, hrev,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem squared_rate_det_zero (σ : Perm ι) (a b : ι → ℝ) (i : ι) :
    (ringMatrix σ (fun j => (a j)^2 + (b (σ⁻¹ j))^2)
      (fun j => -(a j)^2) (fun j => -(b j)^2)).det = 0 := by
  let A := ringMatrix σ (fun j => (a j)^2 + (b (σ⁻¹ j))^2)
    (fun j => -(a j)^2) (fun j => -(b j)^2)
  change A.det = 0
  by_contra hd
  have hv : Matrix.vecMul (fun _ : ι => (1 : ℝ)) A = 0 := by
    ext j
    simp only [Matrix.vecMul, dotProduct, one_mul, Pi.zero_apply]
    change (∑ k, ringMatrix σ (fun j => (a j)^2 + (b (σ⁻¹ j))^2)
      (fun j => -(a j)^2) (fun j => -(b j)^2) k j) = 0
    rw [ringMatrix_column_sum] <;> ring
  have hz := Matrix.eq_zero_of_vecMul_eq_zero hd hv
  have hi := congrFun hz i
  norm_num at hi

#print axioms balanced_ring_determinant_shift
#print axioms cycleGradient_gram_posDef
#print axioms squared_rate_shifted_gram_determinant
#print axioms squared_rate_det_zero

end

end UnicyclicDeterminant
