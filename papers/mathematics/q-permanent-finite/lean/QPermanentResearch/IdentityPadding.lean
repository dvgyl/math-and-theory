import QPermanentResearch.RationalReduction
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Fin

/-!
Adding an independent scalar coordinate preserves the genuine inversion
q-permanent up to that scalar. Iterating a unit scalar gives identity-block
extensions in every larger dimension. All results in this module are generic;
the concrete witness uses them in Witness896.
-/

open scoped BigOperators
namespace QPermanentResearch

/-- The ordered block diagonal matrix `diag(c,A)`, with the new coordinate first. -/
def scalarBorder {R : Type*} [Zero R] {n : ℕ}
    (c : R) (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  fun i j => Fin.cases (Fin.cases c (fun _ => 0) j)
    (fun i => Fin.cases 0 (fun j => A i j) j) i

@[simp] theorem scalarBorder_zero_zero {R : Type*} [Zero R] {n : ℕ}
    (c : R) (A : Matrix (Fin n) (Fin n) R) : scalarBorder c A 0 0 = c := rfl

@[simp] theorem scalarBorder_zero_succ {R : Type*} [Zero R] {n : ℕ}
    (c : R) (A : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    scalarBorder c A 0 j.succ = 0 := rfl

@[simp] theorem scalarBorder_succ_zero {R : Type*} [Zero R] {n : ℕ}
    (c : R) (A : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    scalarBorder c A i.succ 0 = 0 := rfl

@[simp] theorem scalarBorder_succ_succ {R : Type*} [Zero R] {n : ℕ}
    (c : R) (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    scalarBorder c A i.succ j.succ = A i j := rfl

theorem inversionCount_eq_double_sum {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    inversionCount σ = ∑ i : Fin n, ∑ j : Fin n,
      if i < j ∧ σ j < σ i then (1 : ℕ) else 0 := by
  classical
  calc
    inversionCount σ = ∑ p : Fin n × Fin n,
        if p.1 < p.2 ∧ σ p.2 < σ p.1 then (1 : ℕ) else 0 := by
      simp [inversionCount]
    _ = _ := Fintype.sum_prod_type _

/-- Fixing a new first coordinate creates no inversions. -/
theorem inversionCount_scalarBorderPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    inversionCount (Equiv.Perm.decomposeFin.symm (0, σ)) = inversionCount σ := by
  classical
  rw [inversionCount_eq_double_sum, inversionCount_eq_double_sum]
  rw [Fin.sum_univ_succ]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero, Fin.not_lt_zero, and_false,
    ite_false, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  simp

/-- An isolated first coordinate contributes exactly its diagonal entry. -/
theorem qPermanent_scalarBorder {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (c q : R) :
    qPermanent (scalarBorder c A) q = c * qPermanent A q := by
  classical
  unfold qPermanent
  rw [Finset.univ_perm_fin_succ, Finset.sum_map]
  simp only [Equiv.coe_toEmbedding]
  rw [Fintype.sum_prod_type]
  rw [Fin.sum_univ_succ]
  have hz (i : Fin n) :
      (∑ σ : Equiv.Perm (Fin n),
        q ^ inversionCount (Equiv.Perm.decomposeFin.symm (i.succ, σ)) *
          ∏ j : Fin (n+1), scalarBorder c A j
            (Equiv.Perm.decomposeFin.symm (i.succ, σ) j)) = 0 := by
    apply Finset.sum_eq_zero
    intro σ _
    rw [Fin.prod_univ_succ]
    simp
  simp only [hz, Finset.sum_const_zero, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [inversionCount_scalarBorderPerm, Fin.prod_univ_succ]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero, scalarBorder_zero_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
    scalarBorder_succ_succ]
  ring

theorem qPermanentDerivative_scalarBorder {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (c q : ℝ) :
    qPermanentDerivative (scalarBorder c A) q = c * qPermanentDerivative A q := by
  have hf : qPermanent (scalarBorder c A) = fun r => c * qPermanent A r :=
    funext (qPermanent_scalarBorder A c)
  have h := qPermanent_hasDerivAt (scalarBorder c A) q
  rw [hf] at h
  exact h.unique ((qPermanent_hasDerivAt A q).const_mul c)

theorem scalarBorder_isHermitian {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hA : A.IsHermitian) :
    (scalarBorder c A).IsHermitian := by
  change (scalarBorder c A).conjTranspose = scalarBorder c A
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [Matrix.conjTranspose_apply, scalarBorder_zero_zero,
      scalarBorder_zero_succ, scalarBorder_succ_zero, scalarBorder_succ_succ,
      star_zero, star_trivial, hA.apply]
  exact hA.apply _ _

/-- The quadratic form splits into the new scalar square and the old form. -/
theorem scalarBorder_quadratic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin (n+1) → ℝ) :
    dotProduct (star x) ((scalarBorder c A).mulVec x) =
      c * (x 0)^2 + dotProduct (star (fun i : Fin n => x i.succ))
        (A.mulVec (fun i : Fin n => x i.succ)) := by
  classical
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_succ,
    scalarBorder_zero_zero, scalarBorder_zero_succ, scalarBorder_succ_zero,
    scalarBorder_succ_succ, zero_mul, add_zero, zero_add, Finset.sum_const_zero,
    Pi.star_apply, star_trivial]
  ring

theorem scalarBorder_posSemidef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hA : A.PosSemidef) (hc : 0 ≤ c) : (scalarBorder c A).PosSemidef := by
  refine ⟨scalarBorder_isHermitian A c hA.1, ?_⟩
  intro x
  rw [scalarBorder_quadratic]
  exact add_nonneg (mul_nonneg hc (sq_nonneg _)) (hA.2 _)

theorem scalarBorder_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hA : A.PosDef) (hc : 0 < c) : (scalarBorder c A).PosDef := by
  refine ⟨scalarBorder_isHermitian A c hA.1, ?_⟩
  intro x hx
  rw [scalarBorder_quadratic]
  by_cases ht : (fun i : Fin n => x i.succ) = 0
  · have h0 : x 0 ≠ 0 := by
      intro h0
      apply hx
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact h0
      · exact congrFun ht j
    simp only [ht, star_zero, Matrix.mulVec_zero, dotProduct_zero, add_zero]
    exact mul_pos hc (sq_pos_of_ne_zero h0)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hc.le (sq_nonneg _)) (hA.2 _ ht)

@[simp] theorem rationalMatrixCast_scalarBorder {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) :
    rationalMatrixCast (scalarBorder c A) =
      scalarBorder (c : ℝ) (rationalMatrixCast A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [rationalMatrixCast, scalarBorder]

/-- Adjoin `k` independent unit coordinates before the original ordered matrix. -/
def identityPadding {R : Type*} [Zero R] [One R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : (k : ℕ) → Matrix (Fin (n+k)) (Fin (n+k)) R
  | 0 => A
  | k+1 => scalarBorder 1 (identityPadding A k)

@[simp] theorem qPermanent_identityPadding {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (k : ℕ) (q : R) :
    qPermanent (identityPadding A k) q = qPermanent A q := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [identityPadding, qPermanent_scalarBorder, one_mul] using ih

@[simp] theorem qPermanentDerivative_identityPadding {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (q : ℝ) :
    qPermanentDerivative (identityPadding A k) q = qPermanentDerivative A q := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [identityPadding, qPermanentDerivative_scalarBorder, one_mul] using ih

theorem identityPadding_posSemidef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (k : ℕ) :
    (identityPadding A k).PosSemidef := by
  induction k with
  | zero => exact hA
  | succ k ih => exact scalarBorder_posSemidef _ _ ih zero_le_one

theorem identityPadding_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (k : ℕ) :
    (identityPadding A k).PosDef := by
  induction k with
  | zero => exact hA
  | succ k ih => exact scalarBorder_posDef _ _ ih zero_lt_one

@[simp] theorem rationalMatrixCast_identityPadding {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) :
    rationalMatrixCast (identityPadding A k) =
      identityPadding (rationalMatrixCast A) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [identityPadding, rationalMatrixCast_scalarBorder, Rat.cast_one, ih]

/-- The explicit identity extension preserves positive definiteness and the
same strict comparison at the same two parameters. -/
theorem rational_posDef_decrease_identityPadding {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (rationalMatrixCast A).PosDef)
    (q₁ q₂ : ℚ)
    (hdec : qPermanent (rationalMatrixCast A) (q₂ : ℝ) <
      qPermanent (rationalMatrixCast A) (q₁ : ℝ)) (k : ℕ) :
    (rationalMatrixCast (identityPadding A k)).PosDef ∧
      qPermanent (rationalMatrixCast (identityPadding A k)) (q₂ : ℝ) <
        qPermanent (rationalMatrixCast (identityPadding A k)) (q₁ : ℝ) := by
  rw [rationalMatrixCast_identityPadding]
  exact ⟨identityPadding_posDef _ hA k, by simpa only [qPermanent_identityPadding] using hdec⟩

end QPermanentResearch
