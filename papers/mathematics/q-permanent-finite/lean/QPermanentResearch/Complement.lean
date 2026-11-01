import QPermanentResearch.PairMinorIdentity
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
Complementary row/column bijections and their genuine matrix permanent.
Ported and generalized from Kitamura's Apache-2.0 ComplementPermanent.lean,
pinned commit 4200da4fc1a132d69c23fb877795b5b72089544b. No coefficient
or norm identity is postulated here.
-/

open scoped BigOperators
namespace QPermanentResearch
noncomputable section
variable {R : Type*} [CommRing R] [StarRing R]

abbrev PairComplement {n : ℕ} (i j : Fin n) := {x : Fin n // x ≠ i ∧ x ≠ j}

def restrictPair {n : ℕ} {i j k l : Fin n} (σ : Equiv.Perm (Fin n))
    (hi : σ i = k) (hj : σ j = l) : PairComplement i j ≃ PairComplement k l where
  toFun x := ⟨σ x, by
    constructor
    · intro h; exact x.property.1 (σ.injective (h.trans hi.symm))
    · intro h; exact x.property.2 (σ.injective (h.trans hj.symm))⟩
  invFun y := ⟨σ.symm y, by
    constructor
    · intro h; exact y.property.1 (by simpa [h, hi] using (σ.apply_symm_apply y).symm)
    · intro h; exact y.property.2 (by simpa [h, hj] using (σ.apply_symm_apply y).symm)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

def extendPair {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (e : PairComplement i j ≃ PairComplement k l) : Equiv.Perm (Fin n) where
  toFun x := if hi : x = i then k else if hj : x = j then l else e ⟨x, hi, hj⟩
  invFun y := if hk : y = k then i else if hl : y = l then j else e.symm ⟨y, hk, hl⟩
  left_inv x := by
    by_cases hi : x = i
    · subst x; simp
    by_cases hj : x = j
    · subst x; simp [hij.symm, hkl.symm]
    · simp only [dif_neg hi, dif_neg hj]
      have h := (e ⟨x, hi, hj⟩).property
      simp only [dif_neg h.1, dif_neg h.2]
      change (e.symm (e ⟨x, hi, hj⟩)).val = x
      simp
  right_inv y := by
    by_cases hk : y = k
    · subst y; simp
    by_cases hl : y = l
    · subst y; simp [hij.symm, hkl.symm]
    · simp only [dif_neg hk, dif_neg hl]
      have h := (e.symm ⟨y, hk, hl⟩).property
      simp only [dif_neg h.1, dif_neg h.2]
      change (e (e.symm ⟨y, hk, hl⟩)).val = y
      simp

theorem extendPair_left {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (e : PairComplement i j ≃ PairComplement k l) : extendPair hij hkl e i = k := by
  simp [extendPair]

theorem extendPair_right {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (e : PairComplement i j ≃ PairComplement k l) : extendPair hij hkl e j = l := by
  simp [extendPair, hij.symm]

theorem extendPair_complement {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l) (e : PairComplement i j ≃ PairComplement k l)
    (x : PairComplement i j) : extendPair hij hkl e x = e x := by
  simp [extendPair, x.property.1, x.property.2]

def pairMatchingEquiv {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) :
    {σ : Equiv.Perm (Fin n) // σ i = k ∧ σ j = l} ≃
      (PairComplement i j ≃ PairComplement k l) where
  toFun σ := restrictPair σ.val σ.property.1 σ.property.2
  invFun e := ⟨extendPair hij hkl e, extendPair_left hij hkl e, extendPair_right hij hkl e⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hi : x = i
    · subst x; simp [extendPair_left, σ.property.1]
    by_cases hj : x = j
    · subst x; simp [extendPair_right, σ.property.2]
    · change extendPair hij hkl (restrictPair σ.val σ.property.1 σ.property.2) x = σ.val x
      simp [extendPair, hi, hj, restrictPair]
  right_inv e := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact extendPair_complement hij hkl e x

theorem pairComplement_card {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Fintype.card (PairComplement i j) = n - 2 := by
  classical
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter fun x : Fin n => x ≠ i ∧ x ≠ j) =
      (Finset.univ.erase i).erase j := by ext; simp [and_comm]
  rw [hset, Finset.card_erase_of_mem (by simp [hij.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

def pairComplementFin {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    PairComplement i j ≃ Fin (n - 2) :=
  Fintype.equivFinOfCardEq (pairComplement_card i j hij)

def pairMatchingFinEquiv {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) :
    {σ : Equiv.Perm (Fin n) // σ i = k ∧ σ j = l} ≃ Equiv.Perm (Fin (n - 2)) :=
  (pairMatchingEquiv hij hkl).trans
    (Equiv.equivCongr (pairComplementFin i j hij) (pairComplementFin k l hkl))

theorem remainingProduct_subtype {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    remainingProduct A σ i j = ∏ x : PairComplement i j, A x (σ x) := by
  classical
  unfold remainingProduct
  exact Finset.prod_subtype _ (by intro x; simp [and_comm]) _

def complementMatrix {n d : ℕ} (V : Matrix (Fin n) (Fin d) R)
    (i j : Fin n) (hij : i ≠ j) : Matrix (Fin (n - 2)) (Fin d) R :=
  fun a c => V ((pairComplementFin i j hij).symm a) c

theorem remainingGram_matching_sum {n d : ℕ} (U W : Matrix (Fin n) (Fin d) R)
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l) :
    (∑ σ : Equiv.Perm (Fin n), if σ i = k ∧ σ j = l then
      remainingProduct (U * W.conjTranspose) σ i j else 0) =
    (complementMatrix U i j hij * (complementMatrix W k l hkl).conjTranspose).permanent := by
  classical
  rw [← Finset.sum_filter,
    Finset.sum_subtype (p := fun σ : Equiv.Perm (Fin n) => σ i = k ∧ σ j = l)
      _ (by intro σ; simp)]
  rw [← Matrix.permanent_transpose]
  unfold Matrix.permanent
  apply Fintype.sum_equiv (pairMatchingFinEquiv hij hkl)
  intro σ
  rw [remainingProduct_subtype]
  apply Fintype.prod_equiv (pairComplementFin i j hij)
  intro x
  simp [Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    complementMatrix, pairMatchingFinEquiv, pairMatchingEquiv,
    pairComplementFin, Equiv.equivCongr, restrictPair]


end
end QPermanentResearch
