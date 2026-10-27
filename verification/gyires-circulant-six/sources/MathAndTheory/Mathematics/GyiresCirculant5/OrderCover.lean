module

/- See PROVENANCE.md for source attribution and modifications. -/

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases

/-!
# Ordered-gap chambers

`affine a b` is the affine map `i ↦ (a + 1) i + b` of `ZMod 5`, written on `Fin 5`, for
`a : Fin 4` and `b : Fin 5`; these are the 20 affine bijections. The six permutations
`canonicalOrders k` list the orderings `01234`, `01243`, `01324`, `01342`, `01423` and `01432`.
Every permutation of `Fin 5` is one of them followed by an affine map (`order_affine_cover`,
checked by `decide`). Consequently every nonnegative weight vector, after an affine change of
indices, has the form `canonicalWeights k z` with nonnegative sorted gaps `z`
(`exists_canonical_chamber`): its `j`-th smallest weight is `z 0 + ⋯ + z j`.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MathAndTheory.GyiresCirculant5

def affine (a : Fin 4) (b i : Fin 5) : Fin 5 :=
  ⟨((a.val + 1) * i.val + b.val) % 5, Nat.mod_lt _ (by decide)⟩

theorem affine_bijective (a : Fin 4) (b : Fin 5) :
    Function.Bijective (affine a b) := by
  have h : ∀ a : Fin 4, ∀ b : Fin 5, Function.Bijective (affine a b) := by
    decide
  exact h a b

def canonicalOrderFun (k : Fin 6) : Fin 5 → Fin 5 :=
  ![![0, 1, 2, 3, 4], ![0, 1, 2, 4, 3], ![0, 1, 3, 2, 4],
    ![0, 1, 3, 4, 2], ![0, 1, 4, 2, 3], ![0, 1, 4, 3, 2]] k

def canonicalOrderInvFun (k : Fin 6) : Fin 5 → Fin 5 :=
  ![![0, 1, 2, 3, 4], ![0, 1, 2, 4, 3], ![0, 1, 3, 2, 4],
    ![0, 1, 4, 2, 3], ![0, 1, 3, 4, 2], ![0, 1, 4, 3, 2]] k

def canonicalOrders (k : Fin 6) : Equiv.Perm (Fin 5) where
  toFun := canonicalOrderFun k
  invFun := canonicalOrderInvFun k
  left_inv := by
    have h : ∀ k : Fin 6, ∀ i : Fin 5,
        canonicalOrderInvFun k (canonicalOrderFun k i) = i := by decide
    exact h k
  right_inv := by
    have h : ∀ k : Fin 6, ∀ i : Fin 5,
        canonicalOrderFun k (canonicalOrderInvFun k i) = i := by decide
    exact h k

theorem order_affine_cover (σ : Equiv.Perm (Fin 5)) :
    ∃ k : Fin 6, ∃ a : Fin 4, ∃ b : Fin 5,
      ∀ i : Fin 5, σ i = affine a b (canonicalOrders k i) := by
  have h : ∀ σ : Equiv.Perm (Fin 5),
      ∃ k : Fin 6, ∃ a : Fin 4, ∃ b : Fin 5,
        ∀ i : Fin 5, σ i = affine a b (canonicalOrders k i) := by
    decide
  exact h σ

def prefixSums (z : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![z 0, z 0 + z 1, z 0 + z 1 + z 2,
    z 0 + z 1 + z 2 + z 3, z 0 + z 1 + z 2 + z 3 + z 4]

def canonicalWeights (k : Fin 6) (z : Fin 5 → ℝ) : Fin 5 → ℝ :=
  prefixSums z ∘ (canonicalOrders k).symm

theorem exists_canonical_chamber (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ k : Fin 6, ∃ a : Fin 4, ∃ b : Fin 5, ∃ z : Fin 5 → ℝ,
      (∀ i, 0 ≤ z i) ∧ w ∘ affine a b = canonicalWeights k z := by
  classical
  let σ := Tuple.sort w
  have hmono : Monotone (w ∘ σ) := Tuple.monotone_sort w
  let z : Fin 5 → ℝ :=
    ![w (σ 0), w (σ 1) - w (σ 0), w (σ 2) - w (σ 1),
      w (σ 3) - w (σ 2), w (σ 4) - w (σ 3)]
  have hz : ∀ i, 0 ≤ z i := by
    intro i
    fin_cases i
    · exact hw (σ 0)
    · exact sub_nonneg.mpr (hmono (by decide : (0 : Fin 5) ≤ 1))
    · exact sub_nonneg.mpr (hmono (by decide : (1 : Fin 5) ≤ 2))
    · exact sub_nonneg.mpr (hmono (by decide : (2 : Fin 5) ≤ 3))
    · exact sub_nonneg.mpr (hmono (by decide : (3 : Fin 5) ≤ 4))
  have hp : ∀ i, prefixSums z i = w (σ i) := by
    intro i
    fin_cases i <;> simp [prefixSums, z]
  obtain ⟨k, a, b, hσ⟩ := order_affine_cover σ
  refine ⟨k, a, b, z, hz, ?_⟩
  funext i
  change w (affine a b i) = prefixSums z ((canonicalOrders k).symm i)
  rw [hp]
  have hi := hσ ((canonicalOrders k).symm i)
  simp only [Equiv.apply_symm_apply] at hi
  rw [hi]

theorem nonneg_of_canonical_chambers
    (H : (Fin 5 → ℝ) → ℝ)
    (hinv : ∀ a b w, H (w ∘ affine a b) = H w)
    (hch : ∀ k z, (∀ i, 0 ≤ z i) → 0 ≤ H (canonicalWeights k z))
    (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) : 0 ≤ H w := by
  obtain ⟨k, a, b, z, hz, heq⟩ := exists_canonical_chamber w hw
  have h := hch k z hz
  rw [← heq, hinv] at h
  exact h

theorem prefix_constant_of_tail_zero (z : Fin 5 → ℝ)
    (hz : ∀ i : Fin 5, i ≠ 0 → z i = 0) :
    ∀ i, prefixSums z i = z 0 := by
  have h1 := hz 1 (by decide)
  have h2 := hz 2 (by decide)
  have h3 := hz 3 (by decide)
  have h4 := hz 4 (by decide)
  intro i
  fin_cases i <;> simp [prefixSums, h1, h2, h3, h4]

theorem constant_of_zero_of_canonical_chambers
    (H : (Fin 5 → ℝ) → ℝ)
    (hinv : ∀ a b w, H (w ∘ affine a b) = H w)
    (hch : ∀ k z, (∀ i, 0 ≤ z i) → H (canonicalWeights k z) = 0 →
      ∀ i : Fin 5, i ≠ 0 → z i = 0)
    (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) (hzero : H w = 0) :
    ∃ c : ℝ, ∀ i, w i = c := by
  obtain ⟨k, a, b, z, hz, heq⟩ := exists_canonical_chamber w hw
  have hcz : H (canonicalWeights k z) = 0 := by
    rw [← heq, hinv]
    exact hzero
  have htail := hch k z hz hcz
  have hconst : ∀ i, w (affine a b i) = z 0 := by
    intro i
    calc
      w (affine a b i) = canonicalWeights k z i := congrFun heq i
      _ = z 0 := prefix_constant_of_tail_zero z htail ((canonicalOrders k).symm i)
  refine ⟨z 0, ?_⟩
  intro i
  obtain ⟨j, hj⟩ := (affine_bijective a b).surjective i
  rw [← hj]
  exact hconst j

end MathAndTheory.GyiresCirculant5
