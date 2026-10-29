module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.Gyires.CirculantFive.Corollaries
public import MathAndTheory.Mathematics.Gyires.CirculantFive.Examples
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.LinearAlgebra.Matrix.Circulant

/-!
# The results in Mathlib's notation

Mathlib's `Matrix.circulant v` has entries `v (i - j)`, so it is the transpose of `circ v`
(`circulant_eq_transpose_circ`). This file translates the permanents of `circulant v` and of
its products into the polynomials `P5`, `gram` and `conv` of the library, translates the
hypotheses used in `Challenges/Mathematics/Gyires/CirculantFive.lean` (nonnegative entries, doubly
stochastic) into conditions on `v`, and proves the margin of `Theorems.strong_chambers` for an
arbitrary weight vector, sorted by an arbitrary permutation, together with its sharpness. It also
proves that the decomposition of a permutation in `OrderCover.order_affine_cover` is unique.
-/

@[expose] public section

set_option maxHeartbeats 400000

namespace MathAndTheory.GyiresCirculant5

open Matrix

theorem circulant_eq_transpose_circ (v : Fin 5 → ℝ) : circulant v = (circ v)ᵀ := by
  ext i j
  rfl

theorem permanent_circulant (v : Fin 5 → ℝ) : (circulant v).permanent = P5 v := by
  rw [circulant_eq_transpose_circ, permanent_transpose, permanent_circ]

theorem permanent_circulant_mul_transpose (v : Fin 5 → ℝ) :
    (circulant v * (circulant v)ᵀ).permanent = P5 (gram v) := by
  rw [circulant_eq_transpose_circ, transpose_transpose, transpose_mul_circ, permanent_circ]

theorem permanent_transpose_mul_circulant (v : Fin 5 → ℝ) :
    ((circulant v)ᵀ * circulant v).permanent = P5 (gram v) := by
  rw [circulant_eq_transpose_circ, transpose_transpose, circ_mul_transpose, permanent_circ]

theorem permanent_circulant_mul_self (v : Fin 5 → ℝ) :
    (circulant v * circulant v).permanent = P5 (conv v) := by
  rw [circulant_eq_transpose_circ, ← transpose_mul, permanent_transpose, circ_mul_self,
    permanent_circ]

/-- The denominator of Gyires's ratio for `circulant v` is the one for `circ v`. -/
theorem gyiresDenominator_circulant (v : Fin 5 → ℝ) :
    (circulant v * (circulant v)ᵀ).permanent + ((circulant v)ᵀ * circulant v).permanent +
        2 * (circulant v * circulant v).permanent = gyiresDenominator v := by
  unfold gyiresDenominator
  rw [permanent_circulant_mul_transpose, permanent_transpose_mul_circulant,
    permanent_circulant_mul_self, circ_mul_transpose, transpose_mul_circ, circ_mul_self,
    permanent_circ, permanent_circ]

theorem weights_nonneg_of_entries (v : Fin 5 → ℝ) (h : ∀ i j, 0 ≤ circulant v i j) :
    ∀ i, 0 ≤ v i := by
  intro i
  simpa using h i 0

theorem weights_of_doublyStochastic (v : Fin 5 → ℝ)
    (h : circulant v ∈ doublyStochastic ℝ (Fin 5)) :
    (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1 := by
  rw [mem_doublyStochastic_iff_sum] at h
  refine ⟨weights_nonneg_of_entries v h.1, ?_⟩
  simpa using h.2.2 0

theorem circulant_eq_const_iff (v : Fin 5 → ℝ) (c : ℝ) :
    circulant v = of (fun _ _ => c) ↔ ∀ i, v i = c := by
  constructor
  · intro h i
    simpa using congrFun (congrFun h i) 0
  · intro h
    ext i j
    simp [h]

/-- The decomposition of `order_affine_cover` is unique: a permutation of `Fin 5` is the image of
at most one canonical ordering under at most one affine map (checked by `decide`). -/
theorem order_affine_cover_unique (k k' : Fin 6) (a a' : Fin 4) (b b' : Fin 5)
    (h : ∀ i : Fin 5, affine a b (canonicalOrders k i) = affine a' b' (canonicalOrders k' i)) :
    k = k' ∧ a = a' ∧ b = b' := by
  have key : ∀ k k' : Fin 6, ∀ a a' : Fin 4, ∀ b b' : Fin 5,
      affine a b (canonicalOrders k 0) = affine a' b' (canonicalOrders k' 0) →
      affine a b (canonicalOrders k 1) = affine a' b' (canonicalOrders k' 1) →
      affine a b (canonicalOrders k 2) = affine a' b' (canonicalOrders k' 2) →
      affine a b (canonicalOrders k 3) = affine a' b' (canonicalOrders k' 3) →
      k = k' ∧ a = a' ∧ b = b' := by
    decide
  exact key k k' a a' b b' (h 0) (h 1) (h 2) (h 3)

/-- After an affine change of indices, the weights `v (σ 0), …, v (σ 4)` are placed along a
canonical ordering: `v ∘ affine a b` is `canonicalWeights k` of the successive differences. When
`v ∘ σ` is monotone and `v ≥ 0`, these differences are the smallest weight and the gaps between
consecutive sorted weights (`sortedGaps_nonneg`). -/
theorem canonical_chamber_of_monotone (v : Fin 5 → ℝ) (σ : Equiv.Perm (Fin 5)) :
    ∃ k : Fin 6, ∃ a : Fin 4, ∃ b : Fin 5,
      v ∘ affine a b = canonicalWeights k
        ![v (σ 0), v (σ 1) - v (σ 0), v (σ 2) - v (σ 1), v (σ 3) - v (σ 2),
          v (σ 4) - v (σ 3)] := by
  set z : Fin 5 → ℝ :=
    ![v (σ 0), v (σ 1) - v (σ 0), v (σ 2) - v (σ 1), v (σ 3) - v (σ 2),
      v (σ 4) - v (σ 3)] with hzdef
  have hp : ∀ i, prefixSums z i = v (σ i) := by
    intro i
    fin_cases i <;> simp [prefixSums, z]
  obtain ⟨k, a, b, hσ'⟩ := order_affine_cover σ
  refine ⟨k, a, b, ?_⟩
  funext i
  change v (affine a b i) = prefixSums z ((canonicalOrders k).symm i)
  rw [hp]
  have hi := hσ' ((canonicalOrders k).symm i)
  simp only [Equiv.apply_symm_apply] at hi
  rw [hi]

/-- If `σ` sorts the nonnegative weights `v`, the smallest weight and the gaps between consecutive
sorted weights are nonnegative. -/
theorem sortedGaps_nonneg (v : Fin 5 → ℝ) (hv : ∀ i, 0 ≤ v i)
    (σ : Equiv.Perm (Fin 5)) (hσ : Monotone (v ∘ σ)) :
    ∀ i, 0 ≤ (![v (σ 0), v (σ 1) - v (σ 0), v (σ 2) - v (σ 1), v (σ 3) - v (σ 2),
      v (σ 4) - v (σ 3)] : Fin 5 → ℝ) i := by
  intro i
  fin_cases i
  · exact hv (σ 0)
  · exact sub_nonneg.mpr (hσ (by decide : (0 : Fin 5) ≤ 1))
  · exact sub_nonneg.mpr (hσ (by decide : (1 : Fin 5) ≤ 2))
  · exact sub_nonneg.mpr (hσ (by decide : (2 : Fin 5) ≤ 3))
  · exact sub_nonneg.mpr (hσ (by decide : (3 : Fin 5) ≤ 4))

/-- The margin `484 (z₁¹⁰ + ⋯ + z₄¹⁰)` of `strong_chambers`, for every nonnegative weight
vector and every permutation that sorts it. -/
theorem strongDefect_margin (v : Fin 5 → ℝ) (hv : ∀ i, 0 ≤ v i)
    (σ : Equiv.Perm (Fin 5)) (hσ : Monotone (v ∘ σ)) :
    484 * ∑ j : Fin 4, (v (σ j.succ) - v (σ j.castSucc)) ^ 10 ≤ strongDefect v := by
  obtain ⟨k, a, b, heq⟩ := canonical_chamber_of_monotone v σ
  have h := strong_chambers k _ (sortedGaps_nonneg v hv σ hσ)
  rw [← heq, strongDefect_affine] at h
  rw [Fin.sum_univ_four]
  simpa using h

/-- The margin `484` is attained: for `v = (1, 1, 0, 0, 0)`, sorted by `i ↦ i + 2`, the tenth
powers of the gaps add up to `1` and the defect equals `484`. -/
theorem strongDefect_margin_attained :
    ∃ v : Fin 5 → ℝ, (∀ i, 0 ≤ v i) ∧ ∃ σ : Equiv.Perm (Fin 5), Monotone (v ∘ σ) ∧
      ∑ j : Fin 4, (v (σ j.succ) - v (σ j.castSucc)) ^ 10 = 1 ∧ strongDefect v = 484 := by
  refine ⟨twoSupport 1, ?_, Equiv.addRight 2, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [twoSupport]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [twoSupport]
  · rw [Fin.sum_univ_four]
    norm_num [twoSupport]
  · rw [strongDefect_twoSupport]
    norm_num

/-- No constant larger than `484` gives a valid margin. -/
theorem strongDefect_margin_sharp (K : ℝ)
    (hK : ∀ v : Fin 5 → ℝ, (∀ i, 0 ≤ v i) → ∀ σ : Equiv.Perm (Fin 5), Monotone (v ∘ σ) →
      K * ∑ j : Fin 4, (v (σ j.succ) - v (σ j.castSucc)) ^ 10 ≤ strongDefect v) :
    K ≤ 484 := by
  obtain ⟨v, hv, σ, hσ, hsum, hdef⟩ := strongDefect_margin_attained
  have h := hK v hv σ hσ
  rw [hsum, hdef] at h
  linarith

end MathAndTheory.GyiresCirculant5
