module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push

@[expose] public section

open scoped BigOperators
open Module Submodule

namespace MathAndTheory.Gyires.RankTwo

variable {ι : Type*} [Fintype ι]

lemma independent_rows_of_distinct (A : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ j, A i j = 1) (r₀ r₁ : ι) (hne : A r₀ ≠ A r₁) :
    LinearIndepOn ℝ id ({A r₀, A r₁} : Set (ι → ℝ)) := by
  have hzero : A r₀ ≠ 0 := by
    intro h
    have hr := hrow r₀
    rw [h] at hr
    simp at hr
  apply linearIndepOn_id_pair hzero
  intro a ha
  have hsum := congrArg (fun v : ι → ℝ => ∑ j, v j) ha
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hrow, mul_one] at hsum
  apply hne
  simpa [hsum] using ha

/-- Two distinct stochastic rows span every row when the matrix rank is at most two. -/
theorem exists_affine_row_coordinates (A : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ j, A i j = 1) (hrank : A.rank ≤ 2)
    (r₀ r₁ : ι) (hne : A r₀ ≠ A r₁) :
    ∃ lam : ι → ℝ, ∀ i, A i = lam i • A r₁ + (1 - lam i) • A r₀ := by
  classical
  have hind := independent_rows_of_distinct A hrow r₁ r₀ hne.symm
  have hdim : finrank ℝ (span ℝ ({A r₁, A r₀} : Set (ι → ℝ))) = 2 := by
    rw [finrank_span_set_eq_ncard hind, Set.ncard_pair hne.symm]
  have hle : span ℝ ({A r₁, A r₀} : Set (ι → ℝ)) ≤
      span ℝ (Set.range A.row) := by
    apply span_mono
    intro v hv
    rcases hv with rfl | hv
    · exact ⟨r₁, rfl⟩
    · have hv' : v = A r₀ := Set.mem_singleton_iff.mp hv
      subst v
      exact ⟨r₀, rfl⟩
  have hspans : span ℝ ({A r₁, A r₀} : Set (ι → ℝ)) =
      span ℝ (Set.range A.row) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [hdim, ← A.rank_eq_finrank_span_row]
    exact hrank
  have hcoeff (i : ι) : ∃ a b : ℝ, a • A r₁ + b • A r₀ = A i := by
    apply Submodule.mem_span_pair.mp
    rw [hspans]
    exact subset_span ⟨i, rfl⟩
  choose a b hab using hcoeff
  refine ⟨a, ?_⟩
  intro i
  have hsum := congrArg (fun v : ι → ℝ => ∑ j, v j) (hab i)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hrow, mul_one] at hsum
  have hb : b i = 1 - a i := by linarith
  rw [← hb]
  exact (hab i).symm

theorem exists_endpoint_rows (A : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ j, A i j = 1) (hrank : A.rank ≤ 2)
    (r₀ r₁ : ι) (hne : A r₀ ≠ A r₁) :
    ∃ (lo hi : ι) (x : ι → ℝ),
      (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ x lo = 0 ∧ x hi = 1 ∧
      ∀ i, A i = x i • A hi + (1 - x i) • A lo := by
  classical
  let : Nonempty ι := ⟨r₀⟩
  obtain ⟨lam, hlam⟩ := exists_affine_row_coordinates A hrow hrank r₀ r₁ hne
  obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ lam Finset.univ_nonempty
  obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ lam Finset.univ_nonempty
  have hbounds (i : ι) : lam lo ≤ lam i ∧ lam i ≤ lam hi :=
    ⟨hlo i (Finset.mem_univ i), hhi i (Finset.mem_univ i)⟩
  have hgap : 0 < lam hi - lam lo := by
    have hle := (hbounds hi).1
    have hne' : lam hi ≠ lam lo := by
      intro h
      have heq (i : ι) : lam i = lam lo := by
        have hb := hbounds i
        linarith
      apply hne
      calc
        A r₀ = lam r₀ • A r₁ + (1-lam r₀) • A r₀ := hlam r₀
        _ = lam r₁ • A r₁ + (1-lam r₁) • A r₀ := by rw [heq r₀, heq r₁]
        _ = A r₁ := (hlam r₁).symm
    exact sub_pos.mpr (lt_of_le_of_ne hle (Ne.symm hne'))
  let x : ι → ℝ := fun i => (lam i - lam lo) / (lam hi - lam lo)
  have hx (i : ι) : 0 ≤ x i ∧ x i ≤ 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr (hbounds i).1) hgap.le, ?_⟩
    apply (div_le_one hgap).mpr
    linarith [(hbounds i).2]
  refine ⟨lo, hi, x, hx, ?_, ?_, ?_⟩
  · simp [x]
  · simp [x, ne_of_gt hgap]
  · intro i
    rw [hlam i, hlam hi, hlam lo]
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, x]
    field_simp [ne_of_gt hgap]
    ring

end MathAndTheory.Gyires.RankTwo
