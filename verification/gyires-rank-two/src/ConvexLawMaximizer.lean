module

public import PairInterpolation

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.Gyires.RankTwo

open Bernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma convex_law_maximizer_interior_equal
    (F : (Fin (Fintype.card ι + 1) → ℝ) → ℝ) {μ : ℝ} {p : ι → ℝ}
    (hconv : ConvexOn ℝ (convexHull ℝ (law '' parameters (ι := ι) μ)) F)
    (hp : p ∈ parameters μ)
    (hmax : ∀ q ∈ parameters μ, F (law q) ≤ F (law p))
    (hsquares : ∀ q ∈ parameters μ, F (law q) = F (law p) →
      (∑ k, q k ^ 2) ≤ ∑ k, p k ^ 2) :
    ∀ i j, (0 < p i ∧ p i < 1) → (0 < p j ∧ p j < 1) → p i = p j := by
  intro i j hi hj
  by_contra hne
  have hij : i ≠ j := fun h => hne (congrArg p h)
  obtain ⟨x, y, m, α, β, hx, hy, hm, hxy, hmm, hα, hβ, hsum, hprod, hspread⟩ :=
    exists_strict_pair_interpolation hi hj hne
  let q := setPair p i j x y
  let r := setPair p i j m m
  have hq : q ∈ parameters μ := setPair_mem_parameters hp hij hx hy hxy
  have hr : r ∈ parameters μ := setPair_mem_parameters hp hij hm hm hmm
  have hmix : law p = α • law q + β • law r :=
    law_pair_interpolation p hij x y m m α β hxy hmm hsum hprod
  have hqmem : law q ∈ convexHull ℝ (law '' parameters (ι := ι) μ) :=
    subset_convexHull ℝ _ ⟨q, hq, rfl⟩
  have hrmem : law r ∈ convexHull ℝ (law '' parameters (ι := ι) μ) :=
    subset_convexHull ℝ _ ⟨r, hr, rfl⟩
  have hbound := hconv.2 hqmem hrmem hα.le hβ.le hsum
  rw [← hmix] at hbound
  simp only [smul_eq_mul] at hbound
  have hqmax := hmax q hq
  have hrmax := hmax r hr
  have heq : F (law q) = F (law p) := by
    apply le_antisymm hqmax
    have hweighted := mul_le_mul_of_nonneg_left hrmax hβ.le
    have hsum' : α * F (law p) + β * F (law p) = F (law p) := by
      rw [← add_mul, hsum, one_mul]
    have hprodle : α * F (law p) ≤ α * F (law q) := by linarith
    exact (mul_le_mul_iff_right₀ hα).mp hprodle
  have hsq := hsquares q hq heq
  dsimp [q] at hsq
  rw [sum_setPair_apply (fun z => z ^ 2) p hij] at hsq
  linarith

/-- A convex function of the law has a maximizer with equal interior parameters. -/
theorem exists_convex_law_maximizer
    (F : (Fin (Fintype.card ι + 1) → ℝ) → ℝ) (μ : ℝ)
    (hcontinuous : Continuous F)
    (hconv : ConvexOn ℝ (convexHull ℝ (law '' parameters (ι := ι) μ)) F)
    (hne : (parameters (ι := ι) μ).Nonempty) :
    ∃ p ∈ parameters (ι := ι) μ,
      (∀ q ∈ parameters μ, F (law q) ≤ F (law p)) ∧
      ∀ i j, (0 < p i ∧ p i < 1) → (0 < p j ∧ p j < 1) → p i = p j := by
  have hF : Continuous (fun p : ι → ℝ => F (law p)) := hcontinuous.comp continuous_law
  obtain ⟨p₀, hp₀, hmax₀⟩ := (isCompact_parameters μ).exists_isMaxOn hne hF.continuousOn
  let S : Set (ι → ℝ) := parameters μ ∩ {p | F (law p) = F (law p₀)}
  have hcompact : IsCompact S := (isCompact_parameters μ).inter_right
    (isClosed_eq hF continuous_const)
  have hS : S.Nonempty := ⟨p₀, hp₀, rfl⟩
  obtain ⟨p, hp, hsq⟩ := hcompact.exists_isMaxOn hS
    (show Continuous (fun p : ι → ℝ => ∑ k, p k ^ 2) by fun_prop).continuousOn
  have hmax : ∀ q ∈ parameters μ, F (law q) ≤ F (law p) := by
    intro q hq
    rw [hp.2]
    exact hmax₀ hq
  refine ⟨p, hp.1, hmax, convex_law_maximizer_interior_equal F hconv hp.1 hmax ?_⟩
  intro q hq heq
  exact hsq ⟨hq, heq.trans hp.2⟩

/-- The maximizing law is a shifted binomial law, including deterministic laws. -/
theorem exists_convex_law_binomial_maximizer
    (F : (Fin (Fintype.card ι + 1) → ℝ) → ℝ) (μ : ℝ)
    (hcontinuous : Continuous F)
    (hconv : ConvexOn ℝ (convexHull ℝ (law '' parameters (ι := ι) μ)) F)
    (hne : (parameters (ι := ι) μ).Nonempty) :
    ∃ (p : ι → ℝ) (a b : ℕ) (q : ℝ),
      p ∈ parameters μ ∧
      (∀ v ∈ parameters μ, F (law v) ≤ F (law p)) ∧
      (0 < q ∧ q < 1) ∧ a + b ≤ Fintype.card ι ∧
      μ = a + b * q ∧
      generating p = Polynomial.X ^ a * (Polynomial.C (1-q) + Polynomial.C q * Polynomial.X) ^ b := by
  obtain ⟨p, hp, hmax, hequal⟩ := exists_convex_law_maximizer F μ hcontinuous hconv hne
  have hq : ∃ q : ℝ, (0 < q ∧ q < 1) ∧
      ∀ i, (0 < p i ∧ p i < 1) → p i = q := by
    by_cases h : ∃ i, 0 < p i ∧ p i < 1
    · obtain ⟨i, hi⟩ := h
      exact ⟨p i, hi, fun j hj => hequal j i hj hi⟩
    · refine ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩
      intro i hi
      exact False.elim (h ⟨i, hi⟩)
  obtain ⟨q, hq, hconst⟩ := hq
  refine ⟨p, (ones p).card, (fractional p).card, q, hp, hmax, hq,
    profile_counts_le p, ?_, generating_of_equal_interior hp.1 q hconst⟩
  have hsum : (∑ i, p i) = μ := hp.2
  rw [← hsum]
  exact sum_of_equal_interior hp.1 q hconst

end MathAndTheory.Gyires.RankTwo
