module

public import AffineRows

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.Gyires.RankTwo

variable {ι : Type*} [Fintype ι]

theorem mixture_of_endpoint_rows (A : Matrix ι ι ℝ)
    (hnonneg : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1)
    (lo hi : ι) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hxlo : x lo = 0) (hxhi : x hi = 1)
    (hA : ∀ i, A i = x i • A hi + (1 - x i) • A lo) :
    ∃ (t : ℝ) (y : ι → ℝ),
      0 < t ∧ t < Fintype.card ι ∧ (∀ j, 0 ≤ y j ∧ y j ≤ 1) ∧
      (∑ i, x i) = t ∧ (∑ j, y j) = t ∧
      ∀ i j, A i j = x i * y j / t +
        (1 - x i) * (1 - y j) / ((Fintype.card ι : ℝ) - t) := by
  classical
  let t : ℝ := ∑ i, x i
  have htpos : 0 < t := by
    have hsum := Finset.single_le_sum (s := Finset.univ) (a := hi)
      (f := x) (fun i _ => (hx i).1) (Finset.mem_univ hi)
    rw [hxhi] at hsum
    dsimp [t]
    linarith
  have htlt : t < Fintype.card ι := by
    have hsum := Finset.single_le_sum (s := Finset.univ) (a := lo)
      (f := fun i => 1 - x i) (fun i _ => sub_nonneg.mpr (hx i).2) (Finset.mem_univ lo)
    simp only [hxlo, sub_zero, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
    dsimp [t]
    linarith
  have hAentry (i j : ι) : A i j = x i * A hi j + (1-x i) * A lo j := by
    exact congrFun (hA i) j
  have hcolumn (j : ι) : t * A hi j + ((Fintype.card ι : ℝ) - t) * A lo j = 1 := by
    have hsum : (∑ i, A i j) = ∑ i, (x i * A hi j + (1-x i) * A lo j) := by
      exact Finset.sum_congr rfl (fun i _ => hAentry i j)
    have hc := hcol j
    rw [hsum, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at hc
    simpa only [t, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one] using hc
  let y : ι → ℝ := fun j => t * A hi j
  have hy (j : ι) : 0 ≤ y j ∧ y j ≤ 1 := by
    refine ⟨mul_nonneg htpos.le (hnonneg hi j), ?_⟩
    have hterm := mul_nonneg (sub_pos.mpr htlt).le (hnonneg lo j)
    dsimp [y]
    linarith [hcolumn j]
  have hysum : (∑ j, y j) = t := by
    dsimp [y]
    rw [← Finset.mul_sum, hrow, mul_one]
  refine ⟨t, y, htpos, htlt, hy, rfl, hysum, ?_⟩
  intro i j
  have hcomplement : 1 - y j = ((Fintype.card ι : ℝ) - t) * A lo j := by
    dsimp [y]
    linarith [hcolumn j]
  rw [hAentry, hcomplement]
  dsimp [y]
  field_simp [ne_of_gt htpos, ne_of_gt (sub_pos.mpr htlt)]

/-- Every nonuniform doubly stochastic matrix of rank at most two has the mixture form. -/
theorem rank_two_stochastic_representation (hn : 0 < Fintype.card ι)
    (A : Matrix ι ι ℝ) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1)
    (hrank : A.rank ≤ 2) :
    A = (fun _ _ => 1 / (Fintype.card ι : ℝ)) ∨
      ∃ (t : ℝ) (x y : ι → ℝ),
        0 < t ∧ t < Fintype.card ι ∧
        (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (∀ j, 0 ≤ y j ∧ y j ≤ 1) ∧
        (∑ i, x i) = t ∧ (∑ j, y j) = t ∧
        ∀ i j, A i j = x i * y j / t +
          (1 - x i) * (1 - y j) / ((Fintype.card ι : ℝ) - t) := by
  classical
  by_cases hrows : ∀ i j, A i = A j
  · left
    have hn' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    ext i j
    have heq : (∑ k, A k j) = (Fintype.card ι : ℝ) * A i j := by
      calc
        _ = ∑ _k : ι, A i j := Finset.sum_congr rfl (fun k _ => congrFun (hrows k i) j)
        _ = _ := by simp
    have hc := hcol j
    rw [heq] at hc
    apply (eq_div_iff hn').mpr
    linarith
  · push Not at hrows
    obtain ⟨r₀, r₁, hne⟩ := hrows
    obtain ⟨lo, hi, x, hx, hxlo, hxhi, hA⟩ := exists_endpoint_rows A hrow hrank r₀ r₁ hne
    obtain ⟨t, y, ht, htn, hy, hxt, hyt, hrep⟩ :=
      mixture_of_endpoint_rows A hnonneg hrow hcol lo hi x hx hxlo hxhi hA
    exact Or.inr ⟨t, x, y, ht, htn, hx, hy, hxt, hyt, hrep⟩

end MathAndTheory.Gyires.RankTwo
