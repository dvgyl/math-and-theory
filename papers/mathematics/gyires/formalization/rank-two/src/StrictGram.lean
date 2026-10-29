module

public import NormalizedPermanent
public import SecondCoefficient

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.Gyires.RankTwo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma sum_sq_pos_of_ne_zero (u : ι → ℝ) (hu : u ≠ 0) : 0 < ∑ i, (u i)^2 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    apply hu
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  have hsingle := Finset.single_le_sum (s := Finset.univ) (a := i)
    (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
  exact (sq_pos_of_ne_zero hi).trans_le hsingle

theorem centered_gram_lower_bound (hn : 0 < Fintype.card ι)
    (σ : ℝ) (hσ : 0 < σ) (u v : ι → ℝ) (hv : ∑ i, v i = 0) :
    ((Fintype.card ι).factorial : ℝ)/(Fintype.card ι : ℝ)^Fintype.card ι ≤
      ((centered (1/((Fintype.card ι : ℝ)*σ)) u v)*
        (centered (1/((Fintype.card ι : ℝ)*σ)) u v).transpose).permanent := by
  let n := Fintype.card ι
  let κ := (∑ i, (v i)^2)/((n : ℝ)*σ)
  let F (k : ℕ) := ((k.factorial : ℝ)*((n-k).factorial : ℝ)/
      ((n.factorial : ℝ)*σ^k))*(elementary u k)^2*κ^k
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hc : 0 < (n.factorial : ℝ)/(n : ℝ)^n := div_pos hfac (pow_pos hn' n)
  have hκ : 0 ≤ κ := div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    (mul_nonneg hn'.le hσ.le)
  have hF : ∀ k, 0 ≤ F k := by intro k; dsimp [F]; positivity
  have hF0 : F 0 = 1 := by
    simp [F, elementary_zero, ne_of_gt hfac]
  have hsum : 1 ≤ ∑ k ∈ Finset.range (n+1), F k := by
    rw [← hF0]
    exact Finset.single_le_sum (fun k _ => hF k) (by simp)
  have hexp := permanent_centered_gram_left_normalized (ι := ι)
    (Nat.ne_of_gt hn) σ (ne_of_gt hσ) u v hv
  dsimp only at hexp
  change _ = ∑ k ∈ Finset.range (n+1), F k at hexp
  rw [← hexp] at hsum
  simpa only [one_mul] using (le_div_iff₀ hc).mp hsum

theorem centered_gram_strict_lower_bound (hn : 2 ≤ Fintype.card ι)
    (σ : ℝ) (hσ : 0 < σ) (u v : ι → ℝ)
    (hu : ∑ i, u i = 0) (hv : ∑ i, v i = 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    ((Fintype.card ι).factorial : ℝ)/(Fintype.card ι : ℝ)^Fintype.card ι <
      ((centered (1/((Fintype.card ι : ℝ)*σ)) u v)*
        (centered (1/((Fintype.card ι : ℝ)*σ)) u v).transpose).permanent := by
  let n := Fintype.card ι
  let κ := (∑ i, (v i)^2)/((n : ℝ)*σ)
  let F (k : ℕ) := ((k.factorial : ℝ)*((n-k).factorial : ℝ)/
      ((n.factorial : ℝ)*σ^k))*(elementary u k)^2*κ^k
  have hnpos : 0 < n := by dsimp [n]; omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hc : 0 < (n.factorial : ℝ)/(n : ℝ)^n := div_pos hfac (pow_pos hn' n)
  have hκ : 0 < κ := div_pos (sum_sq_pos_of_ne_zero v hv0) (mul_pos hn' hσ)
  have he2 : elementary u 2 ≠ 0 := by
    have hs := sum_sq_pos_of_ne_zero u hu0
    rw [variance_eq_neg_two_elementary u hu] at hs
    intro he
    rw [he] at hs
    linarith
  have hF : ∀ k, 0 ≤ F k := by intro k; dsimp [F]; positivity
  have hF0 : F 0 = 1 := by simp [F, elementary_zero, ne_of_gt hfac]
  have hF2 : 0 < F 2 := by
    have hnum : (0 : ℝ) < (n-2).factorial := by exact_mod_cast Nat.factorial_pos (n-2)
    dsimp [F]
    exact mul_pos (mul_pos (div_pos (mul_pos (by norm_num) hnum)
      (mul_pos hfac (pow_pos hσ 2))) (sq_pos_of_ne_zero he2)) (pow_pos hκ 2)
  have h2 : 2 ∈ (Finset.range (n+1)).erase 0 := by
    simp only [Finset.mem_erase, Finset.mem_range]
    constructor
    · norm_num
    · dsimp [n]; omega
  have hrest : 0 < ∑ k ∈ (Finset.range (n+1)).erase 0, F k :=
    hF2.trans_le (Finset.single_le_sum (fun k _ => hF k) h2)
  have hsum : 1 < ∑ k ∈ Finset.range (n+1), F k := by
    rw [← Finset.sum_erase_add _ _ (by simp : 0 ∈ Finset.range (n+1)), hF0]
    linarith
  have hexp := permanent_centered_gram_left_normalized (ι := ι)
    (Nat.ne_of_gt hnpos) σ (ne_of_gt hσ) u v hv
  dsimp only at hexp
  change _ = ∑ k ∈ Finset.range (n+1), F k at hexp
  rw [← hexp] at hsum
  simpa only [one_mul] using (lt_div_iff₀ hc).mp hsum

end MathAndTheory.Gyires.RankTwo
