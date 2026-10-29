module

public import CenteredParameters
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.Gyires.RankTwo

lemma reciprocal_power_product (N σ : ℝ) (n k : ℕ) (hk : k ≤ n) :
    (1 / N) ^ (n-k) * (1 / (N * σ)) ^ k = 1 / (N ^ n * σ ^ k) := by
  simp only [div_pow, one_pow, mul_pow, div_mul_div_comm, one_mul]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]

lemma normalized_coefficient (n k : ℕ) (hn : n ≠ 0) (hk : k ≤ n)
    (σ e f : ℝ) (hσ : σ ≠ 0) :
    ((k.factorial : ℝ) * ((n-k).factorial : ℝ) *
      (1 / (n : ℝ)) ^ (n-k) * (1 / ((n : ℝ) * σ)) ^ k * e * f) /
        ((n.factorial : ℝ) / (n : ℝ) ^ n) =
      ((k.factorial : ℝ) * ((n-k).factorial : ℝ) /
        ((n.factorial : ℝ) * σ ^ k)) * e * f := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  calc
    _ = ((k.factorial : ℝ) * ((n-k).factorial : ℝ) *
        ((1 / (n : ℝ)) ^ (n-k) * (1 / ((n : ℝ) * σ)) ^ k) * e * f) /
          ((n.factorial : ℝ) / (n : ℝ) ^ n) := by ring
    _ = _ := by
      rw [reciprocal_power_product _ σ n k hk]
      field_simp [hn', hfac, hσ]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- This is the normalized expansion used in the rank-two inequality. -/
theorem permanent_centered_normalized (hn : Fintype.card ι ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) (u v : ι → ℝ) :
    (centered (1 / ((Fintype.card ι : ℝ) * σ)) u v).permanent /
        (((Fintype.card ι).factorial : ℝ) / (Fintype.card ι : ℝ) ^ Fintype.card ι) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        ((k.factorial : ℝ) * ((Fintype.card ι-k).factorial : ℝ) /
          (((Fintype.card ι).factorial : ℝ) * σ ^ k)) * elementary u k * elementary v k := by
  rw [permanent_centered, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  exact normalized_coefficient _ k hn (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)
    σ (elementary u k) (elementary v k) hσ

theorem permanent_centered_gram_left_normalized (hn : Fintype.card ι ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) (u v : ι → ℝ) (hv : ∑ i, v i = 0) :
    let A := centered (1 / ((Fintype.card ι : ℝ) * σ)) u v
    let κ := (∑ i, (v i) ^ 2) / ((Fintype.card ι : ℝ) * σ)
    (A * A.transpose).permanent /
        (((Fintype.card ι).factorial : ℝ) / (Fintype.card ι : ℝ) ^ Fintype.card ι) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        ((k.factorial : ℝ) * ((Fintype.card ι-k).factorial : ℝ) /
          (((Fintype.card ι).factorial : ℝ) * σ ^ k)) * (elementary u k) ^ 2 * κ ^ k := by
  dsimp only
  rw [centered_gram_left hn _ u v hv, permanent_centered, Finset.sum_div]
  have hscale : (1 / ((Fintype.card ι : ℝ) * σ)) ^ 2 * (∑ i, (v i) ^ 2) =
      (1 / ((Fintype.card ι : ℝ) * σ)) *
        ((∑ i, (v i) ^ 2) / ((Fintype.card ι : ℝ) * σ)) := by ring
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ Fintype.card ι := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  rw [hscale, mul_pow]
  calc
    _ = ((k.factorial : ℝ) * ((Fintype.card ι-k).factorial : ℝ) *
        (1 / (Fintype.card ι : ℝ)) ^ (Fintype.card ι-k) *
          (1 / ((Fintype.card ι : ℝ) * σ)) ^ k * elementary u k *
            (elementary u k * (((∑ i, (v i) ^ 2) / ((Fintype.card ι : ℝ) * σ)) ^ k))) /
        (((Fintype.card ι).factorial : ℝ) / (Fintype.card ι : ℝ) ^ Fintype.card ι) := by ring
    _ = _ := by
      rw [normalized_coefficient _ k hn hk' σ _ _ hσ]
      ring

theorem permanent_centered_gram_right_normalized (hn : Fintype.card ι ≠ 0)
    (σ : ℝ) (hσ : σ ≠ 0) (u v : ι → ℝ) (hu : ∑ i, u i = 0) :
    let A := centered (1 / ((Fintype.card ι : ℝ) * σ)) u v
    let κ := (∑ i, (u i) ^ 2) / ((Fintype.card ι : ℝ) * σ)
    (A.transpose * A).permanent /
        (((Fintype.card ι).factorial : ℝ) / (Fintype.card ι : ℝ) ^ Fintype.card ι) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        ((k.factorial : ℝ) * ((Fintype.card ι-k).factorial : ℝ) /
          (((Fintype.card ι).factorial : ℝ) * σ ^ k)) * (elementary v k) ^ 2 * κ ^ k := by
  have h := permanent_centered_gram_left_normalized hn σ hσ v u hu
  dsimp only at h ⊢
  rw [centered_transpose] at h ⊢
  exact h

end MathAndTheory.Gyires.RankTwo
