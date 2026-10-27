module

public import CenteredGram

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.Gyires.RankTwo

variable {ι : Type*} [Fintype ι]

def centerVector (p : ι → ℝ) (θ : ℝ) : ι → ℝ := fun i => p i - θ

lemma sum_centerVector (p : ι → ℝ) (θ : ℝ)
    (hmean : ∑ i, p i = (Fintype.card ι : ℝ) * θ) :
    ∑ i, centerVector p θ i = 0 := by
  simp [centerVector, Finset.sum_sub_distrib, hmean]

lemma centered_variance_eq (p : ι → ℝ) (θ : ℝ)
    (hmean : ∑ i, p i = (Fintype.card ι : ℝ) * θ) :
    (∑ i, (centerVector p θ i) ^ 2) =
      (∑ i, (p i) ^ 2) - (Fintype.card ι : ℝ) * θ ^ 2 := by
  have hterm (i : ι) : (centerVector p θ i) ^ 2 =
      (p i) ^ 2 - 2 * θ * p i + θ ^ 2 := by
    unfold centerVector
    ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, hmean]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem centered_variance_bounds (p : ι → ℝ) (θ : ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hmean : ∑ i, p i = (Fintype.card ι : ℝ) * θ) :
    0 ≤ (∑ i, (centerVector p θ i) ^ 2) ∧
      (∑ i, (centerVector p θ i) ^ 2) ≤
        (Fintype.card ι : ℝ) * (θ * (1 - θ)) := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  · rw [centered_variance_eq p θ hmean]
    have hsq : (∑ i, (p i) ^ 2) ≤ ∑ i, p i := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [mul_nonneg (hp i).1 (sub_nonneg.mpr (hp i).2)]
    rw [hmean] at hsq
    nlinarith

theorem centered_variance_ratio_bounds (hn : Fintype.card ι ≠ 0)
    (p : ι → ℝ) (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hmean : ∑ i, p i = (Fintype.card ι : ℝ) * θ) :
    0 ≤ (∑ i, (centerVector p θ i) ^ 2) /
        ((Fintype.card ι : ℝ) * (θ * (1 - θ))) ∧
      (∑ i, (centerVector p θ i) ^ 2) /
        ((Fintype.card ι : ℝ) * (θ * (1 - θ))) ≤ 1 := by
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hden : 0 < (Fintype.card ι : ℝ) * (θ * (1 - θ)) :=
    mul_pos hn' (mul_pos hθ.1 (sub_pos.mpr hθ.2))
  obtain ⟨hlo, hhi⟩ := centered_variance_bounds p θ hp hmean
  exact ⟨div_nonneg hlo hden.le, (div_le_one hden).mpr hhi⟩

omit [Fintype ι] in
lemma mixture_entry_centered (N t x y : ℝ) (hN : N ≠ 0) (ht : t ≠ 0)
    (hNt : N - t ≠ 0) :
    x * y / t + (1 - x) * (1 - y) / (N - t) =
      1 / N + (x - t / N) * (y - t / N) / (N * (t * (N - t) / N ^ 2)) := by
  field_simp [hN, ht, hNt]
  ring

lemma mixture_eq_centered (t : ℝ) (x y : ι → ℝ)
    (hn : Fintype.card ι ≠ 0) (ht : t ≠ 0) (hNt : (Fintype.card ι : ℝ) - t ≠ 0) :
    (fun i j => x i * y j / t + (1 - x i) * (1 - y j) / ((Fintype.card ι : ℝ) - t)) =
      centered (1 / ((Fintype.card ι : ℝ) *
        (t * ((Fintype.card ι : ℝ) - t) / (Fintype.card ι : ℝ) ^ 2)))
        (centerVector x (t / Fintype.card ι)) (centerVector y (t / Fintype.card ι)) := by
  have hn' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hn
  funext i j
  rw [mixture_entry_centered _ t (x i) (y j) hn' ht hNt]
  simp only [centered, perturbation, centerVector]
  ring

end MathAndTheory.Gyires.RankTwo
