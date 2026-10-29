module

public import PermanentExpansion

@[expose] public section

open scoped BigOperators
open Finset Matrix

namespace MathAndTheory.Gyires.RankTwo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The centered rank-one perturbation of the uniform matrix. -/
noncomputable def centered (s : ℝ) (u v : ι → ℝ) : Matrix ι ι ℝ :=
  perturbation (1 / Fintype.card ι) s u v

omit [DecidableEq ι] in
lemma perturbation_mul (d s e t : ℝ) (u v w z : ι → ℝ) :
    perturbation d s u v * perturbation e t w z =
      fun i j => (Fintype.card ι : ℝ) * d * e +
        s * e * u i * (∑ k, v k) + d * t * (∑ k, w k) * z j +
        s * t * (∑ k, v k * w k) * u i * z j := by
  ext i j
  simp only [Matrix.mul_apply, perturbation]
  have heq (k : ι) : (d + s * u i * v k) * (e + t * w k * z j) =
      d * e + s * e * u i * v k + d * t * w k * z j +
        s * t * (v k * w k) * u i * z j := by ring
  simp_rw [heq, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

omit [DecidableEq ι] in
theorem centered_mul (hn : Fintype.card ι ≠ 0) (s t : ℝ) (u v w z : ι → ℝ)
    (hv : ∑ i, v i = 0) (hw : ∑ i, w i = 0) :
    centered s u v * centered t w z =
      centered (s * t * (∑ i, v i * w i)) u z := by
  have hn' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hn
  unfold centered
  rw [perturbation_mul]
  ext i j
  simp only [perturbation, hv, hw, mul_zero, zero_mul, add_zero]
  field_simp [hn']

omit [DecidableEq ι] in
theorem centered_transpose (s : ℝ) (u v : ι → ℝ) :
    (centered s u v).transpose = centered s v u := by
  ext i j
  simp only [centered, perturbation, Matrix.transpose_apply]
  ring

omit [DecidableEq ι] in
theorem centered_gram_left (hn : Fintype.card ι ≠ 0) (s : ℝ) (u v : ι → ℝ)
    (hv : ∑ i, v i = 0) :
    centered s u v * (centered s u v).transpose =
      centered (s ^ 2 * (∑ i, (v i) ^ 2)) u u := by
  rw [centered_transpose, centered_mul hn s s u v v u hv hv]
  simp only [pow_two]

omit [DecidableEq ι] in
theorem centered_gram_right (hn : Fintype.card ι ≠ 0) (s : ℝ) (u v : ι → ℝ)
    (hu : ∑ i, u i = 0) :
    (centered s u v).transpose * centered s u v =
      centered (s ^ 2 * (∑ i, (u i) ^ 2)) v v := by
  rw [centered_transpose, centered_mul hn s s v u u v hu hu]
  simp only [pow_two]

omit [DecidableEq ι] in
theorem centered_square (hn : Fintype.card ι ≠ 0) (s : ℝ) (u v : ι → ℝ)
    (hu : ∑ i, u i = 0) (hv : ∑ i, v i = 0) :
    centered s u v * centered s u v =
      centered (s ^ 2 * (∑ i, v i * u i)) u v := by
  rw [centered_mul hn s s u v u v hv hu]
  simp only [pow_two]

theorem permanent_centered (s : ℝ) (u v : ι → ℝ) :
    (centered s u v).permanent =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        (k.factorial : ℝ) * ((Fintype.card ι - k).factorial : ℝ) *
          (1 / (Fintype.card ι : ℝ)) ^ (Fintype.card ι - k) * s ^ k *
            elementary u k * elementary v k :=
  permanent_perturbation _ s u v

theorem permanent_centered_gram_left (hn : Fintype.card ι ≠ 0)
    (s : ℝ) (u v : ι → ℝ) (hv : ∑ i, v i = 0) :
    (centered s u v * (centered s u v).transpose).permanent =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        (k.factorial : ℝ) * ((Fintype.card ι - k).factorial : ℝ) *
          (1 / (Fintype.card ι : ℝ)) ^ (Fintype.card ι - k) *
            (s ^ 2 * (∑ i, (v i) ^ 2)) ^ k * (elementary u k) ^ 2 := by
  rw [centered_gram_left hn s u v hv, permanent_centered]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem permanent_centered_gram_right (hn : Fintype.card ι ≠ 0)
    (s : ℝ) (u v : ι → ℝ) (hu : ∑ i, u i = 0) :
    ((centered s u v).transpose * centered s u v).permanent =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        (k.factorial : ℝ) * ((Fintype.card ι - k).factorial : ℝ) *
          (1 / (Fintype.card ι : ℝ)) ^ (Fintype.card ι - k) *
            (s ^ 2 * (∑ i, (u i) ^ 2)) ^ k * (elementary v k) ^ 2 := by
  rw [centered_gram_right hn s u v hu, permanent_centered]
  apply Finset.sum_congr rfl
  intro k _
  ring

end MathAndTheory.Gyires.RankTwo
