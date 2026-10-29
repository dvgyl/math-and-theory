import SixPrincipal
namespace MathAndTheory.Gyires.CirculantSix
open SixCertificates

def paperMatrix (w : Fin 6 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ := fun i j => w (j - i)

example (w : Fin 6 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (Nat.factorial 6 : ℝ) * (paperMatrix w * (paperMatrix w).transpose).permanent ≤
      (6 : ℝ) ^ 6 * (paperMatrix w).permanent ^ 2 := by
  have h := strong_inequality w hw
  change (Nat.factorial 6 : ℝ) * (matrix w * (matrix w).transpose).permanent ≤
    (6 : ℝ) ^ 6 * (matrix w).permanent ^ 2
  norm_num [Nat.factorial]
  linarith

example (w : Fin 6 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (Nat.factorial 6 : ℝ) *
      ((paperMatrix w * (paperMatrix w).transpose).permanent +
        ((paperMatrix w).transpose * paperMatrix w).permanent +
        2 * (paperMatrix w * paperMatrix w).permanent) ≤
      4 * (6 : ℝ) ^ 6 * (paperMatrix w).permanent ^ 2 := by
  have h := gyires w hw
  change (Nat.factorial 6 : ℝ) *
    ((matrix w * (matrix w).transpose).permanent +
      ((matrix w).transpose * matrix w).permanent + 2 * (matrix w * matrix w).permanent) ≤
    4 * (6 : ℝ) ^ 6 * (matrix w).permanent ^ 2
  norm_num [Nat.factorial]
  linarith

example (σ : Equiv.Perm (Fin 6)) (w : Fin 6 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : Monotone (w ∘ σ)) :
    296 * (∑ i : Fin 5, (w (σ i.succ) - w (σ i.castSucc)) ^ 12) ≤
      324 * (paperMatrix w).permanent ^ 2 -
        5 * (paperMatrix w * (paperMatrix w).transpose).permanent :=
  sorted_margin σ w hw hm

example (σ : Equiv.Perm (Fin 6)) (w : Fin 6 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : Monotone (w ∘ σ)) :
    1184 * (∑ i : Fin 5, (w (σ i.succ) - w (σ i.castSucc)) ^ 12) ≤
      1296 * (paperMatrix w).permanent ^ 2 -
        5 * ((paperMatrix w * (paperMatrix w).transpose).permanent +
          ((paperMatrix w).transpose * paperMatrix w).permanent +
          2 * (paperMatrix w * paperMatrix w).permanent) :=
  sorted_gyires_margin σ w hw hm

example (w : Fin 6 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    5 * (paperMatrix w * (paperMatrix w).transpose).permanent =
      324 * (paperMatrix w).permanent ^ 2 ↔ ∃ c : ℝ, ∀ i, w i = c := by
  change 5 * (matrix w * (matrix w).transpose).permanent =
    324 * (matrix w).permanent ^ 2 ↔ ∃ c : ℝ, ∀ i, w i = c
  rw [strong_equality w hw]
  constructor
  · rintro ⟨c, h⟩
    exact ⟨c, fun i => congrFun h i⟩
  · rintro ⟨c, h⟩
    exact ⟨c, funext h⟩

#check @strong_margin
#check @sorted_margin
#check @gyires_doubly_stochastic
#print axioms strong_margin
#print axioms sorted_margin
#print axioms sorted_gyires_margin
#print axioms strong_inequality
#print axioms strong_equality
#print axioms gyires
#print axioms gyires_equality
#print axioms gyires_doubly_stochastic
#print axioms margin_coefficient_le
#print axioms normalized_margin_coefficient_le
end MathAndTheory.Gyires.CirculantSix
