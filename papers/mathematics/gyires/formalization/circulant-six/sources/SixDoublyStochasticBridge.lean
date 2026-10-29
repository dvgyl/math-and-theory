import SixNormalization
namespace MathAndTheory.Gyires.CirculantSix

theorem gyires_doubly_stochastic_of_chamber_margins (hch : ChamberMargins)
    (w : Fin 6 → ℝ) (hA : matrix w ∈ doublyStochastic ℝ (Fin 6)) :
    (Nat.factorial 6 : ℝ) / 6 ^ 6 *
      ((matrix w * (matrix w).transpose).permanent +
        ((matrix w).transpose * matrix w).permanent + 2 * (matrix w * matrix w).permanent) ≤
      4 * (matrix w).permanent ^ 2 ∧
    ((Nat.factorial 6 : ℝ) / 6 ^ 6 *
      ((matrix w * (matrix w).transpose).permanent +
        ((matrix w).transpose * matrix w).permanent + 2 * (matrix w * matrix w).permanent) =
      4 * (matrix w).permanent ^ 2 ↔
        matrix w = (fun _ _ => 1 / 6 : Matrix (Fin 6) (Fin 6) ℝ)) := by
  obtain ⟨hw, hs⟩ := weights_of_doubly_stochastic w hA
  have hi := gyires_of_chamber_margins hch w hw
  have he := gyires_equality_of_chamber_margins hch w hw
  rw [constant_iff_uniform w hs, ← matrix_eq_uniform_iff] at he
  norm_num [Nat.factorial] at ⊢
  constructor
  · linarith
  · constructor
    · intro h
      apply he.mp
      linarith
    · intro h
      have hh := he.mpr h
      linarith

#print axioms gyires_doubly_stochastic_of_chamber_margins
end MathAndTheory.Gyires.CirculantSix
