import SixPrincipalConsequences
namespace MathAndTheory.Gyires.CirculantSix
open SixCertificates

theorem constant_iff_uniform (w : Fin 6 → ℝ) (hs : ∑ i, w i = 1) :
    (∃ c : ℝ, w = fun _ => c) ↔ w = fun _ => 1 / 6 := by
  constructor
  · rintro ⟨c, rfl⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] at hs
    have hc : c = 1 / 6 := by linarith
    rw [hc]
  · intro h
    exact ⟨1 / 6, h⟩

theorem weights_of_doubly_stochastic (w : Fin 6 → ℝ)
    (hA : matrix w ∈ doublyStochastic ℝ (Fin 6)) :
    (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 := by
  rw [mem_doublyStochastic_iff_sum] at hA
  refine ⟨fun i => ?_, ?_⟩
  · simpa [matrix] using hA.1 0 i
  · simpa [matrix] using hA.2.1 0

theorem matrix_eq_uniform_iff (w : Fin 6 → ℝ) :
    matrix w = (fun _ _ => 1 / 6 : Matrix (Fin 6) (Fin 6) ℝ) ↔ w = fun _ => 1 / 6 := by
  constructor
  · intro h
    funext i
    have hi := congrFun (congrFun h 0) i
    simpa [matrix] using hi
  · intro h
    rw [h]
    rfl

#print axioms weights_of_doubly_stochastic
#print axioms matrix_eq_uniform_iff
end MathAndTheory.Gyires.CirculantSix
