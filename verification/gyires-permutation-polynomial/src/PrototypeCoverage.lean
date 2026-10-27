module

public import PrototypeCertificates

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficients

open Matrix Equiv
open MathAndTheory.Gyires.PermutationMatrixBridge

theorem gapThree_reflection (a b c : ℝ) : gapThree a b c = gapThree c b a := by
  unfold gapThree gramThree
  ring

theorem gapThree_nonneg_of_ac_order {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a ≤ c) : 0 ≤ gapThree a b c := by
  by_cases hba : b ≤ a
  · have hz : ∀ i : Fin 3, 0 ≤ (![b,a-b,c-a] : Fin 3 → ℝ) i := by
      intro i
      fin_cases i <;> dsimp <;> linarith
    have h := chamber_gap_nonneg ![b,a-b,c-a] hz 1
    have heqa : b+(a-b)=a := by ring
    have heqc : b+(a-b)+(c-a)=c := by ring
    simpa [chamberValues, heqa, heqc] using h
  · have hab : a ≤ b := le_of_not_ge hba
    by_cases hbc : b ≤ c
    · have hz : ∀ i : Fin 3, 0 ≤ (![a,b-a,c-b] : Fin 3 → ℝ) i := by
        intro i
        fin_cases i <;> dsimp <;> linarith
      have h := chamber_gap_nonneg ![a,b-a,c-b] hz 0
      have heqb : a+(b-a)=b := by ring
      have heqc : a+(b-a)+(c-b)=c := by ring
      simpa [chamberValues, heqb, heqc] using h
    · have hcb : c ≤ b := le_of_not_ge hbc
      have hz : ∀ i : Fin 3, 0 ≤ (![a,c-a,b-c] : Fin 3 → ℝ) i := by
        intro i
        fin_cases i <;> dsimp <;> linarith
      have h := chamber_gap_nonneg ![a,c-a,b-c] hz 2
      have heqc : a+(c-a)=c := by ring
      have heqb : a+(c-a)+(b-c)=b := by ring
      simpa [chamberValues, heqc, heqb] using h

theorem gapThree_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ gapThree a b c := by
  rcases le_total a c with h | h
  · exact gapThree_nonneg_of_ac_order ha hb h
  · rw [gapThree_reflection]
    exact gapThree_nonneg_of_ac_order hc hb h

theorem cycle_order_three_left_gram {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A := polynomialMatrix (finRotate 3) a b c
    dimensionConstant 3 * (A*A.transpose).permanent ≤ A.permanent^2 := by
  have h := gapThree_nonneg ha hb hc
  rw [gapThree_eq_actual ha hb hc] at h
  dsimp only
  norm_num [dimensionConstant]
  linarith

theorem cycle_order_three_both_gram {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    let A := polynomialMatrix (finRotate 3) a b c
    dimensionConstant 3 * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      dimensionConstant 3 * (A.transpose*A).permanent ≤ A.permanent^2 := by
  have hleft := cycle_order_three_left_gram ha hb hc
  refine ⟨hleft, ?_⟩
  rw [← polynomialMatrix_normal]
  exact hleft

end MathAndTheory.Gyires.PermutationCoefficients
