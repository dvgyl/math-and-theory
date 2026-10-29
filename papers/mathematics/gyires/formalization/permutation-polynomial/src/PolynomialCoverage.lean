module

public import PolynomialGap

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCoefficientRecurrence

open MathAndTheory.Gyires.PermutationFinite
open MathAndTheory.Gyires.PermutationCoefficients

theorem permanentSquareExpr_reflection (n : ℕ) (a b c : ℝ) :
    permanentSquareExpr n a b c = permanentSquareExpr n c b a := by
  unfold permanentSquareExpr
  simp only [mul_comm c a, mul_comm (c^3) a, mul_comm c (a^3)]
  ring_nf

theorem gramExpr_reflection (n : ℕ) (a b c : ℝ) : gramExpr n a b c = gramExpr n c b a := by
  unfold gramExpr
  have hd : c^2+b^2+a^2=a^2+b^2+c^2 := by ring
  have he : b*(c+a)=b*(a+c) := by ring
  rw [hd, he, mul_comm c a]

theorem rawGap_reflection (n : ℕ) (a b c : ℝ) : rawGap n a b c = rawGap n c b a := by
  unfold rawGap
  rw [permanentSquareExpr_reflection n a b c, gramExpr_reflection n a b c]

theorem rawGap_nonneg_of_chambers (n : ℕ)
    (hchamber : ∀ z : Fin 3 → ℝ, (∀ i, 0 ≤ z i) → ∀ k : Fin 3,
      0 ≤ rawGap n (chamberValues z k 0) (chamberValues z k 1) (chamberValues z k 2))
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 0 ≤ rawGap n a b c := by
  have hordered : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → a ≤ c → 0 ≤ rawGap n a b c := by
    intro a b c ha hb hac
    by_cases hba : b ≤ a
    · have hz : ∀ i : Fin 3, 0 ≤ (![b,a-b,c-a] : Fin 3 → ℝ) i := by
        intro i
        fin_cases i <;> dsimp <;> linarith
      have h := hchamber ![b,a-b,c-a] hz 1
      have heqa : b+(a-b)=a := by ring
      have heqc : b+(a-b)+(c-a)=c := by ring
      simpa [chamberValues, heqa, heqc] using h
    · have hab : a ≤ b := le_of_not_ge hba
      by_cases hbc : b ≤ c
      · have hz : ∀ i : Fin 3, 0 ≤ (![a,b-a,c-b] : Fin 3 → ℝ) i := by
          intro i
          fin_cases i <;> dsimp <;> linarith
        have h := hchamber ![a,b-a,c-b] hz 0
        have heqb : a+(b-a)=b := by ring
        have heqc : a+(b-a)+(c-b)=c := by ring
        simpa [chamberValues, heqb, heqc] using h
      · have hcb : c ≤ b := le_of_not_ge hbc
        have hz : ∀ i : Fin 3, 0 ≤ (![a,c-a,b-c] : Fin 3 → ℝ) i := by
          intro i
          fin_cases i <;> dsimp <;> linarith
        have h := hchamber ![a,c-a,b-c] hz 2
        have heqc : a+(c-a)=c := by ring
        have heqb : a+(c-a)+(b-c)=b := by ring
        simpa [chamberValues, heqc, heqb] using h
  rcases le_total a c with h | h
  · exact hordered a b c ha hb h
  · rw [rawGap_reflection]
    exact hordered c b a hc hb h

end MathAndTheory.Gyires.PermutationCoefficientRecurrence
