import FiniteCertificate
import Conjecture

namespace Kunisky.FiniteCounterexample

noncomputable section

lemma clauses_injective : Function.Injective clauses := by decide

lemma formula_eq_image : F = Finset.univ.image clauses := by decide

lemma denominator_eq :
    (∑ C ∈ F, Real.sqrt (t223.mass C)) = ∑ i : Fin 8, Real.sqrt (w223 i) := by
  rw [formula_eq_image, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    rw [cert223.2.2 i]
  · intro a _ b _ h
    exact clauses_injective h

def upper : Fin 8 → ℝ :=
  ![959/1000, 1/1000, 93/1000, 117/1000, 102/1000, 97/1000, 92/1000, 177/1000]

lemma sqrt_weights_le : ∀ i : Fin 8, Real.sqrt (w223 i) ≤ upper i := by
  intro i
  fin_cases i <;> apply Real.sqrt_le_iff.mpr <;> norm_num [w223, upper]

lemma denominator_le : (∑ i : Fin 8, Real.sqrt (w223 i)) ≤ 819/500 := by
  calc
    (∑ i : Fin 8, Real.sqrt (w223 i)) ≤ ∑ i : Fin 8, upper i :=
      Finset.sum_le_sum fun i _ => sqrt_weights_le i
    _ = 819/500 := by norm_num [upper, Fin.sum_univ_succ]

lemma denominator_pos : 0 < (∑ i : Fin 8, Real.sqrt (w223 i)) := by
  have h0 : 0 < Real.sqrt (w223 0) := by
    apply Real.sqrt_pos.mpr
    norm_num [w223]
  exact h0.trans_le (Finset.single_le_sum
    (fun i _ => Real.sqrt_nonneg (w223 i)) (Finset.mem_univ 0))

lemma value_eq : certificateValue F t223 = 4 / (∑ i : Fin 8, Real.sqrt (w223 i)) := by
  unfold certificateValue
  have hf : ∀ v : Fin 3, F.filter (fun C => (v,true) ∈ C ∨ (v,false) ∈ C) = F :=
    fun v => fullFormula_filter 3 v
  simp_rw [hf, t223.sum_mass cert223.1]
  rw [denominator_eq]
  norm_num

/-- A strict rational separation from the proposed constant. -/
theorem value_gt_61_25 : 61/25 < certificateValue F t223 := by
  rw [value_eq]
  apply (lt_div_iff₀ denominator_pos).mpr
  nlinarith [denominator_le]

lemma proposed_bound_lt_61_25 : 1 + Real.sqrt 2 < (61/25 : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

/-- This is a genuine finite binary resolution tree deriving the empty clause
from the complete minimally unsatisfiable 3-variable formula. -/
theorem concrete_counterexample :
    Unsatisfiable F ∧ t223.Valid F ∧ t223.conclusion = ∅ ∧
      1 + Real.sqrt 2 < certificateValue F t223 := by
  exact ⟨Tree.unsatisfiable cert223.1 cert223.2.1,
    cert223.1, cert223.2.1, proposed_bound_lt_61_25.trans value_gt_61_25⟩

end
end Kunisky.FiniteCounterexample

namespace Kunisky

/-- Negation of the internal universal-bound predicate Conjecture44. -/
theorem not_conjecture44 : ¬ Conjecture44 := by
  intro h
  obtain ⟨hu,hv,hc,hq⟩ := FiniteCounterexample.concrete_counterexample
  have hh := h 3 FiniteCounterexample.F FiniteCounterexample.t223 hu hv hc
  exact (not_lt_of_gt hq) hh

#print axioms not_conjecture44

end Kunisky
