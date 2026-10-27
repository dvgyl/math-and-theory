module

public import AllProfileContraction
public import StochasticRepresentation
public import StrictGram
public import MathAndTheory.Mathematics.Gyires.TwoColumnContraction

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.Gyires.RankTwo

open Bernoulli Certificate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rank_two_gram_bounds_of_checks (hn : 2 ≤ Fintype.card ι)
    (hcheck : allProfileChecks (Fintype.card ι) = true)
    (A : Matrix ι ι ℝ) (hA : A ∈ doublyStochastic ℝ ι) (hrank : A.rank ≤ 2) :
    (A*A.transpose).permanent ≤ A.permanent ∧
      dimensionConstant (Fintype.card ι) ≤ A.permanent ∧
      (A.permanent = dimensionConstant (Fintype.card ι) ↔ A = uniformMatrix) := by
  by_cases hU : A = uniformMatrix
  · subst A
    rw [uniformMatrix_transpose, uniformMatrix_mul_self, permanent_uniform]
    exact ⟨le_rfl, le_rfl, by simp⟩
  have hnpos : 0 < Fintype.card ι := by omega
  have hn0 : Fintype.card ι ≠ 0 := Nat.ne_of_gt hnpos
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hnpos
  obtain hrep | ⟨t, x, y, ht, htn, hx, hy, hxt, hyt, hrep⟩ :=
    rank_two_stochastic_representation hnpos A hA.1
      (sum_row_of_mem_doublyStochastic hA) (sum_col_of_mem_doublyStochastic hA) hrank
  · exact False.elim (hU hrep)
  let σ := t*((Fintype.card ι : ℝ)-t)/(Fintype.card ι : ℝ)^2
  let u := centerVector x (t/Fintype.card ι)
  let v := centerVector y (t/Fintype.card ι)
  have hσ : 0 < σ := div_pos (mul_pos ht (sub_pos.mpr htn)) (pow_pos hn' 2)
  have hform : A = centered (1/((Fintype.card ι : ℝ)*σ)) u v := by
    have hm := mixture_eq_centered t x y hn0 (ne_of_gt ht) (ne_of_gt (sub_pos.mpr htn))
    have he : A = (fun i j => x i*y j/t+(1-x i)*(1-y j)/((Fintype.card ι : ℝ)-t)) := by
      funext i j
      exact hrep i j
    exact he.trans hm
  have hxp : x ∈ parameters t := ⟨⟨fun i => (hx i).1, fun i => (hx i).2⟩, hxt⟩
  have hyp : y ∈ parameters t := ⟨⟨fun i => (hy i).1, fun i => (hy i).2⟩, hyt⟩
  have hu : ∑ i, u i = 0 := by
    apply sum_centerVector
    rw [hxt]
    field_simp [ne_of_gt hn']
  have hv : ∑ i, v i = 0 := by
    apply sum_centerVector
    rw [hyt]
    field_simp [ne_of_gt hn']
  have hdef := all_parameters_deficit_nonpos_of_all_checks hn hcheck t ⟨ht, htn⟩ x y hxp hyp
  rw [lawDeficit_eq_actual hn _ _ (ne_of_gt hσ) x y hv] at hdef
  have hc : 0 < ((Fintype.card ι).factorial : ℝ)/(Fintype.card ι : ℝ)^Fintype.card ι :=
    div_pos (by exact_mod_cast Nat.factorial_pos (Fintype.card ι)) (pow_pos hn' _)
  have hcontract : (A*A.transpose).permanent ≤ A.permanent := by
    rw [hform]
    exact (div_le_div_iff_of_pos_right hc).mp (sub_nonpos.mp hdef)
  have hu0 : u ≠ 0 := by
    intro h
    apply hU
    rw [hform, h]
    ext i j
    simp [centered, perturbation, uniformMatrix]
  have hv0 : v ≠ 0 := by
    intro h
    apply hU
    rw [hform, h]
    ext i j
    simp [centered, perturbation, uniformMatrix]
  have hstrict := centered_gram_strict_lower_bound hn σ hσ u v hu hv hu0 hv0
  rw [← hform] at hstrict
  change dimensionConstant (Fintype.card ι) < (A*A.transpose).permanent at hstrict
  have hd := hstrict.trans_le hcontract
  refine ⟨hcontract, hd.le, ?_⟩
  constructor
  · intro he
    exact False.elim (ne_of_gt hd he)
  · intro he
    exact False.elim (hU he)

end MathAndTheory.Gyires.RankTwo
