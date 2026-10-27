module

public import SubsetOrbit
public import Mathlib.LinearAlgebra.Matrix.Permanent

@[expose] public section

open scoped BigOperators
open Finset

namespace MathAndTheory.Gyires.RankTwo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A constant matrix plus a scaled rank-one matrix. -/
noncomputable def perturbation (d s : ℝ) (u v : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => d + s * u i * v j

lemma perturbation_perm_product (d s : ℝ) (u v : ι → ℝ) (σ : Equiv.Perm ι) :
    (∏ i, perturbation d s u v (σ i) i) =
      ∑ S ∈ (Finset.univ : Finset ι).powerset,
        d ^ (Fintype.card ι - S.card) * s ^ S.card *
          (∏ i ∈ S, u (σ i)) * (∏ i ∈ S, v i) := by
  unfold perturbation
  simp_rw [add_comm d]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub : S ⊆ (Finset.univ : Finset ι) := Finset.mem_powerset.mp hS
  simp only [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_sdiff_of_subset hsub, Finset.card_univ]
  ring

/-- The permanent expansion holds for signed real entries and every finite order. -/
theorem permanent_perturbation (d s : ℝ) (u v : ι → ℝ) :
    (perturbation d s u v).permanent =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        (k.factorial : ℝ) * ((Fintype.card ι - k).factorial : ℝ) *
          d ^ (Fintype.card ι - k) * s ^ k * elementary u k * elementary v k := by
  unfold Matrix.permanent
  simp_rw [perturbation_perm_product]
  rw [Finset.sum_comm]
  have hterm (S : Finset ι) :
      (∑ σ : Equiv.Perm ι,
        d ^ (Fintype.card ι - S.card) * s ^ S.card *
          (∏ i ∈ S, u (σ i)) * (∏ i ∈ S, v i)) =
        (S.card.factorial : ℝ) * ((Fintype.card ι - S.card).factorial : ℝ) *
          d ^ (Fintype.card ι - S.card) * s ^ S.card *
            elementary u S.card * (∏ i ∈ S, v i) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    change d ^ (Fintype.card ι - S.card) * s ^ S.card * subsetOrbit u S * _ = _
    rw [subsetOrbit_eq_factorials]
    ring
  simp_rw [hterm]
  rw [Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = ∑ S ∈ (Finset.univ : Finset ι).powersetCard k,
        (k.factorial : ℝ) * ((Fintype.card ι - k).factorial : ℝ) *
          d ^ (Fintype.card ι - k) * s ^ k * elementary u k * (∏ i ∈ S, v i) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
    _ = _ := by rw [← Finset.mul_sum]; rfl

end MathAndTheory.Gyires.RankTwo
