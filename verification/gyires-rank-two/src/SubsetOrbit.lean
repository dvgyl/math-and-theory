module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

open scoped BigOperators
open Finset

namespace MathAndTheory.Gyires.RankTwo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The elementary symmetric polynomial of degree `k`. -/
noncomputable def elementary (u : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset ι).powersetCard k, ∏ i ∈ S, u i

noncomputable def subsetOrbit (u : ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ σ : Equiv.Perm ι, ∏ i ∈ S, u (σ i)

omit [DecidableEq ι] in
lemma exists_perm_map_of_card_eq (S T : Finset ι) (h : S.card = T.card) :
    ∃ τ : Equiv.Perm ι, S.map τ.toEmbedding = T := by
  classical
  have ht : Fintype.card {i // i ∈ S} = Fintype.card {i // i ∈ T} := by
    simpa using h
  have hf : Fintype.card {i // i ∉ S} = Fintype.card {i // i ∉ T} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, ht]
  let et := Fintype.equivOfCardEq ht
  let ef := Fintype.equivOfCardEq hf
  let τ : Equiv.Perm ι := Equiv.subtypeCongr et ef
  have hmem (i : ι) : τ i ∈ T ↔ i ∈ S := by
    by_cases hi : i ∈ S
    · have hj : τ i ∈ T := by
        simp [τ, Equiv.subtypeCongr, hi]
      simp [hi, hj]
    · have hj : τ i ∉ T := by
        simpa [τ, Equiv.subtypeCongr, hi] using (ef ⟨i, hi⟩).property
      simp [hi, hj]
  refine ⟨τ, ?_⟩
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    exact (hmem i).mpr hi
  · intro hj
    exact Finset.mem_map.mpr ⟨τ.symm j, (hmem _).mp (by simpa using hj), by simp⟩

lemma subsetOrbit_map (u : ι → ℝ) (S : Finset ι) (τ : Equiv.Perm ι) :
    subsetOrbit u (S.map τ.toEmbedding) = subsetOrbit u S := by
  unfold subsetOrbit
  simp only [Finset.prod_map, Equiv.coe_toEmbedding]
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ => ∏ i ∈ S, u (σ i))

lemma subsetOrbit_eq_of_card_eq (u : ι → ℝ) (S T : Finset ι)
    (h : S.card = T.card) : subsetOrbit u S = subsetOrbit u T := by
  obtain ⟨τ, hτ⟩ := exists_perm_map_of_card_eq S T h
  rw [← hτ, subsetOrbit_map]

omit [DecidableEq ι] in
lemma elementary_comp (u : ι → ℝ) (k : ℕ) (σ : Equiv.Perm ι) :
    elementary (fun i => u (σ i)) k = elementary u k := by
  unfold elementary
  conv_rhs => rw [← Finset.map_univ_equiv σ, Finset.powersetCard_map]
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro S _
  change (∏ i ∈ S, u (σ i)) = ∏ i ∈ S.map σ.toEmbedding, u i
  rw [Finset.prod_map]
  rfl

lemma choose_mul_subsetOrbit (u : ι → ℝ) (S : Finset ι) :
    ((Fintype.card ι).choose S.card : ℝ) * subsetOrbit u S =
      ((Fintype.card ι).factorial : ℝ) * elementary u S.card := by
  calc
    ((Fintype.card ι).choose S.card : ℝ) * subsetOrbit u S =
        ∑ T ∈ (Finset.univ : Finset ι).powersetCard S.card, subsetOrbit u T := by
      have heq : ∀ T ∈ (Finset.univ : Finset ι).powersetCard S.card,
          subsetOrbit u T = subsetOrbit u S := by
        intro T hT
        exact subsetOrbit_eq_of_card_eq u T S (Finset.mem_powersetCard.mp hT).2
      simp_rw [Finset.sum_congr rfl heq]
      simp
    _ = ∑ σ : Equiv.Perm ι, elementary (fun i => u (σ i)) S.card := by
      unfold subsetOrbit elementary
      rw [Finset.sum_comm]
    _ = ((Fintype.card ι).factorial : ℝ) * elementary u S.card := by
      simp_rw [elementary_comp]
      simp [Fintype.card_perm]

/-- Each pair of subsets has `k! * (n-k)!` permutation extensions. -/
theorem subsetOrbit_eq_factorials (u : ι → ℝ) (S : Finset ι) :
    subsetOrbit u S =
      (S.card.factorial : ℝ) * ((Fintype.card ι - S.card).factorial : ℝ) *
        elementary u S.card := by
  have hk : S.card ≤ Fintype.card ι := Finset.card_le_univ S
  have hpos : 0 < (Fintype.card ι).choose S.card := Nat.choose_pos hk
  have hne : ((Fintype.card ι).choose S.card : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  rw [choose_mul_subsetOrbit]
  have hfact : ((Fintype.card ι).choose S.card : ℝ) * (S.card.factorial : ℝ) *
      ((Fintype.card ι - S.card).factorial : ℝ) =
      ((Fintype.card ι).factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  rw [← hfact]
  ring

omit [DecidableEq ι] in
@[simp] lemma elementary_zero (u : ι → ℝ) : elementary u 0 = 1 := by
  simp [elementary]

omit [DecidableEq ι] in
@[simp] lemma elementary_one (u : ι → ℝ) : elementary u 1 = ∑ i, u i := by
  simp [elementary, Finset.powersetCard_one]

end MathAndTheory.Gyires.RankTwo
