import BookOuterCalculus
import Mathlib.Topology.Order.IntermediateValue

set_option maxHeartbeats 1000000
noncomputable section
open Set Polynomial
namespace BookCompletion

theorem outerK_two (n : ℕ) (hn : 1≤n) : outerK n 2=4*(1/2:ℝ)^n := by
  have hn0 : n≠0 := by omega
  norm_num [outerK,u,zero_pow hn0]

theorem outerK_two_lt (n : ℕ) (hn : 2≤n) : outerK n 2<2 := by
  rw [outerK_two n (by omega)]
  have hp : (1/2:ℝ)^n ≤ (1/2:ℝ)^2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  nlinarith

theorem outerK_three (n : ℕ) : outerK n 3=9*(4/3:ℝ)^n-5 := by
  norm_num [outerK,u]

theorem outerK_three_gt (n : ℕ) : 2<outerK n 3 := by
  rw [outerK_three]
  have hp : (1:ℝ) ≤ (4/3:ℝ)^n := one_le_pow₀ (by norm_num)
  linarith

theorem outerK_exists_unique (n : ℕ) (hn : 2≤n) :
    ∃ t : ℝ, 2<t ∧ t<3 ∧ outerK n t=2 ∧
      ∀ s : ℝ, 2<s → outerK n s=2 → s=t := by
  have hcont : ContinuousOn (outerK n) (Icc 2 3) := by
    intro t ht
    exact (outer_hasDerivAt n (by linarith [ht.1] : t≠0)).continuousAt.continuousWithinAt
  have hlo := outerK_two_lt n hn
  have hhi := outerK_three_gt n
  obtain ⟨t,ht,heq⟩ := intermediate_value_Icc (show (2:ℝ)≤3 by norm_num) hcont
    (show (2:ℝ)∈Icc (outerK n 2) (outerK n 3) from ⟨hlo.le,hhi.le⟩)
  have ht2 : 2<t := by
    by_contra h
    have he : t=2 := le_antisymm (not_lt.mp h) ht.1
    subst t
    linarith
  have ht3 : t<3 := by
    by_contra h
    have he : t=3 := le_antisymm ht.2 (not_lt.mp h)
    subst t
    linarith
  refine ⟨t,ht2,ht3,heq,?_⟩
  intro s hs hseq
  exact (outer_strictMonoOn n).injOn hs ht2 (hseq.trans heq.symm)

theorem outer_even_actual_root (n : ℕ) (hn : 2≤n) (he : Even n) :
    ∃ x : ℝ, -3<x ∧ x< -2 ∧ (realPolynomial n).IsRoot x ∧
      ∀ y : ℝ, y< -2 → (realPolynomial n).IsRoot y → y=x := by
  obtain ⟨t,ht2,ht3,hK,hunique⟩ := outerK_exists_unique n hn
  have htpos : 0<t := by linarith
  have htroot : (realPolynomial n).IsRoot (-t) := by
    apply (real_root_iff_normalized n (by omega) htpos).2
    rw [normalized_even_outerK n he,hK]
    ring
  refine ⟨-t,by linarith,by linarith,htroot,?_⟩
  intro y hy hyr
  have hypos : 0< -y := by linarith
  have hnorm : normalized n (-y)=0 := by
    apply (real_root_iff_normalized n (by omega) hypos).1
    simpa using hyr
  have hyK : outerK n (-y)=2 := by
    rw [normalized_even_outerK n he] at hnorm
    linarith
  have hyt := hunique (-y) (by linarith) hyK
  linarith

#print axioms outerK_two
#print axioms outerK_two_lt
#print axioms outerK_three
#print axioms outerK_three_gt
#print axioms outerK_exists_unique
#print axioms outer_even_actual_root
end BookCompletion
