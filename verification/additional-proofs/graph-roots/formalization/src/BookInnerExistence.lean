import BookInnerWitnesses
import BookInnerZeros
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace BookCompletion
open Set

theorem exists_zero_of_positive_negative {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b)) (ha : 0 < f a) (hb : f b < 0) :
    ∃ x ∈ Ioo a b, f x = 0 := by
  obtain ⟨x,hx,hzero⟩ := intermediate_value_Icc' hab.le hc ⟨hb.le,ha.le⟩
  refine ⟨x,⟨?_,?_⟩,hzero⟩
  · by_contra h
    have he : x = a := le_antisymm (le_of_not_gt h) hx.1
    rw [he] at hzero
    linarith
  · by_contra h
    have he : x = b := le_antisymm hx.2 (le_of_not_gt h)
    rw [he] at hzero
    linarith

theorem exists_zero_of_negative_positive {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b)) (ha : f a < 0) (hb : 0 < f b) :
    ∃ x ∈ Ioo a b, f x = 0 := by
  obtain ⟨x,hx,hzero⟩ := exists_zero_of_positive_negative hab hc.neg
    (neg_pos.mpr ha) (neg_neg_of_pos hb)
  exact ⟨x,hx,neg_eq_zero.mp hzero⟩

theorem innerF_exists_unique (n : ℕ) (hn : 2 ≤ n) :
    ∃ t ∈ Ioo 0 (1/2), innerF n t = 0 ∧
      ∀ s ∈ Ioo 0 (1/2), innerF n s = 0 ↔ s = t := by
  have hc : ContinuousOn (innerF n) (Icc (1/10) (1/2)) := by
    intro t ht
    exact (continuousAt_innerF n (by linarith [ht.1]) (by linarith [ht.2])).continuousWithinAt
  obtain ⟨t,ht,hzero⟩ := exists_zero_of_positive_negative (by norm_num : (1/10:ℝ) < 1/2)
    hc (innerF_tenth_pos n hn) (innerF_half_neg n)
  have htD : t ∈ Ioo 0 (1/2) := ⟨by linarith [ht.1],ht.2⟩
  refine ⟨t,htD,hzero,?_⟩
  intro s hs
  constructor
  · intro hz
    exact (innerF_strictAnti hn).injOn hs htD (hz.trans hzero.symm)
  · rintro rfl
    exact hzero

theorem innerG_exists_two (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) :
    ∃ l ∈ Ioo 0 (1/2), ∃ r ∈ Ioo 0 (1/2),
      l < r ∧ innerG n l = 0 ∧ innerG n r = 0 := by
  obtain ⟨t,ht,hneg⟩ := innerG_negative_witness n hn ho
  have hcL : ContinuousOn (innerG n) (Icc (1/100) t) := by
    intro s hs
    exact (continuousAt_innerG n (by linarith [hs.1]) (by linarith [hs.2,ht.2])).continuousWithinAt
  have hcR : ContinuousOn (innerG n) (Icc t (1/2)) := by
    intro s hs
    exact (continuousAt_innerG n (by linarith [hs.1,ht.1]) (by linarith [hs.2])).continuousWithinAt
  obtain ⟨l,hl,hGl⟩ := exists_zero_of_positive_negative ht.1 hcL
    (innerG_hundredth_pos n hn) hneg
  obtain ⟨r,hr,hGr⟩ := exists_zero_of_negative_positive ht.2 hcR hneg (innerG_half_pos n)
  refine ⟨l,⟨by linarith [hl.1],by linarith [hl.2,ht.2]⟩,
    r,⟨by linarith [hr.1,ht.1],hr.2⟩,hl.2.trans hr.1,hGl,hGr⟩

#print axioms exists_zero_of_positive_negative
#print axioms exists_zero_of_negative_positive
#print axioms innerF_exists_unique
#print axioms innerG_exists_two
end BookCompletion
