import BookInnerShape

noncomputable section
namespace BookCompletion
open Set

theorem increasing_derivative_not_three_zeros {f f' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t) (hm : StrictMonoOn f' (Ioo a b))
    {x y z : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) (hz : z ∈ Ioo a b)
    (hxy : x < y) (hyz : y < z) (hfx : f x = 0) (hfy : f y = 0) (hfz : f z = 0) : False := by
  have hxyD : Icc x y ⊆ Ioo a b := by
    intro t ht
    exact ⟨hx.1.trans_le ht.1,ht.2.trans_lt hy.2⟩
  have hyzD : Icc y z ⊆ Ioo a b := by
    intro t ht
    exact ⟨hy.1.trans_le ht.1,ht.2.trans_lt hz.2⟩
  obtain ⟨u,hu,hu0⟩ := exists_hasDerivAt_eq_zero hxy
    (fun t ht => (hd t (hxyD ht)).continuousAt.continuousWithinAt) (hfx.trans hfy.symm)
    (fun t ht => hd t (hxyD ⟨ht.1.le,ht.2.le⟩))
  obtain ⟨v,hv,hv0⟩ := exists_hasDerivAt_eq_zero hyz
    (fun t ht => (hd t (hyzD ht)).continuousAt.continuousWithinAt) (hfy.trans hfz.symm)
    (fun t ht => hd t (hyzD ⟨ht.1.le,ht.2.le⟩))
  have hlt := hm (hxyD ⟨hu.1.le,hu.2.le⟩) (hyzD ⟨hv.1.le,hv.2.le⟩) (hu.2.trans hv.1)
  rw [hu0,hv0] at hlt
  exact lt_irrefl _ hlt

theorem increasing_derivative_two_zero_signs {f f' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t) (hm : StrictMonoOn f' (Ioo a b))
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    (hxy : x < y) (hfx : f x = 0) (hfy : f y = 0) : f' x < 0 ∧ 0 < f' y := by
  have hD : Icc x y ⊆ Ioo a b := by
    intro t ht
    exact ⟨hx.1.trans_le ht.1,ht.2.trans_lt hy.2⟩
  obtain ⟨u,hu,hu0⟩ := exists_hasDerivAt_eq_zero hxy
    (fun t ht => (hd t (hD ht)).continuousAt.continuousWithinAt) (hfx.trans hfy.symm)
    (fun t ht => hd t (hD ⟨ht.1.le,ht.2.le⟩))
  have huD := hD ⟨hu.1.le,hu.2.le⟩
  have hleft := hm hx huD hu.1
  have hright := hm huD hy hu.2
  rw [hu0] at hleft hright
  exact ⟨hleft,hright⟩

theorem innerG_zero_classification {n : ℕ} (hn : 3 ≤ n) {l r : ℝ}
    (hl : l ∈ Ioo 0 (1/2)) (hr : r ∈ Ioo 0 (1/2)) (hlr : l < r)
    (hGl : innerG n l = 0) (hGr : innerG n r = 0) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    innerG n t = 0 ↔ t = l ∨ t = r := by
  have hd : ∀ t ∈ Ioo 0 (1/2), HasDerivAt (innerG n) (innerGprime n t) t :=
    fun t ht => hasDerivAt_innerG (n:=n) (by omega) ht
  have hm := innerGprime_strictMono hn
  constructor
  · intro hz
    by_cases htl : t = l
    · exact Or.inl htl
    by_cases htr : t = r
    · exact Or.inr htr
    exfalso
    rcases lt_or_gt_of_ne htl with htl | hlt
    · exact increasing_derivative_not_three_zeros hd hm ht hl hr htl hlr hz hGl hGr
    · rcases lt_or_gt_of_ne htr with htr | hrt
      · exact increasing_derivative_not_three_zeros hd hm hl ht hr hlt htr hGl hz hGr
      · exact increasing_derivative_not_three_zeros hd hm hl hr ht hlr hrt hGl hGr hz
  · rintro (rfl | rfl) <;> assumption

theorem innerG_root_derivative_signs {n : ℕ} (hn : 3 ≤ n) {l r : ℝ}
    (hl : l ∈ Ioo 0 (1/2)) (hr : r ∈ Ioo 0 (1/2)) (hlr : l < r)
    (hGl : innerG n l = 0) (hGr : innerG n r = 0) :
    innerGprime n l < 0 ∧ 0 < innerGprime n r :=
  increasing_derivative_two_zero_signs
    (fun t ht => hasDerivAt_innerG (n:=n) (by omega) ht)
    (innerGprime_strictMono hn) hl hr hlr hGl hGr

#print axioms increasing_derivative_not_three_zeros
#print axioms increasing_derivative_two_zero_signs
#print axioms innerG_zero_classification
#print axioms innerG_root_derivative_signs
end BookCompletion
