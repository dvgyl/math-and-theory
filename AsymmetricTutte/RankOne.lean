module
public import AsymmetricTutte.PublicDefs
import all AsymmetricTutte.ParallelSum


section

open Finset
open Results.TutteThreshold

namespace AsymmetricTutte

variable {ι : Type*} [DecidableEq ι]

lemma parClass_eq_ground_of_rank_one {M : RkMat ι} (hM : Loopless M)
    (hr : M.r M.E = 1) {e : ι} (he : e ∈ M.E) : parClass M e = M.E := by
  apply Subset.antisymm (parClass_subset M e)
  intro f hf
  apply mem_parClass.mpr
  refine ⟨hf, ?_⟩
  have hge := M.rk_r_single_le_insert (singleton_subset_iff.mpr hf) he
  have hle := M.r_le_r_E (insert_subset he (singleton_subset_iff.mpr hf))
  rw [hM e he] at hge
  rw [hr] at hle
  omega

lemma eval_rank_one {M : RkMat ι} (hM : Loopless M) (hr : M.r M.E = 1) (x y : ℝ) :
    eval M x y = x - 1 + ∑ j ∈ range M.E.card, y ^ j := by
  have hne : M.E.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro h
    rw [h, M.r_empty] at hr
    omega
  obtain ⟨e, he⟩ := hne
  have hP := parClass_eq_ground_of_rank_one hM hr he
  have hN : (classCollapse M e he).E = {e} := by
    simp [classCollapse, hP]
  have hc : (classCollapse M e he).r ((classCollapse M e he).E.erase e) + 1 =
      (classCollapse M e he).r (classCollapse M e he).E := by
    rw [hN]
    simp only [erase_singleton, RkMat.r_empty, zero_add]
    exact (hM e he).symm
  have heN : e ∈ (classCollapse M e he).E := mem_insert_self _ _
  rw [class_sum M hM he, (classCollapse M e he).Z_coloop (x - 1) (y - 1) _ heN hc,
    Function.update_self]
  have hD : ((classCollapse M e he).del e).E = ∅ := by simp [hN]
  rw [RkMat.Z_empty _ _ _ _ hD, mul_one, hP, mul_one]

lemma eval_axis_zero_of_coloop {M : RkMat ι} {e : ι} (he : e ∈ M.E)
    (hc : M.r (M.E.erase e) + 1 = M.r M.E) (y : ℝ) : eval M 0 y = 0 := by
  rw [eval_coloop he hc, zero_mul]

lemma rank_one_separator {M : RkMat ι} (hM : Loopless M) {e : ι} (he : e ∈ M.E)
    (hC : M.r (M.E \ parClass M e) ≠ M.r M.E) : M.IsSep (parClass M e) := by
  refine ⟨parClass_subset M e, ?_⟩
  have hle := M.r_le_r_E (sdiff_subset : M.E \ parClass M e ⊆ M.E)
  have hs := M.r_insert_le (sdiff_subset : M.E \ parClass M e ⊆ M.E) he
  have hc := collapse_rank hM he
  change M.r (insert e (M.E \ parClass M e)) = M.r M.E at hc
  rw [rank_parClass hM he]
  omega

lemma class_rest_card_lt {M : RkMat ι} (hM : Loopless M) {e : ι} (he : e ∈ M.E) :
    (classRest M e).E.card < M.E.card := by
  change (M.E \ parClass M e).card < M.E.card
  exact card_lt_card (sdiff_ssubset (parClass_subset M e)
    ⟨e, self_mem_parClass he (hM e he)⟩)

lemma class_contract_ground {M : RkMat ι} (hM : Loopless M) {e : ι} (he : e ∈ M.E) :
    ((classCollapse M e he).con e (mem_insert_self _ _)).E = (classRest M e).E := by
  change (insert e (M.E \ parClass M e)).erase e = M.E \ parClass M e
  exact erase_insert (by simp [self_mem_parClass he (hM e he)])

end AsymmetricTutte
