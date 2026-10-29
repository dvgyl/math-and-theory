module
public import AsymmetricTutte.Basics


@[expose] public section

open Finset
open Results.TutteThreshold

namespace AsymmetricTutte

variable {ι : Type*} [DecidableEq ι]

noncomputable def parClass (M : RkMat ι) (e : ι) : Finset ι :=
  M.E.filter (fun f => M.r {e, f} = 1)

lemma parClass_subset (M : RkMat ι) (e : ι) : parClass M e ⊆ M.E := filter_subset _ _

lemma mem_parClass {M : RkMat ι} {e f : ι} :
    f ∈ parClass M e ↔ f ∈ M.E ∧ M.r {e, f} = 1 := by
  simp only [parClass, mem_filter]

lemma self_mem_parClass {M : RkMat ι} {e : ι} (he : e ∈ M.E) (h1 : M.r {e} = 1) :
    e ∈ parClass M e := by
  apply mem_parClass.mpr
  simpa using And.intro he h1

lemma parClass_pair {M : RkMat ι} (hM : Loopless M) {e f : ι} (he : e ∈ M.E)
    (hf : f ∈ parClass M e) (hne : e ≠ f) : M.ParPair e f := by
  obtain ⟨hfE, hef⟩ := mem_parClass.mp hf
  exact ⟨he, hfE, hne, hM e he, hM f hfE, hef⟩

lemma rank_insert_parClass_subset {M : RkMat ι} (hM : Loopless M) {e : ι}
    (he : e ∈ M.E) {P : Finset ι} (hP : P ⊆ parClass M e) :
    M.r (insert e P) = 1 := by
  induction P using Finset.induction_on with
  | empty => simpa using hM e he
  | @insert f P hf ih =>
    have hfC := hP (mem_insert_self f P)
    have hPC : P ⊆ parClass M e := fun g hg => hP (mem_insert_of_mem hg)
    have hPE : insert e P ⊆ M.E := insert_subset he (hPC.trans (parClass_subset M e))
    by_cases hfe : f = e
    · subst f
      simpa using ih hPC
    · rw [insert_comm]
      rw [(parClass_pair hM he hfC (Ne.symm hfe)).rk_r_insert_eq hPE (mem_insert_self e P)]
      exact ih hPC

lemma rank_parClass {M : RkMat ι} (hM : Loopless M) {e : ι} (he : e ∈ M.E) :
    M.r (parClass M e) = 1 := by
  simpa only [insert_eq_of_mem (self_mem_parClass he (hM e he))] using
    rank_insert_parClass_subset hM he (subset_refl (parClass M e))

lemma rank_union_parClass {M : RkMat ι} (hM : Loopless M) {e : ι} (he : e ∈ M.E)
    {S : Finset ι} (hS : S ⊆ M.E) :
    M.r (S ∪ parClass M e) = M.r (insert e S) := by
  have hP := parClass_subset M e
  have heP := self_mem_parClass he (hM e he)
  have hs := M.r_submod (insert_subset he hS) hP
  have hlow := M.r_mono (singleton_subset_iff.mpr (show e ∈ insert e S ∩ parClass M e by simp [heP]))
    (inter_subset_right.trans hP : insert e S ∩ parClass M e ⊆ M.E)
  have hmono := M.r_mono (insert_subset (mem_union_right S heP) subset_union_left)
    (union_subset hS hP)
  have hu : insert e S ∪ parClass M e = S ∪ parClass M e := by
    ext f
    simp only [mem_union, mem_insert]
    grind
  rw [hu, rank_parClass hM he] at hs
  rw [hM e he] at hlow
  omega

lemma rank_pair_outside_parClass {M : RkMat ι} (hM : Loopless M) {e f : ι}
    (he : e ∈ M.E) (hf : f ∈ M.E \ parClass M e) : M.r {e, f} = 2 := by
  obtain ⟨hfE, hfP⟩ := mem_sdiff.mp hf
  have hge := M.rk_r_single_le_insert (singleton_subset_iff.mpr hfE) he
  have hle := M.r_insert_le (singleton_subset_iff.mpr hfE) he
  have hne : M.r {e, f} ≠ 1 := fun h => hfP (mem_parClass.mpr ⟨hfE, h⟩)
  rw [hM e he] at hge
  rw [hM f hfE] at hle
  omega

noncomputable def classRest (M : RkMat ι) (e : ι) : RkMat ι :=
  M.restrict (M.E \ parClass M e) sdiff_subset

noncomputable def classCollapse (M : RkMat ι) (e : ι) (he : e ∈ M.E) : RkMat ι :=
  M.restrict (insert e (M.E \ parClass M e)) (insert_subset he sdiff_subset)

lemma collapse_rank {M : RkMat ι} (hM : Loopless M) {e : ι} (he : e ∈ M.E) :
    (classCollapse M e he).r (classCollapse M e he).E = M.r M.E := by
  change M.r (insert e (M.E \ parClass M e)) = M.r M.E
  rw [← rank_union_parClass hM he sdiff_subset, sdiff_union_of_subset (parClass_subset M e)]

lemma collapse_delete_rank {M : RkMat ι} (hM : Loopless M) {e f : ι}
    (he : e ∈ M.E) (hf : f ∈ M.E \ parClass M e) :
    (classCollapse M e he).r ((classCollapse M e he).E.erase f) = M.r (M.E.erase f) := by
  have hfe : f ≠ e := by
    intro h
    subst f
    exact (mem_sdiff.mp hf).2 (self_mem_parClass he (hM e he))
  have hS : (M.E \ parClass M e).erase f ⊆ M.E := (erase_subset _ _).trans sdiff_subset
  have hu : (M.E \ parClass M e).erase f ∪ parClass M e = M.E.erase f := by
    ext g
    have := (mem_sdiff.mp hf).2
    have hPg := @parClass_subset ι _ M e g
    simp only [mem_union, mem_erase, mem_sdiff]
    grind
  change M.r ((insert e (M.E \ parClass M e)).erase f) = M.r (M.E.erase f)
  rw [erase_insert_of_ne hfe.symm, ← rank_union_parClass hM he hS, hu]

lemma collapse_loopless {M : RkMat ι} (hM : Loopless M) {e : ι} (he : e ∈ M.E) :
    Loopless (classCollapse M e he) := by
  intro f hf
  exact hM f ((insert_subset he sdiff_subset) hf)

lemma collapse_admissible {M : RkMat ι} (hM : M.Admissible) {e : ι} (he : e ∈ M.E)
    (hC : M.r (M.E \ parClass M e) = M.r M.E) : (classCollapse M e he).Admissible := by
  have hL : Loopless M := fun f hf => (hM f hf).1
  intro f hf
  refine ⟨collapse_loopless hL he f hf, ?_⟩
  rw [collapse_rank hL he]
  by_cases hfe : f = e
  · subst f
    change M.r ((insert e (M.E \ parClass M e)).erase e) = M.r M.E
    rw [erase_insert (by
      intro h
      exact (mem_sdiff.mp h).2 (self_mem_parClass he (hM e he).1))]
    exact hC
  · have hfC : f ∈ M.E \ parClass M e := (mem_insert.mp hf).resolve_left hfe
    rw [collapse_delete_rank hL he hfC]
    exact (hM f (mem_sdiff.mp hfC).1).2

lemma collapse_contract_admissible {M : RkMat ι} (hM : M.Admissible) {e : ι}
    (he : e ∈ M.E) (hC : M.r (M.E \ parClass M e) = M.r M.E) :
    ((classCollapse M e he).con e (mem_insert_self _ _)).Admissible := by
  apply (collapse_admissible hM he hC).con (mem_insert_self _ _)
  intro f hpair
  have hfC : f ∈ M.E \ parClass M e :=
    (mem_insert.mp hpair.2.1).resolve_left hpair.2.2.1.symm
  have := rank_pair_outside_parClass (fun f hf => (hM f hf).1) he hfC
  have := hpair.2.2.2.2.2
  change M.r {e, f} = 1 at this
  omega

end AsymmetricTutte
