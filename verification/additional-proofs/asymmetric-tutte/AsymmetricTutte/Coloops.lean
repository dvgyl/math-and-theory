import AsymmetricTutte.ParallelSum

open Finset
open Results.TutteThreshold

namespace AsymmetricTutte

variable {ι : Type*} [DecidableEq ι]

lemma parClass_pair_any {M : RkMat ι} (hM : Loopless M) {e f g : ι}
    (he : e ∈ M.E) (hf : f ∈ parClass M e) (hg : g ∈ parClass M e) (hfg : f ≠ g) :
    M.ParPair f g := by
  have hfE := parClass_subset M e hf
  have hgE := parClass_subset M e hg
  refine ⟨hfE, hgE, hfg, hM f hfE, hM g hgE, ?_⟩
  have hupper := M.r_mono (insert_subset hf (singleton_subset_iff.mpr hg)) (parClass_subset M e)
  have hlower := M.rk_r_single_le_insert (singleton_subset_iff.mpr hgE) hfE
  rw [rank_parClass hM he] at hupper
  rw [hM f hfE] at hlower
  omega

lemma parClass_mem_of_pair {M : RkMat ι} (hM : Loopless M) {e f g : ι}
    (he : e ∈ M.E) (hfg : M.ParPair f g) (hg : g ∈ parClass M e) : f ∈ parClass M e := by
  have hp := hfg.rk_symm.rk_r_insert_eq (parClass_subset M e) hg
  have heP := self_mem_parClass he (hM e he)
  have hu := M.r_mono (insert_subset (mem_insert_of_mem heP)
    (singleton_subset_iff.mpr (mem_insert_self f (parClass M e))))
    (insert_subset hfg.1 (parClass_subset M e))
  have hl := M.rk_r_single_le_insert (singleton_subset_iff.mpr hfg.1) he
  rw [hp, rank_parClass hM he] at hu
  rw [hM e he] at hl
  exact mem_parClass.mpr ⟨hfg.1, by omega⟩

lemma class_rest_coloop_mate {M : RkMat ι} (hM : M.Admissible) {e : ι}
    (he : e ∈ M.E) (hk : 2 ≤ (parClass M e).card)
    (hC : M.r (M.E \ parClass M e) = M.r M.E)
    (hmates : ∀ f ∈ M.E, ∃ g, M.ParPair f g ∨ M.SerPair f g)
    {f : ι} (hf : f ∈ (classRest M e).E)
    (hfc : (classRest M e).r ((classRest M e).E.erase f) + 1 =
      (classRest M e).r (classRest M e).E) :
    ∃ g ∈ (classRest M e).E, g ≠ f ∧
      (classRest M e).r ((classRest M e).E.erase g) + 1 =
        (classRest M e).r (classRest M e).E := by
  have hL : Loopless M := fun f hf => (hM f hf).1
  have hfC : f ∈ M.E \ parClass M e := hf
  have hfE := (mem_sdiff.mp hfC).1
  obtain ⟨g, hg⟩ := hmates f hfE
  have hser : M.SerPair f g := by
    rcases hg with hp | hs
    · have hgC : g ∈ M.E \ parClass M e := by
        refine mem_sdiff.mpr ⟨hp.2.1, ?_⟩
        intro hgP
        exact (mem_sdiff.mp hfC).2 (parClass_mem_of_pair hL he hp hgP)
      have hgD : g ∈ (M.E \ parClass M e).erase f := mem_erase.mpr ⟨hp.2.2.1.symm, hgC⟩
      have h := hp.rk_symm.rk_r_insert_eq
        ((erase_subset _ _).trans sdiff_subset) hgD
      rw [insert_erase hfC] at h
      change M.r ((M.E \ parClass M e).erase f) + 1 = M.r (M.E \ parClass M e) at hfc
      omega
    · exact hs
  obtain ⟨_, hgE, hfg, hdrop⟩ := (RkMat.SerPair_iff hM).mp hser
  have hgC : g ∈ M.E \ parClass M e := by
    refine mem_sdiff.mpr ⟨hgE, ?_⟩
    intro hgP
    obtain ⟨a, haP, hag⟩ := Finset.exists_mem_ne (by omega : 1 < (parClass M e).card) g
    have haf : a ≠ f := by
      intro h
      exact (mem_sdiff.mp hfC).2 (h ▸ haP)
    have haD : a ∈ M.E \ {f, g} := by
      simp only [mem_sdiff, mem_insert, mem_singleton]
      exact ⟨parClass_subset M e haP, by grind⟩
    have hpair := parClass_pair_any hL he haP hgP hag
    have h := hpair.rk_r_insert_eq sdiff_subset haD
    have hu : insert g (M.E \ {f, g}) = M.E.erase f := by
      ext a
      simp only [mem_insert, mem_sdiff, mem_erase, mem_singleton]
      grind
    rw [hu, (hM f hfE).2] at h
    omega
  refine ⟨g, hgC, hfg.symm, ?_⟩
  have hS : (M.E \ parClass M e).erase g \ {f} ⊆ (M.E \ parClass M e).erase f := by
    intro a ha
    simp only [mem_sdiff, mem_erase, mem_singleton] at ha ⊢
    grind
  have hinsert := (classRest M e).posit_r_insert_coloop hf hfc hS
  have heq : insert f ((M.E \ parClass M e).erase g \ {f}) =
      (M.E \ parClass M e).erase g := by
    ext a
    simp only [mem_insert, mem_sdiff, mem_erase, mem_singleton]
    grind
  change M.r (insert f ((M.E \ parClass M e).erase g \ {f})) =
      M.r ((M.E \ parClass M e).erase g \ {f}) + 1 at hinsert
  rw [heq] at hinsert
  have hsub := M.r_submod (S := M.E \ {f, g})
    (T := (M.E \ parClass M e).erase f) (sdiff_subset : M.E \ {f, g} ⊆ M.E)
    ((erase_subset _ _).trans (sdiff_subset : M.E \ parClass M e ⊆ M.E))
  have hu : (M.E \ {f, g}) ∪ (M.E \ parClass M e).erase f = M.E.erase f := by
    ext a
    simp only [mem_union, mem_sdiff, mem_erase, mem_insert, mem_singleton]
    grind
  have hi : (M.E \ {f, g}) ∩ (M.E \ parClass M e).erase f =
      (M.E \ parClass M e).erase g \ {f} := by
    ext a
    simp only [mem_inter, mem_sdiff, mem_erase, mem_insert, mem_singleton]
    grind
  rw [hu, hi, (hM f hfE).2] at hsub
  have hstep := M.r_insert_le (S := (M.E \ parClass M e).erase g)
    ((erase_subset _ _).trans sdiff_subset) hgE
  rw [insert_erase hgC] at hstep
  change M.r ((M.E \ parClass M e).erase f) + 1 = M.r (M.E \ parClass M e) at hfc
  change M.r ((M.E \ parClass M e).erase g) + 1 = M.r (M.E \ parClass M e)
  omega

end AsymmetricTutte
