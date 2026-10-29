module
public import AsymmetricTutte.Basics


@[expose] public section

open Finset
open Results.TutteThreshold

namespace AsymmetricTutte

variable {ι : Type*} [DecidableEq ι]

noncomputable def bases (M : RkMat ι) : Finset (Finset ι) :=
  M.E.powerset.filter (fun S => M.r S = M.r M.E ∧ S.card = M.r M.E)

lemma mem_bases {M : RkMat ι} {S : Finset ι} :
    S ∈ bases M ↔ S ⊆ M.E ∧ M.r S = M.r M.E ∧ S.card = M.r M.E := by
  simp only [bases, mem_filter, mem_powerset]

lemma eval_basis_card (M : RkMat ι) : eval M 1 1 = (bases M).card := by
  unfold eval RkMat.Z bases
  simp only [sub_self, prod_const_one, mul_one]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, sum_filter]
  apply sum_congr rfl
  intro S hS
  have hSE := mem_powerset.mp hS
  have hr := M.r_le_r_E hSE
  have hc := M.r_le_card hSE
  by_cases ha : M.r S = M.r M.E
  · by_cases hb : S.card = M.r M.E
    · simp [ha, hb]
    · have hn : S.card - M.r M.E ≠ 0 := by omega
      simp [ha, hb, zero_pow hn]
  · have hn : M.r M.E - M.r S ≠ 0 := by omega
    simp [ha, zero_pow hn]

lemma coloop_mem_basis {M : RkMat ι} {f : ι} (_hf : f ∈ M.E)
    (hc : M.r (M.E.erase f) + 1 = M.r M.E) {S : Finset ι} (hS : S ∈ bases M) :
    f ∈ S := by
  obtain ⟨hSE, hr, _⟩ := mem_bases.mp hS
  by_contra hfS
  have hsub : S ⊆ M.E.erase f := by
    intro g hg
    exact mem_erase.mpr ⟨fun h => hfS (h ▸ hg), hSE hg⟩
  have h := M.r_mono hsub (erase_subset f M.E)
  omega

lemma basis_erase_coloop_into_contract {M : RkMat ι} (hM : M.Admissible)
    {e f : ι} (he : e ∈ M.E) (hf : f ∈ (M.del e).E)
    (hfc : (M.del e).r ((M.del e).E.erase f) + 1 = (M.del e).r (M.del e).E)
    {S : Finset ι} (hS : S ∈ bases (M.del e)) : S.erase f ∈ bases (M.con e he) := by
  have hfS := coloop_mem_basis hf hfc hS
  obtain ⟨hSE, hrS, hcS⟩ := mem_bases.mp hS
  have hSN : S ⊆ M.E.erase e := hSE
  have hfe : f ≠ e := ne_of_mem_erase hf
  have hfE := mem_of_mem_erase hf
  have heS : e ∉ S := fun h => notMem_erase e M.E (hSN h)
  have hSf : S.erase f ⊆ (M.E.erase e).erase f := erase_subset_erase f hSN
  have hin := (M.del e).posit_r_insert_coloop hf hfc hSf
  rw [insert_erase hfS] at hin
  change M.r S = M.r (S.erase f) + 1 at hin
  have hsub := M.r_submod (S := insert e (S.erase f)) (T := (M.E.erase e).erase f)
    (insert_subset he ((erase_subset f S).trans (hSN.trans (erase_subset e M.E))))
    ((erase_subset f (M.E.erase e)).trans (erase_subset e M.E))
  have hu : insert e (S.erase f) ∪ (M.E.erase e).erase f = M.E.erase f := by
    ext g
    simp only [mem_union, mem_insert, mem_erase]
    have hSg := @hSN g
    grind
  have hi : insert e (S.erase f) ∩ (M.E.erase e).erase f = S.erase f := by
    ext g
    simp only [mem_inter, mem_insert, mem_erase]
    have hSg := @hSN g
    grind
  rw [hu, hi, (hM f hfE).2] at hsub
  have hupper := M.r_le_r_E (S := insert e (S.erase f)) (insert_subset he
    ((erase_subset f S).trans (hSN.trans (erase_subset e M.E))))
  change M.r ((M.E.erase e).erase f) + 1 = M.r (M.E.erase e) at hfc
  change M.r S = M.r (M.E.erase e) at hrS
  change S.card = M.r (M.E.erase e) at hcS
  rw [(hM e he).2] at hfc hrS hcS
  have hA : M.r (insert e (S.erase f)) = M.r M.E := by omega
  apply mem_bases.mpr
  refine ⟨(erase_subset _ _).trans hSN, ?_, ?_⟩
  · simp only [RkMat.con_r, RkMat.con_E, insert_erase he, hA]
  · have hcard := card_erase_add_one hfS
    simp only [RkMat.con_r, RkMat.con_E, insert_erase he, (hM e he).1]
    omega

lemma bases_contraction_ge_two {M : RkMat ι} (hM : M.Admissible) {e f g : ι}
    (he : e ∈ M.E) (hf : f ∈ (M.del e).E) (hg : g ∈ (M.del e).E) (hfg : f ≠ g)
    (hfc : (M.del e).r ((M.del e).E.erase f) + 1 = (M.del e).r (M.del e).E)
    (hgc : (M.del e).r ((M.del e).E.erase g) + 1 = (M.del e).r (M.del e).E) :
    2 * eval (M.del e) 1 1 ≤ eval (M.con e he) 1 1 := by
  let B := bases (M.del e)
  let F := B.image (fun S => S.erase f)
  let G := B.image (fun S => S.erase g)
  have hinjF : Set.InjOn (fun S : Finset ι => S.erase f) B := by
    intro S hS T hT hST
    have hs := coloop_mem_basis hf hfc hS
    have ht := coloop_mem_basis hf hfc hT
    simpa only [insert_erase hs, insert_erase ht] using congrArg (insert f) hST
  have hinjG : Set.InjOn (fun S : Finset ι => S.erase g) B := by
    intro S hS T hT hST
    have hs := coloop_mem_basis hg hgc hS
    have ht := coloop_mem_basis hg hgc hT
    simpa only [insert_erase hs, insert_erase ht] using congrArg (insert g) hST
  have hdis : Disjoint F G := by
    apply Finset.disjoint_left.mpr
    intro S hSF hSG
    obtain ⟨A, hA, hAS⟩ := mem_image.mp hSF
    obtain ⟨C, hC, hCS⟩ := mem_image.mp hSG
    have hfC := coloop_mem_basis hf hfc hC
    have hfin : f ∈ C.erase g := mem_erase.mpr ⟨hfg, hfC⟩
    rw [hCS, ← hAS] at hfin
    exact notMem_erase _ _ hfin
  have hsub : F ∪ G ⊆ bases (M.con e he) := by
    intro S hS
    rcases mem_union.mp hS with hS | hS
    · obtain ⟨A, hA, rfl⟩ := mem_image.mp hS
      exact basis_erase_coloop_into_contract hM he hf hfc hA
    · obtain ⟨A, hA, rfl⟩ := mem_image.mp hS
      exact basis_erase_coloop_into_contract hM he hg hgc hA
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hdis, card_image_of_injOn hinjF, card_image_of_injOn hinjG] at hcard
  have hcard' : 2 * (bases (M.del e)).card ≤ (bases (M.con e he)).card := by
    simpa only [B, ← two_mul] using hcard
  rw [eval_basis_card, eval_basis_card]
  exact_mod_cast hcard'

end AsymmetricTutte
