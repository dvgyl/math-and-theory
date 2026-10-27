import AsymmetricTutte.Matroid

open Finset
open Results.TutteThreshold

namespace AsymmetricTutte

variable {ι : Type*} [DecidableEq ι]

lemma merge_parallel_set (P : Finset ι) {M : RkMat ι} {e : ι} (he : e ∈ M.E)
    (heP : e ∉ P) (hP : P ⊆ M.E) (hpar : ∀ g ∈ P, M.ParPair e g) (a z v : ℝ) :
    M.Z z v (Function.update unitWeight e (1, a)) =
      (M.restrict (M.E \ P) sdiff_subset).Z z v
        (Function.update unitWeight e (1, a * (v + 1) ^ P.card +
          ∑ j ∈ range P.card, (v + 1) ^ j)) := by
  induction P using Finset.induction_on generalizing M a with
  | empty =>
    simpa using RkMat.Z_congr z v
      (show M.Same (M.restrict (M.E \ ∅) sdiff_subset) from
        ⟨by simp, fun _ _ => rfl⟩) (fun _ _ => by simp)
  | @insert g P hg ih =>
    have hge : g ≠ e := by
      intro h
      subst g
      exact heP (mem_insert_self _ _)
    have hgE := hP (mem_insert_self g P)
    have heN : e ∈ (M.del g).E := mem_erase.mpr ⟨hge.symm, he⟩
    have heP' : e ∉ P := fun h => heP (mem_insert_of_mem h)
    have hPN : P ⊆ (M.del g).E := by
      intro f hf
      exact mem_erase.mpr ⟨fun h => hg (h ▸ hf), hP (mem_insert_of_mem hf)⟩
    have hparN : ∀ f ∈ P, (M.del g).ParPair e f := by
      intro f hf
      obtain ⟨_, _, hne, h1, h2, h3⟩ := hpar f (mem_insert_of_mem hf)
      exact ⟨heN, hPN hf, hne, h1, h2, h3⟩
    have hmerge :
        Function.update (Function.update unitWeight e (1, a)) e
          (RkMat.mergeW v ((Function.update unitWeight e (1, a)) e)
            ((Function.update unitWeight e (1, a)) g)) =
        Function.update unitWeight e (1, (v + 1) * a + 1) := by
      funext f
      by_cases hfe : f = e
      · subst f
        simp only [Function.update_self, Function.update_of_ne hge, unitWeight, RkMat.mergeW,
          mul_one]
        congr 1
        ring
      · simp only [Function.update_of_ne hfe]
    rw [M.Z_par z v _ (hpar g (mem_insert_self g P)), hmerge,
      ih heN heP' hPN hparN ((v + 1) * a + 1)]
    apply RkMat.Z_congr z v
    · refine ⟨?_, fun _ _ => rfl⟩
      change M.E.erase g \ P = M.E \ insert g P
      ext f
      simp only [mem_sdiff, mem_erase, mem_insert]
      grind
    · intro f hf
      by_cases hfe : f = e
      · subst f
        simp only [Function.update_self, card_insert_of_notMem hg, pow_succ, sum_range_succ]
        congr 1
        ring
      · simp only [Function.update_of_ne hfe]

lemma class_sum (M : RkMat ι) (hM : Loopless M) {e : ι} (he : e ∈ M.E) (x y : ℝ) :
    eval M x y = (classCollapse M e he).Z (x - 1) (y - 1)
      (Function.update unitWeight e (1, ∑ j ∈ range (parClass M e).card, y ^ j)) := by
  let P := (parClass M e).erase e
  have heP : e ∈ parClass M e := self_mem_parClass he (hM e he)
  have hP : P ⊆ M.E := (erase_subset _ _).trans (parClass_subset M e)
  have hpar : ∀ g ∈ P, M.ParPair e g := by
    intro g hg
    exact parClass_pair hM he (mem_of_mem_erase hg) (ne_of_mem_erase hg).symm
  have hW : Function.update (unitWeight : ι → Wt) e (1, 1) = unitWeight := by
    funext f
    by_cases hfe : f = e <;> simp [hfe, unitWeight]
  have h := merge_parallel_set P he (notMem_erase _ _) hP hpar 1 (x - 1) (y - 1)
  rw [hW] at h
  change eval M x y = _ at h
  rw [h]
  apply RkMat.Z_congr (x - 1) (y - 1)
  · refine ⟨?_, fun _ _ => rfl⟩
    change M.E \ (parClass M e).erase e = insert e (M.E \ parClass M e)
    ext f
    have hsub := @parClass_subset ι _ M e f
    simp only [mem_sdiff, mem_erase, mem_insert]
    grind
  · intro f hf
    by_cases hfe : f = e
    · subst f
      have hc := card_erase_add_one heP
      change P.card + 1 = (parClass M e).card at hc
      simp only [Function.update_self, sub_add_cancel, one_mul, ← hc, sum_range_succ]
      congr 1
      ring
    · simp only [Function.update_of_ne hfe]

lemma weighted_ord {M : RkMat ι} {e : ι} (he : e ∈ M.E)
    (h1 : M.r {e} = 1) (hc : M.r (M.E.erase e) = M.r M.E) (x y s : ℝ) :
    M.Z (x - 1) (y - 1) (Function.update unitWeight e (1, s)) =
      eval (M.del e) x y + s * eval (M.con e he) x y := by
  rw [M.Z_ord (x - 1) (y - 1) _ he h1 hc, Function.update_self, one_mul]
  congr 1
  · apply RkMat.Z_congr (x - 1) (y - 1) (RkMat.Same.refl _)
    intro f hf
    exact Function.update_of_ne (ne_of_mem_erase hf) _ _
  · congr 1
    apply RkMat.Z_congr (x - 1) (y - 1) (RkMat.Same.refl _)
    intro f hf
    exact Function.update_of_ne (ne_of_mem_erase hf) _ _

lemma class_deletion_same (M : RkMat ι) (hM : Loopless M) {e : ι} (he : e ∈ M.E) :
    ((classCollapse M e he).del e).Same (classRest M e) := by
  refine ⟨?_, fun _ _ => rfl⟩
  change (insert e (M.E \ parClass M e)).erase e = M.E \ parClass M e
  exact erase_insert (by simp [self_mem_parClass he (hM e he)])

lemma class_recurrence {M : RkMat ι} (hM : M.Admissible) {e : ι} (he : e ∈ M.E)
    (hC : M.r (M.E \ parClass M e) = M.r M.E) (x y : ℝ) :
    eval M x y = eval (classRest M e) x y +
      (∑ j ∈ range (parClass M e).card, y ^ j) *
        eval ((classCollapse M e he).con e (mem_insert_self _ _)) x y := by
  have hL : Loopless M := fun f hf => (hM f hf).1
  have hN := collapse_admissible hM he hC
  rw [class_sum M hL he, weighted_ord (mem_insert_self _ _) (hN e (mem_insert_self _ _)).1
    (hN e (mem_insert_self _ _)).2, eval_congr (class_deletion_same M hL he)]

end AsymmetricTutte
