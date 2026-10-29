import AsymmetricTutte.Necessity.Base
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

namespace AsymmetricMerinoWelsh

open Finset Matroid
open Results.TutteThreshold

noncomputable section

/-- The rank-r uniform matroid on n parallel classes, each of size k. -/
def thickUniform (r n k : ℕ) : Matroid (Fin n × Fin k) :=
  (uniformMatroid r n).comap Prod.fst

theorem thickUniform_rank (r n k : ℕ) (S : Finset (Fin n × Fin k)) :
    rk (thickUniform r n k) (S : Set (Fin n × Fin k)) =
      min r (S.image Prod.fst).card := by
  rw [rk, thickUniform, eRk_comap, eRk_uniformMatroid, ← coe_image,
    Set.encard_coe_eq_coe_finsetCard, ← (Nat.mono_cast (α := ℕ∞)).map_min,
    ENat.toNat_coe]

theorem thickUniform_ground (r n k : ℕ) : (thickUniform r n k).E = Set.univ := rfl

theorem thickUniform_finset (r n k : ℕ) :
    (thickUniform r n k).ground_finite.toFinset = univ := by
  exact Set.Finite.toFinset_eq_univ.mpr rfl

theorem projection_univ (n k : ℕ) (hk : 0 < k) :
    (univ : Finset (Fin n × Fin k)).image Prod.fst = univ := by
  apply eq_univ_of_forall
  intro a
  exact mem_image.mpr ⟨(a, ⟨0, hk⟩), mem_univ _, rfl⟩

theorem thickUniform_eRank {r n k : ℕ} (hrn : r ≤ n) (hk : 0 < k) :
    (thickUniform r n k).eRank.toNat = r := by
  have H := thickUniform_rank r n k univ
  rw [coe_univ, projection_univ n k hk, card_univ, Fintype.card_fin,
    min_eq_left hrn] at H
  simpa only [rk, ← eRk_ground, thickUniform_ground] using H

theorem thickUniform_pair {r n k : ℕ} (hr : 0 < r) (a b : Fin n × Fin k)
    (hne : a ≠ b) (hab : a.1 = b.1) :
    (toRk (thickUniform r n k)).ParPair a b := by
  refine ⟨?_, ?_, hne, ?_, ?_, ?_⟩
  · simp [toRk_E, thickUniform_finset]
  · simp [toRk_E, thickUniform_finset]
  · rw [toRk_r, thickUniform_rank]
    simp [min_eq_right (show 1 ≤ r by omega)]
  · rw [toRk_r, thickUniform_rank]
    simp [min_eq_right (show 1 ≤ r by omega)]
  · rw [toRk_r, thickUniform_rank]
    simp [hab, min_eq_right (show 1 ≤ r by omega)]

theorem thickUniform_admissible {r n k : ℕ} (hr : 0 < r) (hk : 2 ≤ k) :
    IsAdmissible (thickUniform r n k) := by
  apply (Bridge.isAdmissible_iff (thickUniform r n k)).mpr
  intro e he
  obtain ⟨a, b⟩ := e
  have hnon : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  letI := hnon
  obtain ⟨c, hcb⟩ := exists_ne b
  have hp := thickUniform_pair hr (a, c) (a, b)
    (by intro h; exact hcb (Prod.mk.inj h).2) rfl
  refine ⟨hp.2.2.2.2.1, ?_⟩
  exact rank_del_parallel hp

theorem thickUniform_axis_upper {r n k : ℕ} (hr : 0 < r) (hrn : r ≤ n)
    (hk : 0 < k) {x : ℝ} (hx : 1 < x) :
    tutte (thickUniform r n k) x 0 * (x - 1) ^ (n - r) ≤ x ^ n := by
  have H := axis_upper_parallel_fibers (toRk (thickUniform r n k)) Prod.fst
    (fun a _ b _ hne hab => thickUniform_pair hr a b hne hab) (sub_pos.mpr hx)
  rw [Bridge.toRk_r_E, thickUniform_eRank hrn hk, toRk_E, thickUniform_finset,
    projection_univ n k hk, card_univ, Fintype.card_fin] at H
  unfold unitWeights at H
  simpa only [tutte_eq_Z, zero_sub, sub_add_cancel] using H

theorem thickUniform_other_axis_upper {r n k : ℕ} (hrn : r ≤ n) (hk : 0 < k)
    {y : ℝ} (hy : 1 < y) :
    tutte (thickUniform r n k) 0 y * (y - 1) ^ r ≤ y ^ (n * k) := by
  let N := toRk (thickUniform r n k)
  have H := axis_upper N.dual (sub_pos.mpr hy)
  have hcard : N.E.card = n * k := by
    simp [N, toRk_E, thickUniform_finset, Fintype.card_prod]
  have hrank : N.r N.E = r := by
    exact (Bridge.toRk_r_E _).trans (thickUniform_eRank hrn hk)
  have hbound : r ≤ n * k := by
    have h := N.r_le_card (subset_refl N.E)
    rwa [hrank, hcard] at h
  rw [RkMat.Z_dual, RkMat.dual_E] at H
  have hdual : N.dual.r N.E = n * k - r := by
    simp only [RkMat.dual_r, sdiff_self, Finset.bot_eq_empty, N.r_empty,
      add_zero, hcard, hrank]
  rw [hdual, hcard, Nat.sub_sub_self hbound] at H
  simpa only [N, tutte_eq_Z, zero_sub, sub_add_cancel, unitWeights] using H

/-- Choosing r class labels and one of k copies in each chosen class. -/
abbrev Selections (n r k : ℕ) :=
  Σ U : {U : Finset (Fin n) // U.card = r}, (U.1 → Fin k)

def selectionSet {n r k : ℕ} (s : Selections n r k) : Finset (Fin n × Fin k) :=
  s.1.1.attach.image (fun a => (a.1, s.2 a))

theorem selection_projection {n r k : ℕ} (s : Selections n r k) :
    (selectionSet s).image Prod.fst = s.1.1 := by
  simp [selectionSet, Finset.image_image, Function.comp_def]

theorem selection_card {n r k : ℕ} (s : Selections n r k) :
    (selectionSet s).card = r := by
  have hi : Function.Injective (fun a : s.1.1 => (a.1, s.2 a)) := by
    intro a b h
    exact Subtype.ext (Prod.mk.inj h).1
  rw [selectionSet, card_image_of_injective _ hi, card_attach, s.1.2]

theorem selection_injective {n r k : ℕ} :
    Function.Injective (@selectionSet n r k) := by
  rintro ⟨U, f⟩ ⟨V, g⟩ h
  have huv : U = V := by
    apply Subtype.ext
    simpa only [selection_projection] using congrArg (fun S => S.image Prod.fst) h
  subst V
  have hfg : f = g := by
    funext a
    have ha : (a.1, f a) ∈ selectionSet ⟨U, f⟩ :=
      mem_image.mpr ⟨a, mem_attach _ _, rfl⟩
    rw [h] at ha
    obtain ⟨b, _, hb⟩ := mem_image.mp ha
    have hba : b = a := Subtype.ext (Prod.mk.inj hb).1
    subst b
    exact (Prod.mk.inj hb).2.symm
  subst g
  rfl

theorem selections_card (n r k : ℕ) :
    Fintype.card (Selections n r k) = n.choose r * k ^ r := by
  have hU : Fintype.card {U : Finset (Fin n) // U.card = r} = n.choose r := by
    rw [Fintype.card_subtype]
    calc
      (univ.filter (fun U : Finset (Fin n) => U.card = r)).card =
          ((univ : Finset (Fin n)).powersetCard r).card := by
            congr 1
            ext U
            simp
      _ = n.choose r := by simp
  rw [Fintype.card_sigma]
  have hterm : ∀ U : {U : Finset (Fin n) // U.card = r},
      Fintype.card (U.1 → Fin k) = k ^ r := by
    intro U
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, U.2]
  simp [hterm, hU]

abbrev ThickBases (n r k : ℕ) :=
  {S : Finset (Fin n × Fin k) // S.card = r ∧ (S.image Prod.fst).card = r}

theorem thickUniform_basis_count {r n k : ℕ} (hrn : r ≤ n) (hk : 0 < k) :
    tutte (thickUniform r n k) 1 1 = (Fintype.card (ThickBases n r k) : ℝ) := by
  rw [tutte, thickUniform_finset, powerset_univ, thickUniform_eRank hrn hk,
    Fintype.card_subtype, Finset.natCast_card_filter]
  apply sum_congr rfl
  intro S _
  rw [thickUniform_rank]
  have hp : (S.image Prod.fst).card ≤ S.card := card_image_le
  by_cases hS : S.card = r ∧ (S.image Prod.fst).card = r
  · simp [hS]
  · have hz : r - min r (S.image Prod.fst).card ≠ 0 ∨
        S.card - min r (S.image Prod.fst).card ≠ 0 := by omega
    rcases hz with hz | hz
    · simp [hS, zero_pow hz]
    · simp [hS, zero_pow hz]

theorem thickUniform_bases_lower {r n k : ℕ} (hrn : r ≤ n) (hk : 0 < k) :
    (n.choose r : ℝ) * (k : ℝ) ^ r ≤ tutte (thickUniform r n k) 1 1 := by
  let f : Selections n r k → ThickBases n r k := fun s =>
    ⟨selectionSet s, selection_card s, by rw [selection_projection]; exact s.1.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact selection_injective (congrArg Subtype.val hab)
  have hc := Fintype.card_le_of_injective f hf
  rw [selections_card] at hc
  rw [thickUniform_basis_count hrn hk]
  exact_mod_cast hc

end

end AsymmetricMerinoWelsh
