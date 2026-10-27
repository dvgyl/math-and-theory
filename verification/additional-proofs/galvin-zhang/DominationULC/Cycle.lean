import DominationULC.Path
import DominationULC.FiniteFamily
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Data.List.Forall2

namespace DominationULC

open scoped BigOperators

/-- The power of a cycle, using clockwise or anticlockwise cyclic distance at
most `ell`. The empty cycle is the empty graph. -/
def cyclePower : (n ell : ℕ) → SimpleGraph (Fin n)
  | 0, _ => ⊥
  | n + 1, ell => SimpleGraph.circulantGraph {d : Fin (n + 1) | d.val ≤ ell}

theorem dominates_cyclePower_iff {n ell : ℕ} {s : Finset (Fin (n + 1))} :
    Dominates (cyclePower (n + 1) ell) s ↔
      ∀ v, ∃ w ∈ s, (v - w).val ≤ ell ∨ (w - v).val ≤ ell := by
  constructor
  · intro h v
    obtain ⟨w, hw, hvw⟩ := h v
    refine ⟨w, hw, ?_⟩
    rcases hvw with rfl | hvw
    · simp
    · exact hvw.2
  · intro h v
    obtain ⟨w, hw, hvw⟩ := h v
    refine ⟨w, hw, ?_⟩
    by_cases he : v = w
    · exact Or.inl he
    · exact Or.inr ⟨he, hvw⟩

theorem cyclic_near_iff {n ell : ℕ} (v w : Fin (n + 1)) :
    ((v - w).val ≤ ell ∨ (w - v).val ≤ ell) ↔
      ((v.val ≤ w.val + ell ∧ w.val ≤ v.val + ell) ∨
        v.val + (n + 1) ≤ w.val + ell ∨ w.val + (n + 1) ≤ v.val + ell) := by
  have h₁ := Fin.intCast_val_sub_eq_sub_add_ite v w
  have h₂ := Fin.intCast_val_sub_eq_sub_add_ite w v
  by_cases h : w ≤ v <;> by_cases h' : v ≤ w <;>
    simp only [h, h', if_true, if_false, add_zero] at h₁ h₂ <;>
    simp only [Fin.le_iff_val_le_val] at h h' <;> omega

/-- Inserting the distinguished vertex identifies subsets of the other
vertices with subsets containing the distinguished vertex. -/
def rootedSubsetEquiv (n : ℕ) : Finset (Fin n) ≃
    {s : Finset (Fin (n + 1)) // (0 : Fin (n + 1)) ∈ s} where
  toFun s := ⟨insert 0 (s.map (Fin.succEmb n)), by simp⟩
  invFun s := Finset.univ.filter (fun v : Fin n => v.succ ∈ s.val)
  left_inv s := by
    ext v
    simp
  right_inv s := by
    apply Subtype.ext
    ext v
    refine Fin.cases ?_ (fun u => ?_) v
    · simp [s.property]
    · simp

/-- A cyclic composition is the sequence of clockwise gaps from vertex zero. -/
def cycleSubsetEquiv (n : ℕ) : Composition (n + 1) ≃
    {s : Finset (Fin (n + 1)) // (0 : Fin (n + 1)) ∈ s} :=
  (pathSubsetEquiv n).trans (rootedSubsetEquiv n)

def cycleSubset {n : ℕ} (c : Composition (n + 1)) : Finset (Fin (n + 1)) :=
  (cycleSubsetEquiv n c).val

theorem cycleSubset_def {n : ℕ} (c : Composition (n + 1)) :
    cycleSubset c = insert 0 ((pathSubsetEquiv n c).map (Fin.succEmb n)) := rfl

@[simp] theorem zero_mem_cycleSubset {n : ℕ} (c : Composition (n + 1)) :
    (0 : Fin (n + 1)) ∈ cycleSubset c := (cycleSubsetEquiv n c).property

theorem cycleSubset_card {n : ℕ} (c : Composition (n + 1)) :
    (cycleSubset c).card = c.length := by
  rw [cycleSubset_def, Finset.card_insert_of_not_mem]
  · simpa using path_card_add_one c
  · simp

theorem mem_cycleSubset_iff {n : ℕ} (c : Composition (n + 1)) (v : Fin (n + 1)) :
    v ∈ cycleSubset c ↔ ∃ j, j < c.length ∧ c.sizeUpTo j = v.val := by
  refine Fin.cases ?_ (fun u => ?_) v
  · constructor
    · intro _
      exact ⟨0, c.length_pos_of_pos (by omega), by simp⟩
    · intro _
      exact zero_mem_cycleSubset c
  · rw [cycleSubset_def]
    simp only [Finset.mem_insert, Fin.succ_ne_zero, false_or, Finset.mem_map,
      Fin.coe_succEmb, Fin.succ_inj, exists_eq_right]
    rw [mem_pathSubsetEquiv_iff]
    constructor
    · rintro ⟨j, hj0, hjL, hj⟩
      exact ⟨j, hjL, hj⟩
    · rintro ⟨j, hjL, hj⟩
      refine ⟨j, ?_, hjL, hj⟩
      by_contra h
      have hz : j = 0 := by omega
      simp [hz] at hj

def CycleGapGood {N : ℕ} (ell : ℕ) (c : Composition N) : Prop :=
  ∀ i, i < c.length → c.sizeUpTo (i + 1) ≤ c.sizeUpTo i + (2 * ell + 1)

theorem cycle_boundary_vertex {n : ℕ} (c : Composition (n + 1)) {j : ℕ}
    (hj : j < c.length) :
    ∃ v ∈ cycleSubset c, v.val = c.sizeUpTo j := by
  have hb : c.sizeUpTo j < n + 1 := by
    have := sizeUpTo_lt_of_lt c hj (le_refl _)
    simpa using this
  refine ⟨⟨c.sizeUpTo j, hb⟩, ?_, rfl⟩
  exact (mem_cycleSubset_iff c _).mpr ⟨j, hj, rfl⟩

/-- Actual domination in a cycle power is equivalent to bounding every cyclic
gap. The last gap is included and wraps from the last selected vertex to zero. -/
theorem dominates_cycle_iff_gaps {n ell : ℕ} (c : Composition (n + 1)) :
    Dominates (cyclePower (n + 1) ell) (cycleSubset c) ↔ CycleGapGood ell c := by
  rw [dominates_cyclePower_iff]
  constructor
  · intro h i hi
    by_contra hgap
    have hb := c.sizeUpTo_le (i + 1)
    let v : Fin (n + 1) := ⟨c.sizeUpTo i + ell + 1, by omega⟩
    obtain ⟨w, hw, hvw⟩ := h v
    obtain ⟨j, hj, hjv⟩ := (mem_cycleSubset_iff c w).mp hw
    rw [cyclic_near_iff] at hvw
    have hwbound := w.isLt
    dsimp [v] at hvw
    by_cases hji : j ≤ i
    · have hm := c.monotone_sizeUpTo hji
      rcases hvw with hnear | hnear | hnear <;> omega
    · have hm := c.monotone_sizeUpTo (show i + 1 ≤ j by omega)
      rcases hvw with hnear | hnear | hnear <;> omega
  · intro h v
    let i : ℕ := (c.index v).val
    have hi : i < c.length := (c.index v).isLt
    have hlo : c.sizeUpTo i ≤ v.val := c.sizeUpTo_index_le v
    have hhi : v.val < c.sizeUpTo (i + 1) := c.lt_sizeUpTo_index_succ v
    have hgap := h i hi
    obtain ⟨w, hw, hwv⟩ := cycle_boundary_vertex c hi
    by_cases hnear : v.val ≤ c.sizeUpTo i + ell
    · refine ⟨w, hw, (cyclic_near_iff v w).mpr (Or.inl ?_)⟩
      omega
    · by_cases hlast : i + 1 = c.length
      · refine ⟨0, zero_mem_cycleSubset c, (cyclic_near_iff v 0).mpr ?_⟩
        rw [hlast, c.sizeUpTo_length] at hgap hhi
        apply Or.inr (Or.inr ?_)
        simp only [Fin.val_zero]
        omega
      · obtain ⟨w', hw', hwv'⟩ := cycle_boundary_vertex c (show i + 1 < c.length by omega)
        refine ⟨w', hw', (cyclic_near_iff v w').mpr (Or.inl ?_)⟩
        omega

def cycleTranslate {n : ℕ} (d : Fin (n + 1)) (s : Finset (Fin (n + 1))) :
    Finset (Fin (n + 1)) := s.image (fun v => v + d)

theorem mem_cycleTranslate {n : ℕ} (d v : Fin (n + 1)) (s : Finset (Fin (n + 1))) :
    v ∈ cycleTranslate d s ↔ v - d ∈ s := by
  simp only [cycleTranslate, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, h⟩
    have he : w = v - d := (eq_sub_iff_add_eq).mpr h
    simpa [← he] using hw
  · intro h
    exact ⟨v - d, h, sub_add_cancel _ _⟩

@[simp] theorem cycleTranslate_card {n : ℕ} (d : Fin (n + 1))
    (s : Finset (Fin (n + 1))) : (cycleTranslate d s).card = s.card := by
  apply Finset.card_image_of_injective
  intro a b h
  exact add_right_cancel h

@[simp] theorem cycleTranslate_zero {n : ℕ} (s : Finset (Fin (n + 1))) :
    cycleTranslate 0 s = s := by simp [cycleTranslate]

theorem cycleTranslate_comp {n : ℕ} (a b : Fin (n + 1)) (s : Finset (Fin (n + 1))) :
    cycleTranslate a (cycleTranslate b s) = cycleTranslate (b + a) s := by
  simp only [cycleTranslate, Finset.image_image]
  congr 1
  funext v
  exact add_assoc v b a

theorem dominates_cycleTranslate {n ell : ℕ} (d : Fin (n + 1))
    {s : Finset (Fin (n + 1))} (h : Dominates (cyclePower (n + 1) ell) s) :
    Dominates (cyclePower (n + 1) ell) (cycleTranslate d s) := by
  intro v
  obtain ⟨w, hw, hvw⟩ := h (v - d)
  refine ⟨w + d, (mem_cycleTranslate d (w + d) s).mpr (by simpa using hw), ?_⟩
  rcases hvw with hvw | hvw
  · exact Or.inl ((sub_eq_iff_eq_add).mp hvw)
  · apply Or.inr
    have ht := (@SimpleGraph.circulantGraph_adj_translate (Fin (n + 1)) _
      {a | a.val ≤ ell} (v - d) w d).mpr hvw
    simpa only [sub_add_cancel] using ht

noncomputable def rootedCycleRank (n ell k : ℕ) : Finset (Finset (Fin (n + 1))) :=
  (familyRank (Dominates (cyclePower (n + 1) ell)) k).filter (fun s => 0 ∈ s)

theorem mem_rootedCycleRank (n ell k : ℕ) (s : Finset (Fin (n + 1))) :
    s ∈ rootedCycleRank n ell k ↔
      s.card = k ∧ Dominates (cyclePower (n + 1) ell) s ∧ (0 : Fin (n + 1)) ∈ s := by
  simp [rootedCycleRank, and_assoc]

/-- The pointing identity uses graph translation to send the marked selected
vertex to zero. No uniformity of gap tuples is assumed. -/
theorem cycle_pointing (n ell k : ℕ) :
    k * dominationCount (cyclePower (n + 1) ell) k =
      (n + 1) * (rootedCycleRank n ell k).card := by
  classical
  let D := (familyRank (Dominates (cyclePower (n + 1) ell)) k).sigma (fun s => s)
  let E := (rootedCycleRank n ell k).sigma (fun _ => (Finset.univ : Finset (Fin (n + 1))))
  have hDE : D.card = E.card := by
    apply Finset.card_nbij'
      (fun p : (s : Finset (Fin (n + 1))) × Fin (n + 1) =>
        ⟨cycleTranslate (-p.2) p.1, p.2⟩)
      (fun p : (s : Finset (Fin (n + 1))) × Fin (n + 1) =>
        ⟨cycleTranslate p.2 p.1, p.2⟩)
    · intro p hp
      rcases Finset.mem_sigma.mp hp with ⟨hp₁, hp₂⟩
      rcases (mem_familyRank _ k p.1).mp hp₁ with ⟨hc, hd⟩
      apply Finset.mem_sigma.mpr
      refine ⟨(mem_rootedCycleRank n ell k _).mpr ⟨?_, ?_, ?_⟩, by simp⟩
      · simpa using hc
      · exact dominates_cycleTranslate _ hd
      · rw [mem_cycleTranslate]
        simpa using hp₂
    · intro p hp
      rcases Finset.mem_sigma.mp hp with ⟨hp₁, hp₂⟩
      rcases (mem_rootedCycleRank n ell k p.1).mp hp₁ with ⟨hc, hd, hzero⟩
      apply Finset.mem_sigma.mpr
      refine ⟨(mem_familyRank _ k _).mpr ⟨?_, dominates_cycleTranslate _ hd⟩, ?_⟩
      · simpa using hc
      · rw [mem_cycleTranslate]
        simpa using hzero
    · intro p hp
      simp [cycleTranslate_comp]
    · intro p hp
      simp [cycleTranslate_comp]
  calc
    k * dominationCount (cyclePower (n + 1) ell) k = D.card := by
      rw [Finset.card_sigma]
      calc
        _ = ∑ s ∈ familyRank (Dominates (cyclePower (n + 1) ell)) k, k := by
          simp [dominationCount, familyRank, Nat.mul_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro s hs
          exact ((mem_familyRank _ k s).mp hs).1.symm
    _ = E.card := hDE
    _ = (n + 1) * (rootedCycleRank n ell k).card := by
      simp [E, Finset.card_sigma, Nat.mul_comm]

noncomputable def boundedCycleCompositions (n ell k : ℕ) :
    Finset (Composition (n + 1)) := by
  classical
  exact Finset.univ.filter (fun c => c.length = k ∧ CycleGapGood ell c)

theorem rootedCycleRank_card (n ell k : ℕ) :
    (rootedCycleRank n ell k).card = (boundedCycleCompositions n ell k).card := by
  classical
  symm
  apply Finset.card_bij (fun c _ => cycleSubset c)
  · intro c hc
    have hc' : c.length = k ∧ CycleGapGood ell c := (Finset.mem_filter.mp hc).2
    exact (mem_rootedCycleRank n ell k _).mpr
      ⟨by simpa [cycleSubset_card] using hc'.1,
        (dominates_cycle_iff_gaps c).mpr hc'.2, zero_mem_cycleSubset c⟩
  · intro c hc d hd hcd
    apply (cycleSubsetEquiv n).injective
    exact Subtype.ext hcd
  · intro s hs
    obtain ⟨hc, hd, hzero⟩ := (mem_rootedCycleRank n ell k s).mp hs
    let c := (cycleSubsetEquiv n).symm ⟨s, hzero⟩
    have hcs : cycleSubset c = s :=
      congrArg Subtype.val ((cycleSubsetEquiv n).apply_symm_apply ⟨s, hzero⟩)
    refine ⟨c, ?_, hcs⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [← cycleSubset_card, hcs]
      exact hc
    · exact (dominates_cycle_iff_gaps c).mp (by rwa [hcs])

theorem cycle_count_compositions (n ell k : ℕ) :
    k * dominationCount (cyclePower (n + 1) ell) k =
      (n + 1) * (boundedCycleCompositions n ell k).card := by
  rw [cycle_pointing, rootedCycleRank_card]

theorem cycleGapGood_iff_forall₂ {N ell k : ℕ} (c : Composition N) :
    (c.length = k ∧ CycleGapGood ell c) ↔
      List.Forall₂ (· ≤ ·) c.blocks (List.replicate k (2 * ell + 1)) := by
  rw [List.forall₂_iff_get]
  simp only [List.length_replicate]
  constructor
  · rintro ⟨hlen, hgap⟩
    refine ⟨hlen, ?_⟩
    intro i hi hi'
    have h := hgap i hi
    rw [c.sizeUpTo_succ hi] at h
    simp only [List.get_eq_getElem, List.getElem_replicate]
    omega
  · rintro ⟨hlen, hget⟩
    change c.length = k at hlen
    refine ⟨hlen, ?_⟩
    intro i hi
    have h := hget i hi (by omega)
    simp only [List.get_eq_getElem, List.getElem_replicate] at h
    rw [c.sizeUpTo_succ hi]
    omega

end DominationULC
