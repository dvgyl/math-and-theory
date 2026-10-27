import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.Common

namespace DominationULC

open Finset

variable {V : Type*}

/-- The usual graph-theoretic domination predicate. -/
def Dominates (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ v, ∃ w ∈ s, v = w ∨ G.Adj v w

noncomputable def dominationCount [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset V)).filter
    (fun s => s.card = k ∧ Dominates G s)).card

theorem dominationCount_eq_card [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    dominationCount G k = Nat.card {s : Finset V // s.card = k ∧ Dominates G s} := by
  classical
  simp [dominationCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The `ell`th power of the path with vertices `0,...,n-1`, using the
equivalent pair of inequalities for distance at most `ell`. -/
def pathPower (n ell : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ u.val ≤ v.val + ell ∧ v.val ≤ u.val + ell
  symm := by
    intro u v h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    intro u h
    exact h.1 rfl

theorem dominates_pathPower_iff {n ell : ℕ} {s : Finset (Fin n)} :
    Dominates (pathPower n ell) s ↔
      ∀ v : Fin n, ∃ w ∈ s, v.val ≤ w.val + ell ∧ w.val ≤ v.val + ell := by
  constructor
  · intro h v
    obtain ⟨w, hw, hvw⟩ := h v
    refine ⟨w, hw, ?_⟩
    rcases hvw with rfl | hvw
    · omega
    · exact hvw.2
  · intro h v
    obtain ⟨w, hw, hvw⟩ := h v
    refine ⟨w, hw, ?_⟩
    by_cases hv : v = w
    · exact Or.inl hv
    · exact Or.inr ⟨hv, hvw⟩

/-- A subset of the path vertices is identified with the interior boundaries
of a composition of `n+1`. This uses mathlib's proved composition equivalence. -/
def pathSubsetEquiv (n : ℕ) : Composition (n + 1) ≃ Finset (Fin n) :=
  (compositionEquiv (n + 1)).trans (compositionAsSetEquiv (n + 1))

theorem mem_pathSubsetEquiv {n : ℕ} (c : Composition (n + 1)) (v : Fin n) :
    v ∈ pathSubsetEquiv n c ↔
      (⟨v.val + 1, by omega⟩ : Fin (n + 2)) ∈ c.boundaries := by
  simp [pathSubsetEquiv, compositionAsSetEquiv, compositionEquiv,
    Composition.toCompositionAsSet, Nat.add_comm]

theorem mem_pathSubsetEquiv_iff {n : ℕ} (c : Composition (n + 1)) (v : Fin n) :
    v ∈ pathSubsetEquiv n c ↔
      ∃ j, 0 < j ∧ j < c.length ∧ c.sizeUpTo j = v.val + 1 := by
  rw [mem_pathSubsetEquiv]
  simp only [Composition.boundaries, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    have hjv : c.sizeUpTo j.val = v.val + 1 := congrArg Fin.val hj
    have hj0 : j.val ≠ 0 := by
      intro hz
      simp [hz] at hjv
    have hjL : j.val ≠ c.length := by
      intro hz
      simp [hz] at hjv
      omega
    exact ⟨j.val, by omega, by omega, hjv⟩
  · rintro ⟨j, hj0, hjL, hjv⟩
    refine ⟨⟨j, by omega⟩, ?_⟩
    apply Fin.ext
    exact hjv

def pathShift (n : ℕ) : Fin n ↪ Fin (n + 2) where
  toFun v := ⟨v.val + 1, by omega⟩
  inj' := by intro u v h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

theorem pathShift_zero_not_mem {n : ℕ} (s : Finset (Fin n)) :
    (0 : Fin (n + 2)) ∉ s.map (pathShift n) := by
  simp only [Finset.mem_map, not_exists, not_and]
  intro v hv h
  have := congrArg Fin.val h
  simp [pathShift] at this

theorem pathShift_last_not_mem {n : ℕ} (s : Finset (Fin n)) :
    Fin.last (n + 1) ∉ s.map (pathShift n) := by
  simp only [Finset.mem_map, not_exists, not_and]
  intro v hv h
  have := congrArg Fin.val h
  simp only [pathShift, Function.Embedding.coeFn_mk, Fin.val_mk, Fin.val_last] at this
  have := v.isLt
  omega

theorem path_boundaries_eq {n : ℕ} (c : Composition (n + 1)) :
    c.boundaries = insert 0 (insert (Fin.last (n + 1))
      ((pathSubsetEquiv n c).map (pathShift n))) := by
  ext v
  simp only [Finset.mem_insert, Finset.mem_map]
  constructor
  · intro hv
    by_cases h0 : v = 0
    · exact Or.inl h0
    by_cases hlast : v = Fin.last (n + 1)
    · exact Or.inr (Or.inl hlast)
    have hv0 : v.val ≠ 0 := by
      intro h
      apply h0
      exact Fin.ext h
    have hvl : v.val ≠ n + 1 := by
      intro h
      apply hlast
      exact Fin.ext h
    let w : Fin n := ⟨v.val - 1, by have := v.isLt; omega⟩
    have hw : pathShift n w = v := by apply Fin.ext; dsimp [pathShift, w]; omega
    refine Or.inr (Or.inr ⟨w, ?_, hw⟩)
    rw [mem_pathSubsetEquiv]
    simpa only [← hw] using hv
  · rintro (rfl | rfl | ⟨w, hw, rfl⟩)
    · exact c.toCompositionAsSet.zero_mem
    · exact c.toCompositionAsSet.getLast_mem
    · exact (mem_pathSubsetEquiv c w).mp hw

theorem path_card_add_one {n : ℕ} (c : Composition (n + 1)) :
    (pathSubsetEquiv n c).card + 1 = c.length := by
  have hc := c.card_boundaries_eq_succ_length
  rw [path_boundaries_eq] at hc
  have hz : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro h
    have := congrArg Fin.val h
    simp at this
  rw [Finset.card_insert_of_not_mem (by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hz, pathShift_zero_not_mem _⟩),
    Finset.card_insert_of_not_mem (pathShift_last_not_mem _), Finset.card_map] at hc
  omega

/-- Bounds on the first, last, and interior gaps of a nonempty path set. -/
def PathGapGood {n : ℕ} (ell : ℕ) (c : Composition (n + 1)) : Prop :=
  2 ≤ c.length ∧
  c.sizeUpTo 1 ≤ ell + 1 ∧
  n + 1 ≤ c.sizeUpTo (c.length - 1) + (ell + 1) ∧
  ∀ i, 0 < i → i + 1 < c.length →
    c.sizeUpTo (i + 1) ≤ c.sizeUpTo i + (2 * ell + 1)

theorem sizeUpTo_lt_of_lt {N : ℕ} (c : Composition N) {i j : ℕ}
    (hij : i < j) (hj : j ≤ c.length) : c.sizeUpTo i < c.sizeUpTo j := by
  calc
    c.sizeUpTo i < c.sizeUpTo (i + 1) := c.sizeUpTo_strict_mono (by omega)
    _ ≤ c.sizeUpTo j := c.monotone_sizeUpTo (by omega)

theorem boundary_vertex {n : ℕ} (c : Composition (n + 1)) {j : ℕ}
    (hj0 : 0 < j) (hjL : j < c.length) :
    ∃ v ∈ pathSubsetEquiv n c, v.val + 1 = c.sizeUpTo j := by
  have hp : 0 < c.sizeUpTo j := by
    have := sizeUpTo_lt_of_lt c hj0 (by omega)
    simpa using this
  have hb : c.sizeUpTo j < n + 1 := by
    have := sizeUpTo_lt_of_lt c hjL (le_refl _)
    simpa using this
  let v : Fin n := ⟨c.sizeUpTo j - 1, by omega⟩
  have hv : v.val + 1 = c.sizeUpTo j := by dsimp [v]; omega
  refine ⟨v, ?_, hv⟩
  rw [mem_pathSubsetEquiv_iff]
  exact ⟨j, hj0, hjL, hv.symm⟩

/-- The graph-theoretic domination condition is exactly the bounded-gap
condition. This is a semantic bridge, not a definition of domination counts. -/
theorem dominates_path_iff_gaps {n ell : ℕ} (hn : 0 < n)
    (c : Composition (n + 1)) :
    Dominates (pathPower n ell) (pathSubsetEquiv n c) ↔ PathGapGood ell c := by
  rw [dominates_pathPower_iff]
  constructor
  · intro h
    obtain ⟨w, hw, hwlo, hwhi⟩ := h ⟨0, hn⟩
    obtain ⟨j, hj0, hjL, hjv⟩ := (mem_pathSubsetEquiv_iff c w).mp hw
    have hL : 2 ≤ c.length := by omega
    have hfirst : c.sizeUpTo 1 ≤ ell + 1 := by
      have hm := c.monotone_sizeUpTo (show 1 ≤ j by omega)
      dsimp at hwhi
      omega
    have hlast : n + 1 ≤ c.sizeUpTo (c.length - 1) + (ell + 1) := by
      obtain ⟨w', hw', hwlo', hwhi'⟩ := h ⟨n - 1, by omega⟩
      obtain ⟨j', hj0', hjL', hjv'⟩ := (mem_pathSubsetEquiv_iff c w').mp hw'
      have hm := c.monotone_sizeUpTo (show j' ≤ c.length - 1 by omega)
      dsimp at hwlo'
      omega
    refine ⟨hL, hfirst, hlast, ?_⟩
    intro i hi0 hiL
    by_contra hgap
    have hb := c.sizeUpTo_le (i + 1)
    let v : Fin n := ⟨c.sizeUpTo i + ell, by omega⟩
    obtain ⟨w', hw', hwlo', hwhi'⟩ := h v
    obtain ⟨j', hj0', hjL', hjv'⟩ := (mem_pathSubsetEquiv_iff c w').mp hw'
    dsimp [v] at hwlo' hwhi'
    by_cases hji : j' ≤ i
    · have hm := c.monotone_sizeUpTo hji
      omega
    · have hm := c.monotone_sizeUpTo (show i + 1 ≤ j' by omega)
      omega
  · rintro ⟨hL, hfirst, hlast, hgap⟩ v
    let x : Fin (n + 1) := ⟨v.val + 1, by omega⟩
    let i : ℕ := (c.index x).val
    have hiL : i < c.length := (c.index x).isLt
    have hlo : c.sizeUpTo i ≤ v.val + 1 := c.sizeUpTo_index_le x
    have hhi : v.val + 1 < c.sizeUpTo (i + 1) := c.lt_sizeUpTo_index_succ x
    by_cases hi0 : i = 0
    · obtain ⟨w, hw, hwv⟩ := boundary_vertex c (show 0 < 1 by omega) (by omega)
      refine ⟨w, hw, ?_⟩
      simp only [hi0, zero_add] at hhi
      omega
    · by_cases hilast : i + 1 = c.length
      · obtain ⟨w, hw, hwv⟩ := boundary_vertex c (show 0 < i by omega) hiL
        refine ⟨w, hw, ?_⟩
        have hieq : c.length - 1 = i := by omega
        rw [hieq] at hlast
        have hv := v.isLt
        omega
      · have hbound := hgap i (by omega) (by omega)
        by_cases hnear : v.val + 1 ≤ c.sizeUpTo i + ell
        · obtain ⟨w, hw, hwv⟩ := boundary_vertex c (show 0 < i by omega) hiL
          exact ⟨w, hw, by omega⟩
        · obtain ⟨w, hw, hwv⟩ := boundary_vertex c (show 0 < i + 1 by omega) (by omega)
          exact ⟨w, hw, by omega⟩

theorem pathGapGood_iff_blocks {n ell : ℕ} (c : Composition (n + 1))
    (hL : 2 ≤ c.length) :
    PathGapGood ell c ↔
      ∀ i : Fin c.length, c.blocksFun i ≤
        if i.val = 0 ∨ i.val + 1 = c.length then ell + 1 else 2 * ell + 1 := by
  constructor
  · rintro ⟨_, hfirst, hlast, hgap⟩ i
    have hadd := c.sizeUpTo_succ' i
    by_cases hi0 : i.val = 0
    · simp only [hi0, true_or, if_true]
      simp only [hi0, zero_add, Composition.sizeUpTo_zero] at hadd
      omega
    · by_cases hiL : i.val + 1 = c.length
      · simp only [hiL, or_true, if_true]
        have hieq : c.length - 1 = i.val := by omega
        rw [hieq] at hlast
        rw [hiL, Composition.sizeUpTo_length] at hadd
        omega
      · simp only [hi0, hiL, or_self, if_false]
        have hg := hgap i.val (by omega) (by have := i.isLt; omega)
        omega
  · intro h
    refine ⟨hL, ?_, ?_, ?_⟩
    · let i : Fin c.length := ⟨0, by omega⟩
      have hb := h i
      have hadd := c.sizeUpTo_succ' i
      simp only [i, Fin.val_mk, true_or, if_true, zero_add,
        Composition.sizeUpTo_zero] at hb hadd
      omega
    · let i : Fin c.length := ⟨c.length - 1, by omega⟩
      have hiL : i.val + 1 = c.length := by dsimp [i]; omega
      have hb := h i
      have hadd := c.sizeUpTo_succ' i
      rw [hiL, Composition.sizeUpTo_length] at hadd
      simp only [hiL, or_true, if_true] at hb
      dsimp [i] at hb hadd
      omega
    · intro j hj0 hjL
      let i : Fin c.length := ⟨j, by omega⟩
      have hb := h i
      have hadd := c.sizeUpTo_succ' i
      have hne : j ≠ 0 ∧ j + 1 ≠ c.length := by omega
      simp only [i, Fin.val_mk, hne.1, hne.2, or_self, if_false] at hb hadd
      omega

/-- Gap bounds for a path dominating set with `k+1` selected vertices. -/
def pathBounds (ell k : ℕ) : List ℕ :=
  (ell + 1) :: (List.replicate k (2 * ell + 1) ++ [ell + 1])

@[simp] theorem pathBounds_length (ell k : ℕ) : (pathBounds ell k).length = k + 2 := by
  simp [pathBounds, Nat.add_assoc]

theorem pathBounds_get (ell k i : ℕ) (hi : i < (pathBounds ell k).length) :
    (pathBounds ell k).get ⟨i, hi⟩ =
      if i = 0 ∨ i = k + 1 then ell + 1 else 2 * ell + 1 := by
  cases i with
  | zero => simp [pathBounds]
  | succ j =>
    simp only [pathBounds, List.get_eq_getElem, List.getElem_cons_succ]
    by_cases hj : j < k
    · rw [List.getElem_append_left (by simp; exact hj)]
      have hne : j + 1 ≠ k + 1 := by omega
      have hne' : j ≠ k := by omega
      simp [hne, hne']
    · have hjeq : j = k := by simp only [pathBounds_length] at hi; omega
      subst j
      simp

theorem pathBounds_iff {n ell k : ℕ} (c : Composition (n + 1)) :
    List.Forall₂ (· ≤ ·) c.blocks (pathBounds ell k) ↔
      c.length = k + 2 ∧ PathGapGood ell c := by
  constructor
  · intro h
    have hlen : c.length = k + 2 := by simpa using h.length_eq
    refine ⟨hlen, (pathGapGood_iff_blocks c (by omega)).mpr ?_⟩
    intro i
    have hi : i.val < (pathBounds ell k).length := by simp; omega
    have hb := h.get i.isLt hi
    rw [pathBounds_get] at hb
    have hcond : (i.val = 0 ∨ i.val = k + 1) ↔
        (i.val = 0 ∨ i.val + 1 = c.length) := by omega
    simpa only [Composition.blocksFun, hcond] using hb
  · rintro ⟨hlen, hgood⟩
    apply List.forall₂_of_length_eq_of_get
    · simpa using hlen
    · intro i hi hi'
      have hb := (pathGapGood_iff_blocks c (by omega)).mp hgood ⟨i, hi⟩
      rw [pathBounds_get]
      have hcond : (i = 0 ∨ i = k + 1) ↔
          (i = 0 ∨ i + 1 = c.length) := by omega
      simpa only [Composition.blocksFun, Fin.val_mk, hcond] using hb

/-- A proved equivalence from actual dominating vertex subsets of a path
power to compositions with the corresponding individual gap bounds. -/
noncomputable def pathDominatingEquiv (n ell k : ℕ) (hn : 0 < n) :
    {s : Finset (Fin n) // s.card = k + 1 ∧ Dominates (pathPower n ell) s} ≃
      {c : Composition (n + 1) // List.Forall₂ (· ≤ ·) c.blocks (pathBounds ell k)} := by
  classical
  refine {
    toFun := fun s => ⟨(pathSubsetEquiv n).symm s.val, ?_⟩
    invFun := fun c => ⟨pathSubsetEquiv n c.val, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · rw [pathBounds_iff]
    have hc := path_card_add_one ((pathSubsetEquiv n).symm s.val)
    simp only [Equiv.apply_symm_apply, s.property.1] at hc
    refine ⟨by omega, ?_⟩
    apply (dominates_path_iff_gaps hn _).mp
    simpa using s.property.2
  · obtain ⟨hlen, hgood⟩ := (pathBounds_iff c.val).mp c.property
    have hc := path_card_add_one c.val
    exact ⟨by omega, (dominates_path_iff_gaps hn c.val).mpr hgood⟩
  · intro s
    apply Subtype.ext
    exact (pathSubsetEquiv n).apply_symm_apply s.val
  · intro c
    apply Subtype.ext
    exact (pathSubsetEquiv n).symm_apply_apply c.val

theorem path_dominationCount_eq_composition_card (n ell k : ℕ) (hn : 0 < n) :
    dominationCount (pathPower n ell) (k + 1) =
      Nat.card {c : Composition (n + 1) //
        List.Forall₂ (· ≤ ·) c.blocks (pathBounds ell k)} := by
  rw [dominationCount_eq_card]
  exact Nat.card_congr (pathDominatingEquiv n ell k hn)

end DominationULC
