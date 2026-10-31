import BergePath.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

/-!
# Disjoint loose cycles with two isolated vertices are Berge-path saturated

For `d ≥ 3` and `t ≥ 0`, take `t` disjoint loose `d`-cycles and two isolated vertices.
Copy `j` has core vertices `c_0, …, c_{d-1}`, pendant vertices `p_0, …, p_{d-1}` and hyperedges
`e_i = {c_i, c_{i+1}, p_i}` (indices modulo `d`).  This hypergraph has `2td + 2` vertices and
`td` hyperedges, and it is Berge-`P_{d+2}`-saturated.
-/

namespace BergePath

open Fin.CommRing

variable (d t : ℕ)

/-- Vertices of `t` disjoint loose `d`-cycles and two isolated vertices: `(j, false, i)` is the
core vertex `c_i` and `(j, true, i)` the pendant vertex `p_i` of copy `j`; the two vertices
`Sum.inr k` are isolated. -/
abbrev Vtx := (Fin t × Bool × Fin d) ⊕ Fin 2

variable {d t}

/-- The core vertex `c_i` of copy `j`. -/
def core (j : Fin t) (i : Fin d) : Vtx d t := Sum.inl (j, false, i)

/-- The pendant vertex `p_i` of copy `j`. -/
def pend (j : Fin t) (i : Fin d) : Vtx d t := Sum.inl (j, true, i)

/-- The copy containing a vertex, or `none` for an isolated vertex. -/
def copyOf : Vtx d t → Option (Fin t)
  | Sum.inl p => some p.1
  | Sum.inr _ => none

@[simp] theorem core_inj {j j' : Fin t} {i i' : Fin d} : core j i = core j' i' ↔ j = j' ∧ i = i' := by
  simp [core]

@[simp] theorem pend_inj {j j' : Fin t} {i i' : Fin d} : pend j i = pend j' i' ↔ j = j' ∧ i = i' := by
  simp [pend]

@[simp] theorem core_ne_pend {j j' : Fin t} {i i' : Fin d} : core j i ≠ pend j' i' := by
  simp [core, pend]

@[simp] theorem pend_ne_core {j j' : Fin t} {i i' : Fin d} : pend j i ≠ core j' i' := by
  simp [core, pend]

@[simp] theorem copyOf_core (j : Fin t) (i : Fin d) : copyOf (core j i) = some j := rfl

@[simp] theorem copyOf_pend (j : Fin t) (i : Fin d) : copyOf (pend j i) = some j := rfl

variable [NeZero d]

/-- The hyperedge `e_i = {c_i, c_{i+1}, p_i}` of copy `j`, with indices modulo `d`. -/
def cedge (j : Fin t) (i : Fin d) : Finset (Vtx d t) := {core j i, core j (i + 1), pend j i}

variable (d t) in
/-- The hyperedges of `t` disjoint loose `d`-cycles; the two vertices `Sum.inr k` are isolated. -/
def looseCycles : Finset (Finset (Vtx d t)) :=
  Finset.univ.image fun p : Fin t × Fin d => cedge p.1 p.2

theorem mem_cedge {v : Vtx d t} {j : Fin t} {i : Fin d} :
    v ∈ cedge j i ↔ v = core j i ∨ v = core j (i + 1) ∨ v = pend j i := by
  simp [cedge]

theorem copyOf_of_mem_cedge {v : Vtx d t} {j : Fin t} {i : Fin d} (h : v ∈ cedge j i) :
    copyOf v = some j := by
  rcases mem_cedge.1 h with rfl | rfl | rfl <;> rfl

theorem cedge_inj {j j' : Fin t} {i i' : Fin d} (h : cedge j i = cedge j' i') : j = j' ∧ i = i' := by
  have hp : pend j i ∈ cedge j' i' := h ▸ (by simp [cedge])
  simpa [cedge] using hp

theorem mem_looseCycles {e : Finset (Vtx d t)} : e ∈ looseCycles d t ↔ ∃ j i, cedge j i = e := by
  simp [looseCycles]

theorem cedge_mem (j : Fin t) (i : Fin d) : cedge j i ∈ looseCycles d t :=
  mem_looseCycles.2 ⟨j, i, rfl⟩

theorem card_looseCycles : (looseCycles d t).card = t * d := by
  rw [looseCycles, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  rintro ⟨j, i⟩ ⟨j', i'⟩ h
  obtain ⟨rfl, rfl⟩ := cedge_inj h
  rfl

/-! ## Arithmetic modulo `d` -/

theorem natCast_inj_of_lt {a b : ℕ} (ha : a < d) (hb : b < d) (h : (a : Fin d) = (b : Fin d)) :
    a = b := by
  have := congrArg Fin.val h
  simpa [Fin.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

theorem natCast_ne_zero {a : ℕ} (h0 : 0 < a) (ha : a < d) : (a : Fin d) ≠ 0 := by
  rw [Ne, Fin.natCast_eq_zero]
  intro h
  exact absurd (Nat.le_of_dvd h0 h) (by omega)

theorem add_one_ne_self (hd : 2 ≤ d) (i : Fin d) : i + 1 ≠ i := by
  intro h
  have h1 : (1 : Fin d) = 0 := add_left_cancel (a := i) (h.trans (add_zero i).symm)
  exact natCast_ne_zero (d := d) (a := 1) (by norm_num) (by omega) (by simpa using h1)

theorem isThreeUniform_looseCycles (hd : 2 ≤ d) : IsThreeUniform (looseCycles d t) := by
  intro e he
  obtain ⟨j, i, rfl⟩ := mem_looseCycles.1 he
  refine Finset.card_eq_three.2 ⟨core j i, core j (i + 1), pend j i, ?_, by simp, by simp, rfl⟩
  simpa [eq_comm] using add_one_ne_self hd i

/-! ## Runs around a cycle -/

/-- The core vertices `c_i, c_{i+1}, …, c_{i+k-1}` of copy `j`. -/
def coreRun (j : Fin t) : Fin d → ℕ → List (Vtx d t)
  | _, 0 => []
  | i, k + 1 => core j i :: coreRun j (i + 1) k

/-- The vertices `c_i, c_{i+1}, …, c_{i+k-1}, p_{i+k-1}` of copy `j`. -/
def runV (j : Fin t) (i : Fin d) (k : ℕ) : List (Vtx d t) :=
  coreRun j i k ++ [pend j (i + (k : Fin d) - 1)]

/-- The hyperedges `e_i, e_{i+1}, …, e_{i+k-1}` of copy `j`. -/
def runE (j : Fin t) : Fin d → ℕ → List (Finset (Vtx d t))
  | _, 0 => []
  | i, k + 1 => cedge j i :: runE j (i + 1) k

theorem runV_zero (j : Fin t) (i : Fin d) : runV j (i + 1) 0 = [pend j i] := by
  simp [runV, coreRun]

theorem runV_succ (j : Fin t) (i : Fin d) (k : ℕ) :
    runV j i (k + 1) = core j i :: runV j (i + 1) k := by
  have h : i + ((k + 1 : ℕ) : Fin d) - 1 = i + 1 + (k : Fin d) - 1 := by
    rw [Nat.cast_succ, add_comm (k : Fin d) 1, add_assoc]
  simp only [runV, coreRun, List.cons_append, h]

theorem length_runE (j : Fin t) (i : Fin d) (k : ℕ) : (runE j i k).length = k := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [runE, ih]

theorem mem_coreRun {j : Fin t} {i : Fin d} {k : ℕ} {x : Vtx d t} (h : x ∈ coreRun j i k) :
    ∃ l < k, x = core j (i + (l : Fin d)) := by
  induction k generalizing i with
  | zero => simp [coreRun] at h
  | succ k ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨l, hl, rfl⟩ := ih h
      have h' : i + 1 + (l : Fin d) = i + ((l + 1 : ℕ) : Fin d) := by push_cast; ring
      exact ⟨l + 1, by omega, by rw [h']⟩

theorem mem_runV {j : Fin t} {i : Fin d} {k : ℕ} {x : Vtx d t} (h : x ∈ runV j i k) :
    (∃ l < k, x = core j (i + (l : Fin d))) ∨ x = pend j (i + (k : Fin d) - 1) := by
  rcases List.mem_append.1 h with h | h
  · exact Or.inl (mem_coreRun h)
  · exact Or.inr (List.mem_singleton.1 h)

theorem mem_runE {j : Fin t} {i : Fin d} {k : ℕ} {e : Finset (Vtx d t)} (h : e ∈ runE j i k) :
    ∃ l < k, e = cedge j (i + (l : Fin d)) := by
  induction k generalizing i with
  | zero => simp [runE] at h
  | succ k ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨l, hl, rfl⟩ := ih h
      have h' : i + 1 + (l : Fin d) = i + ((l + 1 : ℕ) : Fin d) := by push_cast; ring
      exact ⟨l + 1, by omega, by rw [h']⟩

theorem copyOf_of_mem_runV {j : Fin t} {i : Fin d} {k : ℕ} {x : Vtx d t} (h : x ∈ runV j i k) :
    copyOf x = some j := by
  rcases mem_runV h with ⟨l, -, rfl⟩ | rfl <;> rfl

theorem links_run (j : Fin t) (i : Fin d) (k : ℕ) : Links (runV j i k) (runE j i k) := by
  induction k generalizing i with
  | zero => simpa [runV, coreRun, runE] using Links.single (pend j (i - 1))
  | succ k ih =>
    rw [runV_succ]
    cases k with
    | zero =>
      rw [runV_zero]
      exact Links.cons (by simp [cedge]) (by simp [cedge]) (Links.single _)
    | succ k =>
      have h := ih (i + 1)
      rw [runV_succ] at h ⊢
      exact Links.cons (by simp [cedge]) (by simp [cedge]) h

theorem coreRun_nodup (j : Fin t) (i : Fin d) {k : ℕ} (hk : k ≤ d) : (coreRun j i k).Nodup := by
  induction k generalizing i with
  | zero => simp [coreRun]
  | succ k ih =>
    refine List.nodup_cons.2 ⟨fun hmem => ?_, ih (i + 1) (by omega)⟩
    obtain ⟨l, hl, hx⟩ := mem_coreRun hmem
    rw [core_inj] at hx
    have h0 : ((1 + l : ℕ) : Fin d) = 0 := by
      have := hx.2
      push_cast
      calc (1 : Fin d) + (l : Fin d) = (i + 1 + (l : Fin d)) - i := by ring
        _ = 0 := by rw [← this]; ring
    exact natCast_ne_zero (by omega) (by omega) h0

theorem runV_nodup (j : Fin t) (i : Fin d) {k : ℕ} (hk : k ≤ d) : (runV j i k).Nodup := by
  refine List.nodup_append.2 ⟨coreRun_nodup j i hk, List.nodup_singleton _, ?_⟩
  intro a ha b hb hab
  obtain ⟨l, -, rfl⟩ := mem_coreRun ha
  rw [List.mem_singleton.1 hb] at hab
  exact core_ne_pend hab

theorem runE_nodup (j : Fin t) (i : Fin d) {k : ℕ} (hk : k ≤ d) : (runE j i k).Nodup := by
  induction k generalizing i with
  | zero => simp [runE]
  | succ k ih =>
    refine List.nodup_cons.2 ⟨fun hmem => ?_, ih (i + 1) (by omega)⟩
    obtain ⟨l, hl, hx⟩ := mem_runE hmem
    have hx := (cedge_inj hx).2
    have h0 : ((1 + l : ℕ) : Fin d) = 0 := by
      push_cast
      calc (1 : Fin d) + (l : Fin d) = (i + 1 + (l : Fin d)) - i := by ring
        _ = 0 := by rw [← hx]; ring
    exact natCast_ne_zero (by omega) (by omega) h0

theorem runE_subset {j : Fin t} {i : Fin d} {k : ℕ} {e : Finset (Vtx d t)} (h : e ∈ runE j i k) :
    e ∈ looseCycles d t := by
  obtain ⟨l, -, rfl⟩ := mem_runE h
  exact cedge_mem _ _

theorem isBergePath_run (j : Fin t) (i : Fin d) {k : ℕ} (hk : k ≤ d) :
    IsBergePath (looseCycles d t) (runV j i k) (runE j i k) :=
  ⟨links_run j i k, runV_nodup j i hk, runE_nodup j i hk, fun _ he => runE_subset he⟩

/-! ## Long paths from every cycle vertex -/

/-- Every vertex of a cycle starts a Berge path through all `d` hyperedges of its copy. -/
theorem exists_path_from (hd : 3 ≤ d) {v : Vtx d t} {j : Fin t} (hv : copyOf v = some j) :
    ∃ rest es, IsBergePath (looseCycles d t) (v :: rest) es ∧ es.length = d ∧
      ∀ x ∈ v :: rest, copyOf x = some j := by
  rcases v with ⟨j', b, i⟩ | k
  · simp only [copyOf, Option.some.injEq] at hv
    subst hv
    cases b with
    | false =>
      have hp := isBergePath_run j' i (le_refl d)
      have hd' : d = (d - 1) + 1 := by omega
      have hr : runV j' i d = core j' i :: runV j' (i + 1) (d - 1) := by
        rw [← runV_succ, ← hd']
      rw [hr] at hp
      refine ⟨_, _, hp, length_runE _ _ _, fun x hx => ?_⟩
      have hx' : x ∈ runV j' i d := by rw [hr]; exact hx
      exact copyOf_of_mem_runV hx'
    | true =>
      have hp := (isBergePath_run j' (i + 1) (le_refl d)).reverse
      have hr : (runV j' (i + 1) d).reverse = pend j' i :: (coreRun j' (i + 1) d).reverse := by
        simp [runV]
      rw [hr] at hp
      refine ⟨_, _, hp, by simp [length_runE], fun x hx => ?_⟩
      have hx' : x ∈ (runV j' (i + 1) d).reverse := by rw [hr]; exact hx
      exact copyOf_of_mem_runV (List.mem_reverse.1 hx')
  · simp [copyOf] at hv

/-! ## Saturation -/

theorem not_containsBergePath_looseCycles (hd : 3 ≤ d) :
    ¬ ContainsBergePath (looseCycles d t) (d + 2) := by
  rintro ⟨vs, es, hp, hlen⟩
  -- every hyperedge of a Berge path lies in the copy of its first vertex
  have key : ∀ {vs : List (Vtx d t)} {es : List (Finset (Vtx d t))}, Links vs es →
      (∀ e ∈ es, e ∈ looseCycles d t) → ∀ j : Fin t, (∀ v ∈ vs.head?, copyOf v = some j) →
      ∀ e ∈ es, ∃ i, e = cedge j i := by
    intro vs es h
    induction h with
    | single v => simp
    | @cons u v vs e es hu hv _ ih =>
      intro hmem j hj e' he'
      obtain ⟨j', i', rfl⟩ := mem_looseCycles.1 (hmem e (by simp))
      have hj' : j' = j := by
        have := copyOf_of_mem_cedge hu
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq'] at hj
        rw [hj] at this
        exact (Option.some.inj this).symm
      subst hj'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact ⟨i', rfl⟩
      · exact ih (fun e he => hmem e (by simp [he])) j'
          (by simpa using copyOf_of_mem_cedge hv) e' he'
  cases hp.links with
  | single v => simp only [List.length_nil] at hlen; omega
  | @cons u v vs₀ e es₀ hu hv hl =>
    obtain ⟨j, i, rfl⟩ := mem_looseCycles.1 (hp.edges_mem e (by simp))
    have hall := key hp.links hp.edges_mem j (by simpa using copyOf_of_mem_cedge hu)
    have hsub : (cedge j i :: es₀).toFinset ⊆ Finset.univ.image (cedge j) := by
      intro e he
      obtain ⟨i', rfl⟩ := hall e (List.mem_toFinset.1 he)
      simp
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hp.edges_nodup] at hcard
    have := hcard.trans Finset.card_image_le
    simp at this hlen
    omega

theorem containsBergePath_of_cross (hd : 3 ≤ d) {f : Finset (Vtx d t)} (hf : f ∉ looseCycles d t)
    {u w : Vtx d t} {j : Fin t} (hu : u ∈ f) (hw : w ∈ f) (hju : copyOf u = some j)
    (hjw : copyOf w ≠ some j) : ContainsBergePath (insert f (looseCycles d t)) (d + 2) := by
  obtain ⟨rest, es, hp, hlen, hcopy⟩ := exists_path_from hd hju
  refine ⟨w :: u :: rest, f :: es, ?_, by simp [hlen]⟩
  exact (hp.mono (Finset.subset_insert _ _)).cons (fun hmem => hjw (hcopy w hmem))
    (fun hmem => hf (hp.edges_mem f hmem)) (Finset.mem_insert_self _ _) hw hu

theorem containsBergePath_of_pend_pair {f : Finset (Vtx d t)}
    (hf : f ∉ looseCycles d t) {j : Fin t} {x y : Fin d} (hxy : x ≠ y) (hx : pend j x ∈ f)
    (hy : pend j y ∈ f) : ContainsBergePath (insert f (looseCycles d t)) (d + 2) := by
  have hp := (isBergePath_run j (x + 1) (le_refl d)).reverse
  have hr : (runV j (x + 1) d).reverse = pend j x :: (coreRun j (x + 1) d).reverse := by
    simp [runV]
  rw [hr] at hp
  refine ⟨pend j y :: pend j x :: (coreRun j (x + 1) d).reverse, f :: (runE j (x + 1) d).reverse,
    ?_, by simp [length_runE]⟩
  refine (hp.mono (Finset.subset_insert _ _)).cons ?_ (fun hmem => hf (hp.edges_mem f hmem))
    (Finset.mem_insert_self _ _) hy hx
  intro hmem
  rcases List.mem_cons.1 hmem with h | h
  · exact hxy ((pend_inj.1 h).2.symm)
  · rw [List.mem_reverse] at h
    obtain ⟨l, -, hl⟩ := mem_coreRun h
    exact pend_ne_core hl

theorem containsBergePath_of_core_pair {f : Finset (Vtx d t)}
    (hf : f ∉ looseCycles d t) {j : Fin t} {x y : Fin d} (hxy : x ≠ y) (hx : core j x ∈ f)
    (hy : core j y ∈ f) : ContainsBergePath (insert f (looseCycles d t)) (d + 2) := by
  obtain ⟨k, hk⟩ : ∃ k, k = (y - x).val := ⟨_, rfl⟩
  have hkd : k < d := hk ▸ (y - x).isLt
  have hyx : y = x + (k : Fin d) := by simp [hk]
  have hk0 : 0 < k := by
    by_contra h
    have h0 : k = 0 := by omega
    apply hxy
    rw [hyx, h0]
    simp
  -- the shift between the two cores, as an identity of offsets
  have shift : ∀ l l' : ℕ, l < k → l' < d - k → x + (l : Fin d) ≠ y + (l' : Fin d) := by
    intro l l' hl hl' h
    rw [hyx] at h
    have h' : ((l : ℕ) : Fin d) = ((k + l' : ℕ) : Fin d) := by
      push_cast
      calc (l : Fin d) = (x + (l : Fin d)) - x := by ring
        _ = (x + (k : Fin d) + (l' : Fin d)) - x := by rw [h]
        _ = (k : Fin d) + (l' : Fin d) := by ring
    have := natCast_inj_of_lt (by omega) (by omega) h'
    omega
  have h₁ := (isBergePath_run j x hkd.le).reverse
  have h₂ := isBergePath_run j y (k := d - k) (by omega)
  have hV : ∀ a ∈ (runV j x k).reverse, a ∉ runV j y (d - k) := by
    intro a ha hb
    rw [List.mem_reverse] at ha
    rcases mem_runV ha with ⟨l, hl, rfl⟩ | rfl <;> rcases mem_runV hb with ⟨l', hl', hb'⟩ | hb'
    · exact shift l l' hl hl' (core_inj.1 hb').2
    · exact core_ne_pend hb'
    · exact pend_ne_core hb'
    · have h := (pend_inj.1 hb').2
      rw [hyx] at h
      have h0 : ((d - k : ℕ) : Fin d) = 0 := by
        calc ((d - k : ℕ) : Fin d)
            = (x + (k : Fin d) + ((d - k : ℕ) : Fin d) - 1) - (x + (k : Fin d) - 1) := by ring
          _ = 0 := by rw [← h]; ring
      exact natCast_ne_zero (by omega) (by omega) h0
  have hE : ∀ e ∈ (runE j x k).reverse, e ∉ runE j y (d - k) := by
    intro e he he'
    rw [List.mem_reverse] at he
    obtain ⟨l, hl, rfl⟩ := mem_runE he
    obtain ⟨l', hl', hl''⟩ := mem_runE he'
    exact shift l l' hl hl' (cedge_inj hl'').2
  have hr₁ : (runV j x k).reverse = (runV j (x + 1) (k - 1)).reverse ++ [core j x] := by
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk', runV_succ]
    simp
  have hr₂ : runV j y (d - k) = core j y :: runV j (y + 1) (d - k - 1) := by
    obtain ⟨k', hk'⟩ : ∃ k', d - k = k' + 1 := ⟨d - k - 1, by omega⟩
    rw [hk', runV_succ]
    simp
  rw [hr₁] at h₁ hV
  rw [hr₂] at h₂ hV
  have hJ := IsBergePath.join (h₁.mono (Finset.subset_insert f _))
    (h₂.mono (Finset.subset_insert f _)) hV hE
    (fun hmem => hf (runE_subset (List.mem_reverse.1 hmem))) (fun hmem => hf (runE_subset hmem))
    (Finset.mem_insert_self _ _) hx hy
  refine ⟨_, _, hJ, ?_⟩
  simp [length_runE]
  omega

/-- Lemma 7 of the manuscript: `t` disjoint loose `d`-cycles with two isolated vertices form a
three-uniform Berge-`P_{d+2}`-saturated hypergraph. -/
theorem looseCycles_saturated (hd : 3 ≤ d) : IsBergePathSaturated (looseCycles d t) (d + 2) := by
  refine ⟨isThreeUniform_looseCycles (by omega), not_containsBergePath_looseCycles hd, ?_⟩
  intro f hcard hf
  obtain ⟨x, y, z, hxy, hxz, hyz, hfeq⟩ := Finset.card_eq_three.1 hcard
  have hxm : x ∈ f := by rw [hfeq]; simp
  have hym : y ∈ f := by rw [hfeq]; simp
  have hzm : z ∈ f := by rw [hfeq]; simp
  by_cases hcross : ∃ u ∈ f, ∃ w ∈ f, ∃ j, copyOf u = some j ∧ copyOf w ≠ some j
  · obtain ⟨u, hu, w, hw, j, h₁, h₂⟩ := hcross
    exact containsBergePath_of_cross hd hf hu hw h₁ h₂
  push Not at hcross
  rcases x with ⟨cx, bx, ix⟩ | kx
  · have hy := hcross _ hxm _ hym cx rfl
    have hz := hcross _ hxm _ hzm cx rfl
    rcases y with ⟨cy, by', iy⟩ | ky
    · rcases z with ⟨cz, bz, iz⟩ | kz
      · simp only [copyOf, Option.some.injEq] at hy hz
        subst hy hz
        cases bx <;> cases by' <;> cases bz
        all_goals first
          | exact containsBergePath_of_core_pair hf (by simpa using hxy) hxm hym
          | exact containsBergePath_of_core_pair hf (by simpa using hxz) hxm hzm
          | exact containsBergePath_of_core_pair hf (by simpa using hyz) hym hzm
          | exact containsBergePath_of_pend_pair hf (by simpa using hxy) hxm hym
          | exact containsBergePath_of_pend_pair hf (by simpa using hxz) hxm hzm
          | exact containsBergePath_of_pend_pair hf (by simpa using hyz) hym hzm
      · simp [copyOf] at hz
    · simp [copyOf] at hy
  · rcases y with ⟨cy, by', iy⟩ | ky
    · have := hcross _ hym _ hxm cy rfl
      simp [copyOf] at this
    · rcases z with ⟨cz, bz, iz⟩ | kz
      · have := hcross _ hzm _ hxm cz rfl
        simp [copyOf] at this
      · exfalso
        have h₁ : kx ≠ ky := fun h => hxy (by rw [h])
        have h₂ : kx ≠ kz := fun h => hxz (by rw [h])
        have h₃ : ky ≠ kz := fun h => hyz (by rw [h])
        exact (by decide : ∀ a b c : Fin 2, a ≠ b → a ≠ c → b ≠ c → False) kx ky kz h₁ h₂ h₃

end BergePath
