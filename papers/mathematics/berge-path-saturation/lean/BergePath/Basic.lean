import Mathlib.Data.Finset.Card
import Mathlib.Order.Lattice.Nat

/-!
# Berge paths and Berge-path saturation of three-uniform hypergraphs

A hypergraph on a vertex type `V` is a finite set `H : Finset (Finset V)` of hyperedges.
Following English, Graber, Kirkpatrick, Methuku and Sullivan (arXiv:1710.03735v1), a
*Berge path of length `L`* consists of distinct vertices `v₀, …, v_L` and distinct
hyperedges `e₁, …, e_L` of `H` with `{v_{i-1}, v_i} ⊆ e_i`.  The graph path `P_m` has `m`
vertices, so a Berge-`P_m` is a Berge path of length `m - 1`.  A three-uniform hypergraph is
Berge-`P_m`-saturated when it contains no Berge-`P_m` but adding any absent three-element set
creates one; no further condition (such as linearity) is imposed on the added set.
The saturation number `sat₃(n, Berge-P_m)` is the least number of hyperedges of such a
hypergraph on `n` vertices.  Isolated vertices are allowed: the vertex set is all of `Fin n`.
-/

namespace BergePath

variable {V : Type*}

/-- `Links vs es` says that `vs = [v₀, …, v_L]` and `es = [e₁, …, e_L]` satisfy
`v_{i-1} ∈ e_i` and `v_i ∈ e_i` for every `1 ≤ i ≤ L`; in particular `vs` has one more entry
than `es`. -/
inductive Links : List V → List (Finset V) → Prop
  | single (v : V) : Links [v] []
  | cons {u v : V} {vs : List V} {e : Finset V} {es : List (Finset V)} :
      u ∈ e → v ∈ e → Links (v :: vs) es → Links (u :: v :: vs) (e :: es)

/-- A Berge path in `H` with vertex list `vs` and hyperedge list `es`: the vertices are
distinct, the hyperedges are distinct members of `H`, and consecutive vertices lie in the
hyperedge between them. Its length is `es.length`. -/
structure IsBergePath (H : Finset (Finset V)) (vs : List V) (es : List (Finset V)) : Prop where
  links : Links vs es
  vertices_nodup : vs.Nodup
  edges_nodup : es.Nodup
  edges_mem : ∀ e ∈ es, e ∈ H

/-- `H` contains a Berge copy of the path `P_m` on `m` vertices, that is, a Berge path of
length `m - 1`. -/
def ContainsBergePath (H : Finset (Finset V)) (m : ℕ) : Prop :=
  ∃ vs es, IsBergePath H vs es ∧ es.length + 1 = m

/-- Every hyperedge has exactly three vertices. -/
def IsThreeUniform (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e.card = 3

/-- `H` is a three-uniform Berge-`P_m`-saturated hypergraph: it is three-uniform, contains
no Berge-`P_m`, and adding any absent three-element vertex set creates a Berge-`P_m`. -/
def IsBergePathSaturated [DecidableEq V] (H : Finset (Finset V)) (m : ℕ) : Prop :=
  IsThreeUniform H ∧ ¬ ContainsBergePath H m ∧
    ∀ f : Finset V, f.card = 3 → f ∉ H → ContainsBergePath (insert f H) m

/-- `sat₃(n, Berge-P_m)`: the least number of hyperedges of a three-uniform
Berge-`P_m`-saturated hypergraph on the vertex set `Fin n`. -/
noncomputable def satNumber (n m : ℕ) : ℕ :=
  sInf {k | ∃ H : Finset (Finset (Fin n)), IsBergePathSaturated H m ∧ H.card = k}

theorem satNumber_le {n m : ℕ} {H : Finset (Finset (Fin n))}
    (h : IsBergePathSaturated H m) : satNumber n m ≤ H.card :=
  Nat.sInf_le ⟨H, h, rfl⟩

/-- For `m = 4s + r` with `1 ≤ r ≤ 4`, the value `a_m = (3 + r)2^s - 5` of Theorem 2.2 of
arXiv:1710.03735v1 (the least size of a three-uniform Berge-`P_m`-saturated linear tree). -/
def treeSize (m : ℕ) : ℕ :=
  (3 + (m - 4 * ((m - 1) / 4))) * 2 ^ ((m - 1) / 4) - 5

/-- The value `⌈(n - ⌊n / b⌋) / 2⌉`, `b = 2a_m + 1`, conjectured for `sat₃(n, Berge-P_m)`. -/
def conjecturedSat (m n : ℕ) : ℕ :=
  (n - n / (2 * treeSize m + 1) + 1) / 2

/-- The three-uniform case of Conjecture 2.4 of arXiv:1710.03735v1:
`sat₃(n, Berge-P_m) = ⌈(n - ⌊n / (2a_m + 1)⌋) / 2⌉` for all `m ≥ 10` and `n ≥ 2a_m + 1`. -/
def Conjecture24ThreeUniform : Prop :=
  ∀ m n : ℕ, 10 ≤ m → 2 * treeSize m + 1 ≤ n → satNumber n m = conjecturedSat m n

/-! ## Operations on Berge paths -/

theorem Links.length_eq {vs : List V} {es : List (Finset V)} (h : Links vs es) :
    vs.length = es.length + 1 := by
  induction h with
  | single v => rfl
  | cons _ _ _ ih => simp [ih]

theorem Links.map {W : Type*} (f : V ↪ W) {vs : List V} {es : List (Finset V)}
    (h : Links vs es) : Links (vs.map f) (es.map (Finset.map f)) := by
  induction h with
  | single v => exact Links.single _
  | cons hu hv _ ih => exact Links.cons (Finset.mem_map_of_mem f hu) (Finset.mem_map_of_mem f hv) ih

/-- Joining two linked lists through a new hyperedge containing the last vertex of the first
and the first vertex of the second. -/
theorem Links.join {xs ys : List V} {x y : V} {f : Finset V} {es₁ es₂ : List (Finset V)}
    (h₁ : Links (xs ++ [x]) es₁) (h₂ : Links (y :: ys) es₂) (hx : x ∈ f) (hy : y ∈ f) :
    Links (xs ++ x :: y :: ys) (es₁ ++ f :: es₂) := by
  induction xs generalizing es₁ with
  | nil =>
    cases h₁ with
    | single => exact Links.cons hx hy h₂
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases h₁ with
      | cons ha hb h =>
        cases h with
        | single => exact Links.cons ha hb (Links.cons hx hy h₂)
    | cons b xs =>
      cases h₁ with
      | cons ha hb h => exact Links.cons ha hb (ih h)

theorem Links.reverse {vs : List V} {es : List (Finset V)} (h : Links vs es) :
    Links vs.reverse es.reverse := by
  induction h with
  | single v => exact Links.single v
  | @cons u v vs e es hu hv _ ih =>
    have := Links.join (xs := vs.reverse) (ys := []) (by simpa using ih) (Links.single u) hv hu
    simpa using this

theorem IsBergePath.mono {H H' : Finset (Finset V)} (hHH' : H ⊆ H') {vs : List V}
    {es : List (Finset V)} (h : IsBergePath H vs es) : IsBergePath H' vs es :=
  ⟨h.links, h.vertices_nodup, h.edges_nodup, fun e he => hHH' (h.edges_mem e he)⟩

theorem IsBergePath.reverse {H : Finset (Finset V)} {vs : List V} {es : List (Finset V)}
    (h : IsBergePath H vs es) : IsBergePath H vs.reverse es.reverse :=
  ⟨h.links.reverse, List.nodup_reverse.2 h.vertices_nodup, List.nodup_reverse.2 h.edges_nodup,
    fun e he => h.edges_mem e (List.mem_reverse.1 he)⟩

/-- Prepending a new first vertex through a new hyperedge. -/
theorem IsBergePath.cons {H : Finset (Finset V)} {v w : V} {vs : List V} {f : Finset V}
    {es : List (Finset V)} (h : IsBergePath H (v :: vs) es) (hw : w ∉ v :: vs) (hf : f ∉ es)
    (hfH : f ∈ H) (hwf : w ∈ f) (hvf : v ∈ f) : IsBergePath H (w :: v :: vs) (f :: es) :=
  ⟨Links.cons hwf hvf h.links, List.nodup_cons.2 ⟨hw, h.vertices_nodup⟩,
    List.nodup_cons.2 ⟨hf, h.edges_nodup⟩, by
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hfH
      · exact h.edges_mem e he⟩

/-- Joining two vertex-disjoint and edge-disjoint Berge paths through a new hyperedge. -/
theorem IsBergePath.join {H : Finset (Finset V)} {xs ys : List V} {x y : V} {f : Finset V}
    {es₁ es₂ : List (Finset V)} (h₁ : IsBergePath H (xs ++ [x]) es₁)
    (h₂ : IsBergePath H (y :: ys) es₂) (hV : ∀ a ∈ xs ++ [x], a ∉ y :: ys)
    (hE : ∀ e ∈ es₁, e ∉ es₂) (hf₁ : f ∉ es₁) (hf₂ : f ∉ es₂) (hfH : f ∈ H)
    (hx : x ∈ f) (hy : y ∈ f) : IsBergePath H (xs ++ x :: y :: ys) (es₁ ++ f :: es₂) := by
  refine ⟨Links.join h₁.links h₂.links hx hy, ?_, ?_, ?_⟩
  · have h := List.nodup_append.2 ⟨h₁.vertices_nodup, h₂.vertices_nodup,
      fun a ha b hb hab => hV a ha (hab ▸ hb)⟩
    simpa using h
  · refine List.nodup_append.2 ⟨h₁.edges_nodup, List.nodup_cons.2 ⟨hf₂, h₂.edges_nodup⟩, ?_⟩
    intro a ha b hb hab
    subst hab
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hf₁ ha
    · exact hE a ha hb
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact h₁.edges_mem e he
    · rcases List.mem_cons.1 he with rfl | he
      · exact hfH
      · exact h₂.edges_mem e he

end BergePath
