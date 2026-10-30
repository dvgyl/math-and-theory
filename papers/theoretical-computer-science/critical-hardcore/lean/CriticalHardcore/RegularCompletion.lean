import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
An explicit regular completion of a finite graph.

There are `2 * Δ` copies of the original vertex set. Original edges remain
inside each copy. At each vertex, its degree deficiency is supplied by
disjoint perfect matchings between the two Boolean sides of `Fin Δ × Bool`.
The construction preserves each original copy as an induced subgraph.
-/

set_option autoImplicit false

namespace CriticalHardcore
namespace RegularCompletion

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Copy (Δ : ℕ) := Fin Δ × Bool

abbrev Vertex (V : Type*) (Δ : ℕ) := V × Copy Δ

/-- The `s`-th matching on the copy set. -/
def flipShift {Δ : ℕ} [NeZero Δ] (c : Copy Δ) (s : Fin Δ) : Copy Δ :=
  if c.2 then (c.1 - s, false) else (c.1 + s, true)

theorem flipShift_involutive {Δ : ℕ} [NeZero Δ] (c : Copy Δ) (s : Fin Δ) :
    flipShift (flipShift c s) s = c := by
  rcases c with ⟨a, b⟩
  cases b <;> simp [flipShift]

theorem flipShift_ne {Δ : ℕ} [NeZero Δ] (c : Copy Δ) (s : Fin Δ) :
    flipShift c s ≠ c := by
  rcases c with ⟨a, b⟩
  cases b <;> simp [flipShift]

theorem flipShift_injective {Δ : ℕ} [NeZero Δ] (c : Copy Δ) :
    Function.Injective (flipShift c) := by
  rcases c with ⟨a, b⟩
  cases b <;> intro s t h <;> simpa [flipShift] using h

variable (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) [NeZero Δ]

def deficiency (v : V) : ℕ := Δ - G.degree v

def slot (v : V) (j : Fin (deficiency G Δ v)) : Fin Δ :=
  j.castLE (Nat.sub_le Δ (G.degree v))

theorem slot_injective (v : V) : Function.Injective (slot G Δ v) :=
  Fin.castLE_injective (Nat.sub_le Δ (G.degree v))

def vertical (x : Vertex V Δ) (j : Fin (deficiency G Δ x.1)) : Vertex V Δ :=
  (x.1, flipShift x.2 (slot G Δ x.1 j))

@[simp] theorem vertical_fst (x : Vertex V Δ) (j : Fin (deficiency G Δ x.1)) :
    (vertical G Δ x j).1 = x.1 := rfl

theorem vertical_involutive (x : Vertex V Δ) (j : Fin (deficiency G Δ x.1)) :
    vertical G Δ (vertical G Δ x j) j = x := by
  rcases x with ⟨v, c⟩
  simp [vertical, flipShift_involutive]

theorem vertical_ne (x : Vertex V Δ) (j : Fin (deficiency G Δ x.1)) :
    vertical G Δ x j ≠ x := by
  intro h
  exact flipShift_ne x.2 (slot G Δ x.1 j) (congrArg Prod.snd h)

theorem vertical_injective (x : Vertex V Δ) : Function.Injective (vertical G Δ x) := by
  intro i j h
  apply slot_injective G Δ x.1
  exact flipShift_injective x.2 (congrArg Prod.snd h)

def graph : SimpleGraph (Vertex V Δ) where
  Adj x y := (G.Adj x.1 y.1 ∧ x.2 = y.2) ∨ ∃ j, vertical G Δ x j = y
  symm := by
    intro x y h
    rcases h with ⟨hxy, hc⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨G.symm hxy, hc.symm⟩
    · exact Or.inr ⟨j, vertical_involutive G Δ x j⟩
  loopless := by
    intro x h
    rcases h with ⟨hxx, _⟩ | ⟨j, hj⟩
    · exact G.loopless x.1 hxx
    · exact vertical_ne G Δ x j hj

instance graph_decidableAdj : DecidableRel (graph G Δ).Adj := by
  intro x y
  change Decidable ((G.Adj x.1 y.1 ∧ x.2 = y.2) ∨ ∃ j, vertical G Δ x j = y)
  infer_instance

theorem graph_adj_iff (x y : Vertex V Δ) :
    (graph G Δ).Adj x y ↔
      (G.Adj x.1 y.1 ∧ x.2 = y.2) ∨ ∃ j, vertical G Δ x j = y := Iff.rfl

theorem neighbors_eq (x : Vertex V Δ) :
    (graph G Δ).neighborFinset x =
      (G.neighborFinset x.1).image (fun w => (w, x.2)) ∪
        Finset.univ.image (vertical G Δ x) := by
  ext y
  rcases y with ⟨w, c⟩
  simp only [SimpleGraph.mem_neighborFinset, graph_adj_iff, Finset.mem_union,
    Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro (⟨h, hc⟩ | h)
    · exact Or.inl ⟨w, h, rfl, hc⟩
    · exact Or.inr h
  · rintro (⟨u, hu, rfl, hc⟩ | h)
    · exact Or.inl ⟨hu, hc⟩
    · exact Or.inr h

theorem neighbor_parts_disjoint (x : Vertex V Δ) :
    Disjoint ((G.neighborFinset x.1).image (fun w => (w, x.2)))
      (Finset.univ.image (vertical G Δ x)) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hz'
  exact G.ne_of_adj ((G.mem_neighborFinset x.1 w).mp hw) (congrArg Prod.fst hj)

theorem degree_eq (hdegree : ∀ v : V, G.degree v ≤ Δ) (x : Vertex V Δ) :
    (graph G Δ).degree x = Δ := by
  rw [SimpleGraph.degree, neighbors_eq,
    Finset.card_union_of_disjoint (neighbor_parts_disjoint G Δ x)]
  rw [Finset.card_image_of_injective _ (by
    intro v w h
    exact congrArg Prod.fst h)]
  rw [Finset.card_image_of_injective _ (vertical_injective G Δ x)]
  simp only [Finset.card_univ, Fintype.card_fin,
    SimpleGraph.card_neighborFinset_eq_degree, deficiency]
  simpa only [Nat.add_comm] using Nat.sub_add_cancel (hdegree x.1)

theorem regular (hdegree : ∀ v : V, G.degree v ≤ Δ) :
    (graph G Δ).IsRegularOfDegree Δ := degree_eq G Δ hdegree

/-- Every one of the `2 * Δ` original copies is induced. -/
def embedding (c : Copy Δ) : G ↪g graph G Δ where
  toFun v := (v, c)
  inj' := by intro v w h; exact congrArg Prod.fst h
  map_rel_iff' := by
    intro v w
    change ((G.Adj v w ∧ c = c) ∨ ∃ j, vertical G Δ (v, c) j = (w, c)) ↔ G.Adj v w
    constructor
    · rintro (⟨h, _⟩ | ⟨j, hj⟩)
      · exact h
      · exact False.elim (flipShift_ne c (slot G Δ v j) (congrArg Prod.snd hj))
    · intro h
      exact Or.inl ⟨h, rfl⟩

@[simp] theorem embedding_apply (c : Copy Δ) (v : V) :
    embedding G Δ c v = (v, c) := rfl

def canonicalEmbedding : G ↪g graph G Δ := embedding G Δ (0, false)

@[simp] theorem canonicalEmbedding_apply (v : V) :
    canonicalEmbedding G Δ v = (v, (0, false)) := rfl

theorem card_vertex : Fintype.card (Vertex V Δ) = 2 * Δ * Fintype.card V := by
  simp [Vertex, Copy, Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end RegularCompletion
end CriticalHardcore
