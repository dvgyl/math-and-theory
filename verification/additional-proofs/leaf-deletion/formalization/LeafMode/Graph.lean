import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.DeriveFintype

namespace LeafMode

inductive V (n k l : ℕ)
  | root : V n k l
  | u : Fin n → V n k l
  | v : Fin n → V n k l
  | tip : Fin n → Fin k → V n k l
  | extra : Fin l → V n k l
  deriving DecidableEq, Fintype

open V

def parent {n k l : ℕ} : V n k l → V n k l
  | root => root
  | u _ => root
  | v i => u i
  | tip i _ => v i
  | extra _ => root

def depth {n k l : ℕ} : V n k l → ℕ
  | root => 0
  | u _ => 1
  | v _ => 2
  | tip _ _ => 3
  | extra _ => 1

@[simp] theorem parent_ne_self {n k l : ℕ} {x : V n k l} (h : x ≠ root) :
    parent x ≠ x := by
  cases x <;> simp_all [parent]

theorem depth_parent_lt {n k l : ℕ} {x : V n k l} (h : x ≠ root) :
    depth (parent x) < depth x := by
  cases x <;> simp_all [parent, depth]

def graph (n k l : ℕ) : SimpleGraph (V n k l) where
  Adj x y := (x ≠ root ∧ parent x = y) ∨ (y ≠ root ∧ parent y = x)
  symm := by intro x y h; exact h.symm
  loopless := by intro x h; rcases h with h | h <;> exact parent_ne_self h.1 h.2

@[simp] theorem graph_adj {n k l : ℕ} {x y : V n k l} :
    (graph n k l).Adj x y ↔
      (x ≠ root ∧ parent x = y) ∨ (y ≠ root ∧ parent y = x) := Iff.rfl

instance {n k l : ℕ} : DecidableRel (graph n k l).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))


theorem graph_connected (n k l : ℕ) : (graph n k l).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable (graph n k l)).mpr
  refine ⟨root, ?_⟩
  have hu (i : Fin n) : (graph n k l).Reachable root (u i) :=
    SimpleGraph.Adj.reachable (by simp [parent])
  have hv (i : Fin n) : (graph n k l).Reachable root (v i) :=
    (hu i).trans (SimpleGraph.Adj.reachable (by simp [parent]))
  intro x
  cases x with
  | root => exact SimpleGraph.Reachable.refl _
  | u i => exact hu i
  | v i => exact hv i
  | tip i j => exact (hv i).trans (SimpleGraph.Adj.reachable (by simp [parent]))
  | extra j => exact SimpleGraph.Adj.reachable (by simp [parent])

noncomputable def childEdge {n k l : ℕ} (x : {x : V n k l // x ≠ root}) :
    (graph n k l).edgeSet :=
  ⟨s(x.val, parent x.val), (SimpleGraph.mem_edgeSet _).mpr (Or.inl ⟨x.property, rfl⟩)⟩

theorem childEdge_bijective (n k l : ℕ) :
    Function.Bijective (@childEdge n k l) := by
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    change s(x.val, parent x.val) = s(y.val, parent y.val) at he
    rcases Sym2.eq_iff.mp he with he | he
    · exact Subtype.ext he.1
    · have hx := depth_parent_lt x.property
      have hy := depth_parent_lt y.property
      rw [he.2, he.1] at hx
      omega
  · rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
      have ha := (SimpleGraph.mem_edgeSet _).mp he
      change (x ≠ root ∧ parent x = y) ∨ (y ≠ root ∧ parent y = x) at ha
      rcases ha with ⟨hx, hxy⟩ | ⟨hy, hyx⟩
      · refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
        simp [childEdge, hxy]
      · refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
        simp [childEdge, hyx, Sym2.eq_swap]

theorem graph_isTree (n k l : ℕ) : (graph n k l).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨graph_connected n k l, ?_⟩
  rw [← Nat.card_congr (Equiv.ofBijective childEdge (childEdge_bijective n k l))]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have h : 0 < Fintype.card (V n k l) := Fintype.card_pos_iff.mpr ⟨root⟩
  omega


@[simp] theorem extra_adj_iff {n k l : ℕ} (j : Fin l) (y : V n k l) :
    (graph n k l).Adj (extra j) y ↔ y = root := by
  cases y <;> simp [parent]

theorem extra_degree {n k l : ℕ} (j : Fin l) :
    (graph n k l).degree (extra j) = 1 := by
  have hn : (graph n k l).neighborFinset (extra j) = {root} := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, extra_adj_iff, Finset.mem_singleton]
  rw [SimpleGraph.degree, hn]
  simp

def embedCore {n k : ℕ} : V n k 0 → V n k 1
  | root => root
  | u i => u i
  | v i => v i
  | tip i j => tip i j
  | extra j => Fin.elim0 j

@[simp] theorem embedCore_ne_extra {n k : ℕ} (x : V n k 0) :
    embedCore x ≠ extra 0 := by
  cases x <;> simp [embedCore]
  next j => exact Fin.elim0 j

def deleteLeafEquiv (n k : ℕ) : V n k 0 ≃ {x : V n k 1 // x ≠ extra 0} where
  toFun x := ⟨embedCore x, embedCore_ne_extra x⟩
  invFun x := match h : x.val with
    | root => root
    | u i => u i
    | v i => v i
    | tip i j => tip i j
    | extra j => False.elim (x.property (h.trans (congrArg extra (Fin.eq_zero j))))
  left_inv x := by
    cases x <;> simp [embedCore]
    next j => exact Fin.elim0 j
  right_inv x := by
    rcases x with ⟨x, hx⟩
    cases x <;> simp [embedCore]
    next j => exact False.elim (hx (congrArg extra (Fin.eq_zero j)))

def deleteLeafIso (n k : ℕ) :
    graph n k 0 ≃g (graph n k 1).induce {x | x ≠ extra 0} where
  toEquiv := deleteLeafEquiv n k
  map_rel_iff' := by
    intro x y
    change (graph n k 1).Adj (embedCore x) (embedCore y) ↔ (graph n k 0).Adj x y
    cases x <;> cases y <;> simp [embedCore, graph_adj, parent]
    all_goals exact Fin.elim0 ‹Fin 0›

end LeafMode
