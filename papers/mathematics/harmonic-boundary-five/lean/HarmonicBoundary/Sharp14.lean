import HarmonicBoundary.DistanceCertificate

/-! An actual 14-vertex graph achieving the sharp five-boundary kernel bound.
Every finite fact is proved by `decide`, not native_decide or an oracle.
The distance-table proof invokes the generic shortest-walk soundness theorem.
-/
namespace HarmonicBoundary.Sharp14
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def adjacencyTable : List (List Nat) := [
  [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0],
  [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1],
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
]

def distanceTable : List (List Nat) := [
  [0, 1, 1, 2, 3, 3, 4, 5, 5, 1, 2, 4, 6, 6],
  [1, 0, 1, 2, 3, 3, 4, 5, 5, 2, 1, 4, 6, 6],
  [1, 1, 0, 1, 2, 2, 3, 4, 4, 2, 2, 3, 5, 5],
  [2, 2, 1, 0, 1, 1, 2, 3, 3, 3, 3, 2, 4, 4],
  [3, 3, 2, 1, 0, 1, 2, 3, 3, 4, 4, 1, 4, 4],
  [3, 3, 2, 1, 1, 0, 1, 2, 2, 4, 4, 2, 3, 3],
  [4, 4, 3, 2, 2, 1, 0, 1, 1, 5, 5, 3, 2, 2],
  [5, 5, 4, 3, 3, 2, 1, 0, 1, 6, 6, 4, 1, 2],
  [5, 5, 4, 3, 3, 2, 1, 1, 0, 6, 6, 4, 2, 1],
  [1, 2, 2, 3, 4, 4, 5, 6, 6, 0, 3, 5, 7, 7],
  [2, 1, 2, 3, 4, 4, 5, 6, 6, 3, 0, 5, 7, 7],
  [4, 4, 3, 2, 1, 2, 3, 4, 4, 5, 5, 0, 5, 5],
  [6, 6, 5, 4, 4, 3, 2, 1, 2, 7, 7, 5, 0, 3],
  [6, 6, 5, 4, 4, 3, 2, 2, 1, 7, 7, 5, 3, 0]
]

def Adj (u v : Fin 14) : Prop :=
  ((adjacencyTable[u.val]!).getD v.val 0) = 1
instance (u v : Fin 14) : Decidable (Adj u v) := inferInstanceAs (Decidable (_ = _))

def dist (u v : Fin 14) : Nat :=
  (distanceTable[u.val]!).getD v.val 0

theorem simple_undirected :
    (∀ u : Fin 14, ¬ Adj u u) ∧ (∀ u v : Fin 14, Adj u v ↔ Adj v u) := by decide

theorem exactDistanceCertificate : DistanceCertificate Adj dist := by
  constructor
  · decide
  · decide
  · decide

theorem distances_are_actual_graph_distances (u v : Fin 14) :
    WalkLen Adj u v (dist u v) ∧
      ∀ n, WalkLen Adj u v n → dist u v ≤ n :=
  certified_distance_is_shortest exactDistanceCertificate u v

def score (u t : Fin 14) : Int :=
  ((List.finRange 14).map fun w =>
    if Adj u w then (dist u t : Int) - (dist w t : Int) else 0).sum

def Boundary (u : Fin 14) : Prop := ∃ t : Fin 14, 0 < score u t
instance (u : Fin 14) : Decidable (Boundary u) := by
  unfold Boundary
  infer_instance

theorem boundary_exactly_the_five_leaves :
    ∀ u : Fin 14, Boundary u ↔ 9 ≤ u.val := by decide

def boundaryVertices : List (Fin 14) := (List.finRange 14).filter fun u => decide (Boundary u)

theorem boundary_cardinality_five : boundaryVertices.length = 5 := by decide

def degree (u : Fin 14) : Nat :=
  ((List.finRange 14).filter fun w => decide (Adj u w)).length

theorem no_degree_two_vertices : ∀ u : Fin 14, degree u = 1 ∨ degree u = 3 := by decide

#print axioms exactDistanceCertificate
#print axioms distances_are_actual_graph_distances
#print axioms boundary_exactly_the_five_leaves
#print axioms boundary_cardinality_five
end HarmonicBoundary.Sharp14
