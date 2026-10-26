module
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
The explicit connected 14-vertex graph used in the DomiRank counterexample.
Vertices 1,2 form K2; 3,4,5 and 6,7,8 form two K3 components.
Each of 0,1,2 is adjacent to every vertex 3,...,9.
Vertex 9 is also adjacent to the four leaves 10,...,13.
-/
@[expose] public section

namespace MathAndTheory.DomiRank
open Matrix

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- The exact zero-one adjacency data, with no loops. -/
def adjData : Matrix (Fin 14) (Fin 14) ℕ := ![
  ![0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
  ![0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
  ![1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0],
  ![1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
  ![1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]]

/-- The graph is the finite simple graph specified by the adjacency data. -/
def graph : SimpleGraph (Fin 14) where
  Adj i j := adjData i j = 1
  symm := ⟨by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [adjData]⟩
  loopless := ⟨by decide⟩

instance graphAdjDecidable : DecidableRel graph.Adj := fun i j =>
  inferInstanceAs (Decidable (adjData i j = 1))

/-- The real adjacency matrix of the explicit graph. -/
def A : Matrix (Fin 14) (Fin 14) ℝ := fun i j => (adjData i j : ℝ)

theorem A_eq_adjMatrix : A = graph.adjMatrix ℝ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, adjData, graph, SimpleGraph.adjMatrix_apply, Matrix.map_apply]

/-- Its row sums are the usual vertex degrees. -/
def degree : Fin 14 → ℝ := A *ᵥ (fun _ => 1)

theorem degree_eq : degree = ![7,8,8,5,5,5,5,5,5,7,1,1,1,1] := by
  ext i
  fin_cases i <;>
    norm_num [degree, A, adjData, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem degree_eq_graph_degree (i : Fin 14) : degree i = (graph.degree i : ℝ) := by
  rw [degree, A_eq_adjMatrix]
  simpa using (SimpleGraph.adjMatrix_mulVec_const_apply (G := graph) (α := ℝ) (a := 1) (v := i))

/-- Every vertex can be reached from vertex 9 in at most two edges. -/
theorem graph_connected : graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨9, ?_⟩
  intro i
  fin_cases i
  · exact (show graph.Adj 9 0 by decide).reachable
  · exact (show graph.Adj 9 1 by decide).reachable
  · exact (show graph.Adj 9 2 by decide).reachable
  · exact (show graph.Adj 9 0 by decide).reachable.trans
      (show graph.Adj 0 3 by decide).reachable
  · exact (show graph.Adj 9 0 by decide).reachable.trans
      (show graph.Adj 0 4 by decide).reachable
  · exact (show graph.Adj 9 0 by decide).reachable.trans
      (show graph.Adj 0 5 by decide).reachable
  · exact (show graph.Adj 9 0 by decide).reachable.trans
      (show graph.Adj 0 6 by decide).reachable
  · exact (show graph.Adj 9 0 by decide).reachable.trans
      (show graph.Adj 0 7 by decide).reachable
  · exact (show graph.Adj 9 0 by decide).reachable.trans
      (show graph.Adj 0 8 by decide).reachable
  · exact SimpleGraph.Reachable.refl _
  · exact (show graph.Adj 9 10 by decide).reachable
  · exact (show graph.Adj 9 11 by decide).reachable
  · exact (show graph.Adj 9 12 by decide).reachable
  · exact (show graph.Adj 9 13 by decide).reachable

/-- The DomiRank resolvent matrix. -/
def resolvent (s : ℝ) : Matrix (Fin 14) (Fin 14) ℝ := 1 + s • A

end MathAndTheory.DomiRank
