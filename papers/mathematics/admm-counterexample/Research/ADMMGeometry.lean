import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Elementary Euclidean geometry used by the exact ADMM cycle certificate.

The ambient vectors are four real coordinates, with the explicitly specified
Euclidean dot product and squared distance. The feasible sets are the actual
convex hulls of their five displayed vertices. No projection axioms are used:
the vertex normal inequalities below prove unique global minimization of the
quadratic distance over the entire convex hull.
-/

namespace ADMMGeometry

open scoped BigOperators

abbrev Vec := Fin 4 → ℝ
abbrev Vertices := Fin 5 → Vec

def dot (x y : Vec) : ℝ := ∑ j, x j * y j

def sqDist (x y : Vec) : ℝ := ∑ j, (x j - y j) ^ 2

def polytope (v : Vertices) : Set Vec := convexHull ℝ (Set.range v)

/-- `p` is the unique global minimizer of Euclidean squared distance from `q`
over `S`. This is the usual Euclidean projection property. -/
def IsProjection (S : Set Vec) (q p : Vec) : Prop :=
  p ∈ S ∧
  (∀ y ∈ S, sqDist q p ≤ sqDist q y) ∧
  (∀ y ∈ S, sqDist q y ≤ sqDist q p → y = p)

theorem vertex_mem_polytope (v : Vertices) (i : Fin 5) : v i ∈ polytope v := by
  exact subset_convexHull ℝ (Set.range v) (Set.mem_range_self i)

theorem convex_polytope (v : Vertices) : Convex ℝ (polytope v) := by
  exact convex_convexHull ℝ (Set.range v)

theorem compact_polytope (v : Vertices) : IsCompact (polytope v) := by
  exact (Set.finite_range v).isCompact_convexHull

theorem closed_polytope (v : Vertices) : IsClosed (polytope v) := by
  exact (compact_polytope v).isClosed

theorem zero_mem_polytope (v : Vertices) (hs : ∑ i, v i = 0) :
    (0 : Vec) ∈ polytope v := by
  apply mem_convexHull_of_exists_fintype (fun _ : Fin 5 => (1 / 5 : ℝ)) v
  · intro i
    norm_num
  · norm_num
  · intro i
    exact Set.mem_range_self i
  · rw [← Finset.smul_sum, hs, smul_zero]

theorem dot_add_right (a x y : Vec) : dot a (x + y) = dot a x + dot a y := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_smul_right (a x : Vec) (c : ℝ) : dot a (c • x) = c * dot a x := by
  simp [dot, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem dot_affine_combination (a p x y : Vec) (s t : ℝ) (hst : s + t = 1) :
    dot a (s • x + t • y - p) = s * dot a (x - p) + t * dot a (y - p) := by
  have hvec : s • x + t • y - p = s • (x - p) + t • (y - p) := by
    ext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      s * x j + t * y j - p j = s * x j + t * y j - (s + t) * p j := by
        rw [hst, one_mul]
      _ = s * (x j - p j) + t * (y j - p j) := by ring
  rw [hvec, dot_add_right, dot_smul_right, dot_smul_right]

/-- A vertexwise supporting halfspace inequality holds on the whole polytope. -/
theorem normal_on_polytope (v : Vertices) (p a : Vec)
    (h : ∀ i, dot a (v i - p) ≤ 0) :
    ∀ y ∈ polytope v, dot a (y - p) ≤ 0 := by
  have hhalf : Convex ℝ {y : Vec | dot a (y - p) ≤ 0} := by
    intro x hx y hy s t hs ht hst
    change dot a (s • x + t • y - p) ≤ 0
    rw [dot_affine_combination a p x y s t hst]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hs hx)
      (mul_nonpos_of_nonneg_of_nonpos ht hy)
  have hsub : Set.range v ⊆ {y : Vec | dot a (y - p) ≤ 0} := by
    rintro y ⟨i, rfl⟩
    exact h i
  exact convexHull_min hsub hhalf

theorem sqDist_nonneg (x y : Vec) : 0 ≤ sqDist x y := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i - y i)

theorem sqDist_self (x : Vec) : sqDist x x = 0 := by
  simp [sqDist]

theorem eq_of_sqDist_eq_zero (x y : Vec) (h : sqDist x y = 0) : x = y := by
  have hall : ∀ i ∈ (Finset.univ : Finset (Fin 4)), (x i - y i) ^ 2 = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i - y i))).mp h
  ext i
  have hi := hall i (Finset.mem_univ i)
  nlinarith [sq_nonneg (x i - y i)]

theorem squared_distance_identity (q p y : Vec) :
    sqDist q y = sqDist q p + sqDist y p - 2 * dot (q - p) (y - p) := by
  simp [sqDist, dot, Fin.sum_univ_succ]
  ring

/-- Finite normal-cone checks certify the actual unique Euclidean projection. -/
theorem projection_of_vertex_normals (v : Vertices) (i : Fin 5) (q : Vec)
    (h : ∀ j, dot (q - v i) (v j - v i) ≤ 0) :
    IsProjection (polytope v) q (v i) := by
  refine ⟨vertex_mem_polytope v i, ?_, ?_⟩
  · intro y hy
    have hn := normal_on_polytope v (v i) (q - v i) h y hy
    have hd := squared_distance_identity q (v i) y
    have hz := sqDist_nonneg y (v i)
    linarith
  · intro y hy hmin
    have hn := normal_on_polytope v (v i) (q - v i) h y hy
    have hd := squared_distance_identity q (v i) y
    have hz := sqDist_nonneg y (v i)
    apply eq_of_sqDist_eq_zero y (v i)
    linarith

end ADMMGeometry
