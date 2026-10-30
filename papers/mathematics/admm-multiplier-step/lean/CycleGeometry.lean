import ProximalModel
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Group.Fin.Basic

set_option autoImplicit false

open scoped BigOperators

namespace ADMMCycle

variable {ι : Type*} [Fintype ι]

abbrev Vec (ι : Type*) := EuclideanSpace ℝ ι

noncomputable def ofInt (a : ι → ℤ) : Vec ι :=
  (WithLp.equiv 2 _).symm (fun j => (a j : ℝ))

@[simp] theorem ofInt_apply (a : ι → ℤ) (j : ι) : ofInt a j = (a j : ℝ) := rfl

theorem vec_sum_apply {κ : Type*} [Fintype κ] (f : κ → Vec ι) (j : ι) :
    (∑ i, f i) j = ∑ i, f i j := by
  let ev : Vec ι →+ ℝ := { toFun := fun v => v j, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum ev f Finset.univ

theorem inner_ofInt (a b : ι → ℤ) :
    @inner ℝ (Vec ι) _ (ofInt a) (ofInt b) = ((∑ j, a j * b j : ℤ) : ℝ) := by
  simp [PiLp.inner_apply, ofInt, RCLike.inner_apply, Int.cast_sum, Int.cast_mul, mul_comm]

theorem ofInt_add (a b : ι → ℤ) : ofInt (a + b) = ofInt a + ofInt b := by
  ext j
  simp

theorem ofInt_sub (a b : ι → ℤ) : ofInt (a - b) = ofInt a - ofInt b := by
  ext j
  simp

noncomputable def polytope {κ : Type*} (v : κ → Vec ι) : Set (Vec ι) :=
  convexHull ℝ (Set.range v)

theorem vertex_mem_polytope {κ : Type*} (v : κ → Vec ι) (i : κ) :
    v i ∈ polytope v := subset_convexHull ℝ _ (Set.mem_range_self i)

theorem convex_polytope {κ : Type*} (v : κ → Vec ι) : Convex ℝ (polytope v) :=
  convex_convexHull ℝ _

theorem compact_polytope {κ : Type*} [Fintype κ] (v : κ → Vec ι) :
    IsCompact (polytope v) := (Set.finite_range v).isCompact_convexHull

theorem zero_mem_polytope {κ : Type*} [Fintype κ] [Nonempty κ] (v : κ → Vec ι)
    (hsum : ∑ i, v i = 0) : (0 : Vec ι) ∈ polytope v := by
  have hc : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.mpr Fintype.card_pos
  apply mem_convexHull_of_exists_fintype (fun _ : κ => (Fintype.card κ : ℝ)⁻¹) v
  · intro i
    positivity
  · simp [Finset.sum_const, nsmul_eq_mul, ne_of_gt hc]
  · intro i
    exact Set.mem_range_self i
  · rw [← Finset.smul_sum, hsum, smul_zero]

theorem normal_on_polytope {κ : Type*} (v : κ → Vec ι) (p a : Vec ι)
    (h : ∀ i, @inner ℝ (Vec ι) _ a (v i - p) ≤ 0) :
    ∀ y ∈ polytope v, @inner ℝ (Vec ι) _ a (y - p) ≤ 0 := by
  have hhalf : Convex ℝ {y : Vec ι | @inner ℝ (Vec ι) _ a (y - p) ≤ 0} := by
    intro x hx y hy s t hs ht hst
    have he : s • x + t • y - p = s • (x - p) + t • (y - p) := by
      ext j
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      calc
        s * x j + t * y j - p j = s * x j + t * y j - (s + t) * p j := by
          rw [hst, one_mul]
        _ = s * (x j - p j) + t * (y j - p j) := by ring
    change @inner ℝ (Vec ι) _ a (s • x + t • y - p) ≤ 0
    rw [he, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hs hx)
      (mul_nonpos_of_nonneg_of_nonpos ht hy)
  exact convexHull_min (by rintro y ⟨i, rfl⟩; exact h i) hhalf

theorem prox_of_vertex_normals {κ : Type*} (v : κ → Vec ι) (i : κ) (q : Vec ι)
    (h : ∀ j, @inner ℝ (Vec ι) _ (q - v i) (v j - v i) ≤ 0) :
    ADMM74.IsProx (polytope v) (fun _ => 0) q (v i) := by
  apply ADMM74.isProx_of_supports
  refine ⟨vertex_mem_polytope v i, ?_⟩
  intro y hy
  simpa only [zero_add] using normal_on_polytope v (v i) (q - v i) h y hy

theorem prox_unique {κ : Type*} (v : κ → Vec ι) {q x y : Vec ι}
    (hx : ADMM74.IsProx (polytope v) (fun _ => 0) q x)
    (hy : ADMM74.IsProx (polytope v) (fun _ => 0) q y) : x = y :=
  ADMM74.isProx_unique (convexOn_const 0 (convex_polytope v)) hx hy

section Shift

variable [AddCommGroup ι]

noncomputable def shift (i : ι) (v : Vec ι) : Vec ι :=
  (WithLp.equiv 2 _).symm (fun j => v (i + j))

@[simp] theorem shift_apply (i j : ι) (v : Vec ι) : shift i v j = v (i + j) := rfl

@[simp] theorem shift_zero (v : Vec ι) : shift 0 v = v := by
  ext j
  change v (0 + j) = v j
  rw [zero_add]

theorem shift_add (i j : ι) (v : Vec ι) : shift (i + j) v = shift i (shift j v) := by
  ext k
  change v ((i + j) + k) = v (j + (i + k))
  rw [add_assoc, add_left_comm]

theorem shift_add_vec (i : ι) (v w : Vec ι) : shift i (v + w) = shift i v + shift i w := by
  ext j
  rfl

theorem shift_sub (i : ι) (v w : Vec ι) : shift i (v - w) = shift i v - shift i w := by
  ext j
  rfl

theorem shift_smul (i : ι) (c : ℝ) (v : Vec ι) : shift i (c • v) = c • shift i v := by
  ext j
  rfl

theorem inner_shift (i : ι) (v w : Vec ι) :
    @inner ℝ (Vec ι) _ (shift i v) (shift i w) = @inner ℝ (Vec ι) _ v w := by
  simp only [PiLp.inner_apply, shift_apply]
  exact Equiv.sum_comp (Equiv.addLeft i) (fun j => @inner ℝ ℝ _ (v j) (w j))

theorem norm_shift (i : ι) (v : Vec ι) : ‖shift i v‖ = ‖v‖ := by
  have h := inner_shift i v v
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (shift i v), norm_nonneg v]

theorem inner_shift_difference (i j : ι) (a p v : Vec ι) :
    @inner ℝ (Vec ι) _ (shift i a) (shift j v - shift i p) =
      @inner ℝ (Vec ι) _ a (shift (j - i) v - p) := by
  have hj : shift j v = shift i (shift (j - i) v) := by
    rw [← shift_add]
    rw [show i + (j - i) = j by abel]
  rw [hj, ← shift_sub, inner_shift]

theorem sum_shift_eq_zero (v : Vec ι) (hsum : ∑ j, v j = 0) : ∑ i, shift i v = 0 := by
  ext j
  rw [vec_sum_apply]
  change (∑ i, v (i + j)) = 0
  exact (Equiv.sum_comp (Equiv.addRight j) v).trans hsum

end Shift

end ADMMCycle
