import Proximal
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace FiniteCP

open CPSharpness

variable {n d : ℕ} [NeZero n]

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

def hull (x : Fin n → Space d) : Set (Space d) := convexHull ℝ (Set.range x)

omit [NeZero n] in
theorem mem_hull (x : Fin n → Space d) (i : Fin n) : x i ∈ hull x :=
  subset_convexHull ℝ _ (Set.mem_range_self i)

omit [NeZero n] in
theorem hull_convex (x : Fin n → Space d) : Convex ℝ (hull x) := convex_convexHull ℝ _

omit [NeZero n] in
theorem hull_compact (x : Fin n → Space d) : IsCompact (hull x) :=
  (Set.finite_range x).isCompact_convexHull

theorem hull_nonempty (x : Fin n → Space d) : (hull x).Nonempty :=
  ⟨x 0, mem_hull x 0⟩

omit [NeZero n] in
theorem supports_of_vertices (x : Fin n → Space d) (i : Fin n) (p : Space d)
    (h : ∀ j, ⟪p, x j - x i⟫ ≤ 0) : Supports (hull x) (fun _ => 0) (x i) p := by
  refine ⟨mem_hull x i, ?_⟩
  have hc : Convex ℝ {w : Space d | ⟪p, w - x i⟫ ≤ 0} := by
    intro u hu v hv a b ha hb hab
    change ⟪p, a • u + b • v - x i⟫ ≤ 0
    have he : a • u + b • v - x i = a • (u - x i) + b • (v - x i) := by
      have hh : a • x i + b • x i = x i := by rw [← add_smul, hab, one_smul]
      calc
        a • u + b • v - x i = (a • u + b • v) - (a • x i + b • x i) := by rw [hh]
        _ = a • (u - x i) + b • (v - x i) := by module
    rw [he, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hu)
      (mul_nonpos_of_nonneg_of_nonpos hb hv)
  have hs : Set.range x ⊆ {w : Space d | ⟪p, w - x i⟫ ≤ 0} := by
    rintro w ⟨j, rfl⟩
    exact h j
  intro w hw
  simpa only [zero_add] using convexHull_min hs hc hw

theorem exists_prox (x : Fin n → Space d) (c : Space d) :
    ∃ w, IsProx (hull x) (fun _ => 0) c w := by
  have hf : ContinuousOn (fun w : Space d => (1 / 2 : ℝ) * ‖w - c‖ ^ 2) (hull x) := by
    fun_prop
  obtain ⟨w, hw, hm⟩ := (hull_compact x).exists_isMinOn (hull_nonempty x) hf
  exact ⟨w, hw, fun u hu => by simpa only [zero_add] using hm hu⟩

def project (x : Fin n → Space d) (c : Space d) : Space d :=
  Classical.choose (exists_prox x c)

theorem project_isProx (x : Fin n → Space d) (c : Space d) :
    IsProx (hull x) (fun _ => 0) c (project x c) := Classical.choose_spec (exists_prox x c)

theorem project_vertex (x : Fin n → Space d) (c : Space d) (i : Fin n)
    (h : ∀ j, ⟪c - x i, x j - x i⟫ ≤ 0) : project x c = x i :=
  isProx_unique (convexOn_const 0 (hull_convex x)) (project_isProx x c)
    (isProx_of_supports (supports_of_vertices x i (c - x i) h))

def nextIndex (i : Fin n) : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩

def cpMap (x y : Fin n → Space d) (κ θ : ℝ) (w : Space d × Space d) : Space d × Space d :=
  let u := project x (w.1 - w.2)
  let v := project y (w.2 + κ • ((1 + θ) • u - θ • w.1))
  (u, v)

def NormalCertificate (x y : Fin n → Space d) (κ θ : ℝ) : Prop :=
  (∀ i j, ⟪x i - y i - x (nextIndex i), x j - x (nextIndex i)⟫ ≤ 0) ∧
  (∀ i j, ⟪y i + κ • ((1 + θ) • x (nextIndex i) - θ • x i) - y (nextIndex i),
      y j - y (nextIndex i)⟫ ≤ 0)

theorem certified_step (x y : Fin n → Space d) (κ θ : ℝ)
    (h : NormalCertificate x y κ θ) (i : Fin n) :
    cpMap x y κ θ (x i, y i) = (x (nextIndex i), y (nextIndex i)) := by
  have hx := project_vertex x (x i - y i) (nextIndex i) (h.1 i)
  have hy := project_vertex y
    (y i + κ • ((1 + θ) • x (nextIndex i) - θ • x i)) (nextIndex i) (h.2 i)
  simp only [cpMap, hx]
  exact Prod.ext rfl hy

def cycleIndex (k : ℕ) : Fin n := ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩

def orbit (x y : Fin n → Space d) (k : ℕ) : Space d × Space d :=
  (x (cycleIndex k), y (cycleIndex k))

theorem index_succ (k : ℕ) : cycleIndex (n := n) (k + 1) = nextIndex (cycleIndex k) := by
  apply Fin.ext
  simp [cycleIndex, nextIndex, Nat.add_mod]

theorem orbit_recursion (x y : Fin n → Space d) (κ θ : ℝ)
    (h : NormalCertificate x y κ θ) (k : ℕ) :
    orbit x y (k + 1) = cpMap x y κ θ (orbit x y k) := by
  unfold orbit
  rw [index_succ, certified_step x y κ θ h]

theorem iterate_eq_orbit (x y : Fin n → Space d) (κ θ : ℝ)
    (h : NormalCertificate x y κ θ) (k : ℕ) :
    (cpMap x y κ θ)^[k] (x 0, y 0) = orbit x y k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, ← orbit_recursion x y κ θ h]

theorem orbit_subseq (x y : Fin n → Space d) (i : Fin n) (k : ℕ) :
    orbit x y (n * k + i.val) = (x i, y i) := by
  have he : cycleIndex (n * k + i.val) = i := by
    apply Fin.ext
    simp [cycleIndex, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  simp only [orbit, he]

theorem orbit_periodic (x y : Fin n → Space d) (k : ℕ) :
    orbit x y (k + n) = orbit x y k := by
  simp [orbit, cycleIndex, Nat.add_mod]

theorem orbit_not_convergent (x y : Fin n → Space d) (i j : Fin n) (hne : x i ≠ x j) :
    ¬ ∃ w, Filter.Tendsto (orbit x y) Filter.atTop (nhds w) := by
  rintro ⟨w, hw⟩
  have ht (a : ℕ) : Filter.Tendsto (fun k : ℕ => n * k + a) Filter.atTop Filter.atTop := by
    apply StrictMono.tendsto_atTop
    intro b c hbc
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hbc (NeZero.pos n)) a
  have hi : Filter.Tendsto (fun _ : ℕ => (x i, y i)) Filter.atTop (nhds w) := by
    simpa only [Function.comp_def, orbit_subseq] using hw.comp (ht i.val)
  have hj : Filter.Tendsto (fun _ : ℕ => (x j, y j)) Filter.atTop (nhds w) := by
    simpa only [Function.comp_def, orbit_subseq] using hw.comp (ht j.val)
  have hei : (x i, y i) = w := tendsto_nhds_unique tendsto_const_nhds hi
  have hej : (x j, y j) = w := tendsto_nhds_unique tendsto_const_nhds hj
  exact hne (congrArg Prod.fst (hei.trans hej.symm))

theorem certified_nonconvergence (x y : Fin n → Space d) (κ θ : ℝ)
    (h : NormalCertificate x y κ θ) (i j : Fin n) (hne : x i ≠ x j) :
    ¬ ∃ w, Filter.Tendsto (fun k : ℕ => (cpMap x y κ θ)^[k] (x 0, y 0))
      Filter.atTop (nhds w) := by
  simpa only [iterate_eq_orbit x y κ θ h] using orbit_not_convergent x y i j hne

theorem zero_mem_hull (x : Fin n → Space d) (hzero : ∑ i : Fin n, x i = 0) :
    (0 : Space d) ∈ hull x := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have h := (hull_convex x).sum_mem (t := Finset.univ)
    (w := fun _ : Fin n => (1 / (n : ℝ))) (z := x)
    (by intro i hi; positivity)
    (by simp [Finset.sum_const, hn]) (by intro i hi; exact mem_hull x i)
  have he : (∑ i : Fin n, (1 / (n : ℝ)) • x i) = 0 := by
    rw [← Finset.smul_sum, hzero, smul_zero]
  simpa only [he] using h

def IsSaddle (K J : Set (Space d)) (x y : Space d) : Prop :=
  x ∈ K ∧ y ∈ J ∧ (∀ v ∈ J, ⟪x, v⟫ ≤ ⟪x, y⟫) ∧ (∀ u ∈ K, ⟪x, y⟫ ≤ ⟪u, y⟫)

theorem origin_saddle (x y : Fin n → Space d)
    (hx : ∑ i : Fin n, x i = 0) (hy : ∑ i : Fin n, y i = 0) :
    IsSaddle (hull x) (hull y) 0 0 := by
  exact ⟨zero_mem_hull x hx, zero_mem_hull y hy, by simp, by simp⟩

end FiniteCP
