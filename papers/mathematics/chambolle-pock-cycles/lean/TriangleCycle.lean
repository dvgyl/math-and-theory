import Proximal
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# A genuine period-three orbit of the projected Chambolle--Pock algorithm

The convex domains are compact triangles in ordinary Euclidean space.  Every update
below is the unique global minimizer of its squared-distance objective.  The model
uses no stipulated proximal selector and no assumed iteration inequalities.
-/

set_option autoImplicit false

noncomputable section

namespace CPSharpness

abbrev Plane := EuclideanSpace ℝ (Fin 3)

local notation "⟪" x ", " y "⟫" => @inner ℝ Plane _ x y

def next (i : Fin 3) : Fin 3 := ![1, 2, 0] i
def prev (i : Fin 3) : Fin 3 := ![2, 0, 1] i

def X (i : Fin 3) : Plane := ![!₂[2, -1, -1], !₂[-1, 2, -1], !₂[-1, -1, 2]] i

def Y (s b : ℝ) (i : Fin 3) : Plane :=
  s • X i + b • (X (prev i) - X (next i))

def C : Set Plane := convexHull ℝ (Set.range X)
def D (s b : ℝ) : Set Plane := convexHull ℝ (Set.range (Y s b))

theorem X_mem (i : Fin 3) : X i ∈ C :=
  subset_convexHull ℝ _ (Set.mem_range_self i)

theorem Y_mem (s b : ℝ) (i : Fin 3) : Y s b i ∈ D s b :=
  subset_convexHull ℝ _ (Set.mem_range_self i)

theorem C_convex : Convex ℝ C := convex_convexHull ℝ _
theorem D_convex (s b : ℝ) : Convex ℝ (D s b) := convex_convexHull ℝ _

theorem C_compact : IsCompact C := (Set.finite_range X).isCompact_convexHull
theorem D_compact (s b : ℝ) : IsCompact (D s b) :=
  (Set.finite_range (Y s b)).isCompact_convexHull

theorem C_nonempty : C.Nonempty := ⟨X 0, X_mem 0⟩
theorem D_nonempty (s b : ℝ) : (D s b).Nonempty := ⟨Y s b 0, Y_mem s b 0⟩

theorem zero_mem_C : (0 : Plane) ∈ C := by
  have h := C_convex.sum_mem (t := Finset.univ) (w := fun _ : Fin 3 => (1 / 3 : ℝ))
    (z := X) (by intro i hi; norm_num) (by norm_num) (by intro i hi; exact X_mem i)
  have he : (∑ i : Fin 3, (1 / 3 : ℝ) • X i) = 0 := by
    ext j
    fin_cases j <;> norm_num [Fin.sum_univ_succ, X]
  simpa only [he] using h

theorem zero_mem_D (s b : ℝ) : (0 : Plane) ∈ D s b := by
  have h := (D_convex s b).sum_mem (t := Finset.univ)
    (w := fun _ : Fin 3 => (1 / 3 : ℝ)) (z := Y s b)
    (by intro i hi; norm_num) (by norm_num) (by intro i hi; exact Y_mem s b i)
  have he : (∑ i : Fin 3, (1 / 3 : ℝ) • Y s b i) = 0 := by
    ext j
    fin_cases j <;> norm_num [Fin.sum_univ_succ, Y, X, next, prev] <;> ring
  simpa only [he] using h

/-- A saddle point for the actual constrained bilinear problem `min_C max_D ⟪x,y⟫`. -/
def IsBilinearSaddle (K J : Set Plane) (x y : Plane) : Prop :=
  x ∈ K ∧ y ∈ J ∧ (∀ v ∈ J, ⟪x, v⟫ ≤ ⟪x, y⟫) ∧ (∀ u ∈ K, ⟪x, y⟫ ≤ ⟪u, y⟫)

theorem zero_saddle (s b : ℝ) : IsBilinearSaddle C (D s b) 0 0 := by
  exact ⟨zero_mem_C, zero_mem_D s b, by simp, by simp⟩

theorem supports_hull_of_vertices (z : Fin 3 → Plane) (i : Fin 3) (p : Plane)
    (h : ∀ j, ⟪p, z j - z i⟫ ≤ 0) :
    Supports (convexHull ℝ (Set.range z)) (fun _ => 0) (z i) p := by
  refine ⟨subset_convexHull ℝ _ (Set.mem_range_self i), ?_⟩
  have hc : Convex ℝ {w : Plane | ⟪p, w - z i⟫ ≤ 0} := by
    intro u hu v hv a b ha hb hab
    change ⟪p, a • u + b • v - z i⟫ ≤ 0
    have he : a • u + b • v - z i = a • (u - z i) + b • (v - z i) := by
      have hh : a • z i + b • z i = z i := by rw [← add_smul, hab, one_smul]
      calc
        a • u + b • v - z i = (a • u + b • v) - (a • z i + b • z i) := by rw [hh]
        _ = a • (u - z i) + b • (v - z i) := by module
    rw [he, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hu)
      (mul_nonpos_of_nonneg_of_nonpos hb hv)
  have hs : Set.range z ⊆ {w : Plane | ⟪p, w - z i⟫ ≤ 0} := by
    rintro w ⟨j, rfl⟩
    exact h j
  intro w hw
  simpa only [zero_add] using convexHull_min hs hc hw

def PrimalCenter (s b : ℝ) (i : Fin 3) : Plane := X (prev i) - Y s b (prev i)

def DualCenter (s b κ θ : ℝ) (i : Fin 3) : Plane :=
  Y s b (prev i) + κ • ((1 + θ) • X i - θ • X (prev i))

theorem primal_vertex_normal (s b : ℝ) (hb : 1 / 2 ≤ b) (hs : 2 ≤ s + b)
    (i j : Fin 3) : ⟪PrimalCenter s b i - X i, X j - X i⟫ ≤ 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [PrimalCenter, X, Y, prev, next, PiLp.inner_apply, Fin.sum_univ_succ,
      real_inner_eq_re_inner, RCLike.inner_apply, Matrix.cons_val_two] <;> nlinarith

theorem dual_vertex_normal (s b κ θ : ℝ)
    (h₁ : s ^ 2 + 3 * b ^ 2 ≤ κ * ((1 + θ) * s - (1 + 3 * θ) * b))
    (h₂ : 2 * (s ^ 2 + 3 * b ^ 2) ≤ κ * ((1 + 2 * θ) * s + b))
    (i j : Fin 3) :
    ⟪DualCenter s b κ θ i - Y s b i, Y s b j - Y s b i⟫ ≤ 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [DualCenter, X, Y, prev, next, PiLp.inner_apply, Fin.sum_univ_succ,
      real_inner_eq_re_inner, RCLike.inner_apply, Matrix.cons_val_two] <;> nlinarith

theorem primal_isProx (s b : ℝ) (hb : 1 / 2 ≤ b) (hs : 2 ≤ s + b)
    (i : Fin 3) : IsProx C (fun _ => 0) (PrimalCenter s b i) (X i) :=
  isProx_of_supports (supports_hull_of_vertices X i _ (primal_vertex_normal s b hb hs i))

theorem dual_isProx (s b κ θ : ℝ)
    (h₁ : s ^ 2 + 3 * b ^ 2 ≤ κ * ((1 + θ) * s - (1 + 3 * θ) * b))
    (h₂ : 2 * (s ^ 2 + 3 * b ^ 2) ≤ κ * ((1 + 2 * θ) * s + b))
    (i : Fin 3) : IsProx (D s b) (fun _ => 0) (DualCenter s b κ θ i) (Y s b i) :=
  isProx_of_supports (supports_hull_of_vertices (Y s b) i _
    (dual_vertex_normal s b κ θ h₁ h₂ i))

theorem exists_isProx_zero (K : Set Plane) (hc : IsCompact K) (hn : K.Nonempty)
    (c : Plane) : ∃ x, IsProx K (fun _ => 0) c x := by
  have hf : ContinuousOn (fun x : Plane => (1 / 2 : ℝ) * ‖x - c‖ ^ 2) K := by
    fun_prop
  obtain ⟨x, hx, hm⟩ := hc.exists_isMinOn hn hf
  refine ⟨x, hx, ?_⟩
  intro y hy
  simpa only [zero_add] using hm hy

/-- The actual global squared-distance minimizer on a compact nonempty domain. -/
def projection (K : Set Plane) (hc : IsCompact K) (hn : K.Nonempty) (c : Plane) : Plane :=
  Classical.choose (exists_isProx_zero K hc hn c)

theorem projection_isProx (K : Set Plane) (hc : IsCompact K) (hn : K.Nonempty)
    (c : Plane) : IsProx K (fun _ => 0) c (projection K hc hn c) :=
  Classical.choose_spec (exists_isProx_zero K hc hn c)

theorem projection_unique (K : Set Plane) (hc : IsCompact K) (hn : K.Nonempty)
    (hcv : Convex ℝ K) (c x : Plane) (hx : IsProx K (fun _ => 0) c x) :
    projection K hc hn c = x :=
  isProx_unique (convexOn_const 0 hcv) (projection_isProx K hc hn c) hx

def projectC : Plane → Plane := projection C C_compact C_nonempty
def projectD (s b : ℝ) : Plane → Plane := projection (D s b) (D_compact s b) (D_nonempty s b)

theorem projectC_cycle (s b : ℝ) (hb : 1 / 2 ≤ b) (hs : 2 ≤ s + b)
    (i : Fin 3) : projectC (PrimalCenter s b i) = X i :=
  projection_unique C C_compact C_nonempty C_convex _ _ (primal_isProx s b hb hs i)

theorem projectD_cycle (s b κ θ : ℝ)
    (h₁ : s ^ 2 + 3 * b ^ 2 ≤ κ * ((1 + θ) * s - (1 + 3 * θ) * b))
    (h₂ : 2 * (s ^ 2 + 3 * b ^ 2) ≤ κ * ((1 + 2 * θ) * s + b))
    (i : Fin 3) : projectD s b (DualCenter s b κ θ i) = Y s b i :=
  projection_unique (D s b) (D_compact s b) (D_nonempty s b) (D_convex s b) _ _
    (dual_isProx s b κ θ h₁ h₂ i)

/-- The projected Chambolle--Pock map, with primal step one and dual step `κ`. -/
def cpMap (s b κ θ : ℝ) (w : Plane × Plane) : Plane × Plane :=
  let xnew := projectC (w.1 - w.2)
  let ynew := projectD s b (w.2 + κ • ((1 + θ) • xnew - θ • w.1))
  (xnew, ynew)

theorem cpMap_cycle (s b κ θ : ℝ) (hb : 1 / 2 ≤ b) (hs : 2 ≤ s + b)
    (h₁ : s ^ 2 + 3 * b ^ 2 ≤ κ * ((1 + θ) * s - (1 + 3 * θ) * b))
    (h₂ : 2 * (s ^ 2 + 3 * b ^ 2) ≤ κ * ((1 + 2 * θ) * s + b))
    (i : Fin 3) : cpMap s b κ θ (X (prev i), Y s b (prev i)) = (X i, Y s b i) := by
  have hx := projectC_cycle s b hb hs i
  have hy := projectD_cycle s b κ θ h₁ h₂ i
  change projectC (X (prev i) - Y s b (prev i)) = X i at hx
  simp only [cpMap, hx]
  exact Prod.ext rfl hy

theorem cpMap_cycle_next (s b κ θ : ℝ) (hb : 1 / 2 ≤ b) (hs : 2 ≤ s + b)
    (h₁ : s ^ 2 + 3 * b ^ 2 ≤ κ * ((1 + θ) * s - (1 + 3 * θ) * b))
    (h₂ : 2 * (s ^ 2 + 3 * b ^ 2) ≤ κ * ((1 + 2 * θ) * s + b))
    (i : Fin 3) : cpMap s b κ θ (X i, Y s b i) = (X (next i), Y s b (next i)) := by
  have h := cpMap_cycle s b κ θ hb hs h₁ h₂ (next i)
  have hp : prev (next i) = i := by fin_cases i <;> rfl
  simpa only [hp] using h

def cycleIndex (n : ℕ) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by decide)⟩

def cycle (s b : ℝ) (n : ℕ) : Plane × Plane := (X (cycleIndex n), Y s b (cycleIndex n))

theorem cycleIndex_succ (n : ℕ) : cycleIndex (n + 1) = next (cycleIndex n) := by
  have hn : n % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases h : n % 3 <;> apply Fin.ext <;>
    norm_num [cycleIndex, next, Nat.add_mod, h]

theorem cycle_recursion (s b κ θ : ℝ) (hb : 1 / 2 ≤ b) (hs : 2 ≤ s + b)
    (h₁ : s ^ 2 + 3 * b ^ 2 ≤ κ * ((1 + θ) * s - (1 + 3 * θ) * b))
    (h₂ : 2 * (s ^ 2 + 3 * b ^ 2) ≤ κ * ((1 + 2 * θ) * s + b))
    (n : ℕ) : cycle s b (n + 1) = cpMap s b κ θ (cycle s b n) := by
  unfold cycle
  rw [cycleIndex_succ, cpMap_cycle_next s b κ θ hb hs h₁ h₂]

theorem cycle_periodic (s b : ℝ) (n : ℕ) : cycle s b (n + 3) = cycle s b n := by
  simp [cycle, cycleIndex, Nat.add_mod]

theorem cycle_subseq_zero (s b : ℝ) (n : ℕ) : cycle s b (3 * n) = (X 0, Y s b 0) := by
  simp [cycle, cycleIndex]

theorem cycle_subseq_one (s b : ℝ) (n : ℕ) : cycle s b (3 * n + 1) = (X 1, Y s b 1) := by
  simp [cycle, cycleIndex, Nat.add_mod]

theorem X_zero_ne_one : X 0 ≠ X 1 := by
  intro h
  have he := congrArg (fun z : Plane => z 0) h
  norm_num [X] at he

theorem cycle_not_convergent (s b : ℝ) :
    ¬ ∃ w : Plane × Plane, Filter.Tendsto (cycle s b) Filter.atTop (nhds w) := by
  rintro ⟨w, hw⟩
  have ht₀ : Filter.Tendsto (fun n : ℕ => 3 * n) Filter.atTop Filter.atTop := by
    apply StrictMono.tendsto_atTop
    intro a b hab
    change 3 * a < 3 * b
    omega
  have ht₁ : Filter.Tendsto (fun n : ℕ => 3 * n + 1) Filter.atTop Filter.atTop := by
    apply StrictMono.tendsto_atTop
    intro a b hab
    change 3 * a + 1 < 3 * b + 1
    omega
  have h₀ : Filter.Tendsto (fun _ : ℕ => (X 0, Y s b 0)) Filter.atTop (nhds w) := by
    simpa only [Function.comp_def, cycle_subseq_zero] using hw.comp ht₀
  have h₁ : Filter.Tendsto (fun _ : ℕ => (X 1, Y s b 1)) Filter.atTop (nhds w) := by
    simpa only [Function.comp_def, cycle_subseq_one] using hw.comp ht₁
  have he₀ : (X 0, Y s b 0) = w := tendsto_nhds_unique tendsto_const_nhds h₀
  have he₁ : (X 1, Y s b 1) = w := tendsto_nhds_unique tendsto_const_nhds h₁
  exact X_zero_ne_one (congrArg Prod.fst (he₀.trans he₁.symm))

theorem iterate_eq_cycle (s b κ θ : ℝ) (hb : 1 / 2 ≤ b) (hs : 2 ≤ s + b)
    (h₁ : s ^ 2 + 3 * b ^ 2 ≤ κ * ((1 + θ) * s - (1 + 3 * θ) * b))
    (h₂ : 2 * (s ^ 2 + 3 * b ^ 2) ≤ κ * ((1 + 2 * θ) * s + b))
    (n : ℕ) : (cpMap s b κ θ)^[n] (X 0, Y s b 0) = cycle s b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, ← cycle_recursion s b κ θ hb hs h₁ h₂]

/-- Nonconvergence of the actual iterated projection algorithm, despite its saddle point. -/
theorem cp_iterates_not_convergent (s b κ θ : ℝ) (hb : 1 / 2 ≤ b) (hs : 2 ≤ s + b)
    (h₁ : s ^ 2 + 3 * b ^ 2 ≤ κ * ((1 + θ) * s - (1 + 3 * θ) * b))
    (h₂ : 2 * (s ^ 2 + 3 * b ^ 2) ≤ κ * ((1 + 2 * θ) * s + b)) :
    ¬ ∃ w : Plane × Plane,
      Filter.Tendsto (fun n : ℕ => (cpMap s b κ θ)^[n] (X 0, Y s b 0))
        Filter.atTop (nhds w) := by
  simpa only [iterate_eq_cycle s b κ θ hb hs h₁ h₂] using cycle_not_convergent s b

theorem sharp_parameters (κ θ : ℝ) (hκ : 0 < κ) (hθ : 0 ≤ θ)
    (hΔ : 0 ≤ κ ^ 2 * (1 + θ) ^ 2 - 2 * κ * (1 + 3 * θ) - 3) :
    2 ≤ κ * (1 + θ) / 2 + 1 / 2 ∧
    (κ * (1 + θ) / 2) ^ 2 + 3 * (1 / 2 : ℝ) ^ 2 ≤
      κ * ((1 + θ) * (κ * (1 + θ) / 2) - (1 + 3 * θ) * (1 / 2)) ∧
    2 * ((κ * (1 + θ) / 2) ^ 2 + 3 * (1 / 2 : ℝ) ^ 2) ≤
      κ * ((1 + 2 * θ) * (κ * (1 + θ) / 2) + 1 / 2) := by
  have hqpos : 0 < κ * (1 + θ) := mul_pos hκ (by linarith)
  have hq : 3 ≤ κ * (1 + θ) := by
    by_contra hh
    have hu : κ * (1 + θ) < 3 := lt_of_not_ge hh
    have hp := mul_pos (show 0 < 3 - κ * (1 + θ) by linarith)
      (show 0 < κ * (1 + θ) + 1 by linarith)
    nlinarith [mul_nonneg hκ.le hθ]
  refine ⟨by linarith, ?_, ?_⟩
  · nlinarith [hΔ]
  · have hp := mul_nonneg (mul_nonneg hκ.le hθ)
      (show 0 ≤ κ * (1 + θ) - 1 by linarith)
    nlinarith

/-- Attainment of every point in the exact period-three obstruction region. -/
theorem sharp_cycle_nonconvergence (κ θ : ℝ) (hκ : 0 < κ) (hθ : 0 ≤ θ)
    (hΔ : 0 ≤ κ ^ 2 * (1 + θ) ^ 2 - 2 * κ * (1 + 3 * θ) - 3) :
    ¬ ∃ w : Plane × Plane,
      Filter.Tendsto
        (fun n : ℕ => (cpMap (κ * (1 + θ) / 2) (1 / 2) κ θ)^[n]
          (X 0, Y (κ * (1 + θ) / 2) (1 / 2) 0)) Filter.atTop (nhds w) := by
  obtain ⟨hs, h₁, h₂⟩ := sharp_parameters κ θ hκ hθ hΔ
  exact cp_iterates_not_convergent _ _ _ _ (by norm_num) hs h₁ h₂

/-- In particular, the fixed triangles `s=3/2,b=1/2` cycle at dual step three. -/
theorem step_three_nonconvergence (θ : ℝ) (hθ : 0 ≤ θ) :
    ¬ ∃ w : Plane × Plane,
      Filter.Tendsto
        (fun n : ℕ => (cpMap (3 / 2) (1 / 2) 3 θ)^[n]
          (X 0, Y (3 / 2) (1 / 2) 0)) Filter.atTop (nhds w) := by
  apply cp_iterates_not_convergent <;> norm_num <;> nlinarith

end CPSharpness
