module
public import THGStrong.Core
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Finite interpolation algebra for the strong-convexity certificate.
The generic finite-sum organization adapts the MIT-licensed
THGGradient/FactorIdentity.lean supplied with the already established convex
case. The strong-interpolation expansion and its coefficient matrix are new
to this investigation; no novelty claim is made for the generic sum lemmas.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
open Finset

namespace THGStrong

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem trajectory_closed (N : ℕ) (h : ℝ) (x g : ℕ → E)
    (hx : ∀ i < N, x (i + 1) = x i - h • g i) :
    ∀ i ≤ N, x i = x 0 - h • ∑ k ∈ range i, g k := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    rw [hx i (by omega), ih (by omega), sum_range_succ, smul_add]
    abel

theorem symmetric_bilinear_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (g : ι → E)
    (hoff : ∀ i j, i ≠ j → M i j + M j i = 0) :
    ∑ i, ∑ j, M i j * ⟪g i, g j⟫_ℝ = ∑ i, M i i * sq (g i) := by
  have htranspose : (∑ i, ∑ j, M j i * ⟪g i, g j⟫_ℝ) =
      ∑ i, ∑ j, M i j * ⟪g i, g j⟫_ℝ := by
    rw [sum_comm]
    congr 1
    ext i
    congr 1
    ext j
    rw [real_inner_comm]
  have hdouble : 2 * (∑ i, ∑ j, M i j * ⟪g i, g j⟫_ℝ) =
      ∑ i, ∑ j, (M i j + M j i) * ⟪g i, g j⟫_ℝ := by
    simp only [add_mul, sum_add_distrib]
    rw [htranspose]
    ring
  have hdiag : (∑ i, ∑ j, (M i j + M j i) * ⟪g i, g j⟫_ℝ) =
      2 * ∑ i, M i i * sq (g i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [sum_eq_single i]
    · dsimp [sq]; ring
    · intro j _ hji
      rw [hoff i j (Ne.symm hji), zero_mul]
    · simp
  linarith

theorem sum_weighted_difference {ι : Type*} [Fintype ι]
    (w : ι → ι → ℝ) (v : ι → ℝ) :
    (∑ i, ∑ j, w i j * (v i - v j)) =
      ∑ i, (∑ j, (w i j - w j i)) * v i := by
  simp only [mul_sub, sum_sub_distrib, sub_mul, sum_mul]
  rw [sum_comm (f := fun i j => w i j * v j)]

theorem sum_weighted_pair {ι : Type*} [Fintype ι]
    (w : ι → ι → ℝ) (v : ι → ℝ) :
    (∑ i, ∑ j, w i j * (v i + v j)) =
      ∑ i, (∑ j, (w i j + w j i)) * v i := by
  simp only [mul_add, sum_add_distrib, add_mul, sum_mul]
  rw [sum_comm (f := fun i j => w i j * v j)]

theorem sum_four_swap {ι : Type*} [Fintype ι] (F : ι → ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) =
      ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := by
  calc
    _ = ∑ i, ∑ k, ∑ l, ∑ j, F i j k l := by
      apply sum_congr rfl; intro i _
      rw [sum_comm]
      apply sum_congr rfl; intro k _
      rw [sum_comm]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl; intro k _
      rw [sum_comm]

def historyCoefficient {ι : Type*} [Fintype ι]
    (w T : ι → ι → ℝ) (μ h : ℝ) (i j : ι) : ℝ :=
  w i j + h * ∑ k, (w k i + μ * w i k) * (T k j - T i j) -
    (μ * h^2 / 2) * ∑ k, ∑ l,
      w k l * (T k i - T l i) * (T k j - T l j)

theorem weighted_interpolation_expansion {ι : Type*} [Fintype ι]
    (w T : ι → ι → ℝ) (f : ι → ℝ) (x g : ι → E) (X : E) (μ h : ℝ)
    (hx : ∀ i, x i = X - h • ∑ j, (T i j) • g j) :
    (∑ i, ∑ j, w i j * Q μ (x i) (x j) (g i) (g j) (f i) (f j)) =
      (∑ i, 2 * (1-μ) * (∑ j, (w i j - w j i)) * f i)
      + 2 * (∑ i, ∑ j, historyCoefficient w T μ h i j * ⟪g i, g j⟫_ℝ)
      - ∑ i, (∑ j, (w i j + w j i)) * sq (g i) := by
  have hvec (i j : ι) : x i - x j = -h • ∑ k, (T i k - T j k) • g k := by
    rw [hx i, hx j]
    simp only [sub_smul, sum_sub_distrib, neg_smul, smul_sub]
    abel
  have hipos (i j : ι) : ⟪g j, x i - x j⟫_ℝ =
      -h * ∑ k, (T i k - T j k) * ⟪g j, g k⟫_ℝ := by
    rw [hvec, real_inner_smul_right, inner_sum]
    simp_rw [real_inner_smul_right]
  have hpos (v : ι → ι → ℝ) :
      (∑ i, ∑ j, v i j * ⟪g j, x i - x j⟫_ℝ) =
      -h * ∑ i, ∑ j, (∑ k, v k i * (T k j - T i j)) * ⟪g i, g j⟫_ℝ := by
    simp_rw [hipos, mul_sum, sum_mul]
    calc
      _ = ∑ i, ∑ j, ∑ k, -h * (v i j * (T i k - T j k) * ⟪g j, g k⟫_ℝ) := by
        apply sum_congr rfl; intro i _
        apply sum_congr rfl; intro j _
        apply sum_congr rfl; intro k _
        ring
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl; intro i _
        rw [sum_comm]
        simp only [mul_sum]
  have hswap : (∑ i, ∑ j, w i j * ⟪g i, x i - x j⟫_ℝ) =
      -(∑ i, ∑ j, w j i * ⟪g j, x i - x j⟫_ℝ) := by
    rw [sum_comm]
    simp only [← sum_neg_distrib]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    simp only [inner_sub_right]
    ring
  have hlinear : (∑ i, ∑ j, w i j * ⟪g j - μ • g i, x i - x j⟫_ℝ) =
      -h * ∑ i, ∑ j, (∑ k, (w k i + μ * w i k) * (T k j - T i j)) *
        ⟪g i, g j⟫_ℝ := by
    have he : (∑ i, ∑ j, w i j * ⟪g j - μ • g i, x i - x j⟫_ℝ) =
        ∑ i, ∑ j, (w i j + μ * w j i) * ⟪g j, x i - x j⟫_ℝ := by
      calc
        _ = (∑ i, ∑ j, w i j * ⟪g j, x i-x j⟫_ℝ) -
            μ * (∑ i, ∑ j, w i j * ⟪g i,x i-x j⟫_ℝ) := by
          simp only [inner_sub_left, real_inner_smul_left, mul_sum,
            ← sum_sub_distrib]
          apply sum_congr rfl; intro i _
          apply sum_congr rfl; intro j _
          ring
        _ = _ := by
          rw [hswap]
          simp only [add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
          ring
    rw [he, hpos]
  have hsquare (i j : ι) : sq (x i - x j) =
      h^2 * ∑ k, ∑ l, (T i k - T j k) * (T i l - T j l) * ⟪g k, g l⟫_ℝ := by
    have hi : ⟪∑ k, (T i k-T j k) • g k, ∑ l, (T i l-T j l) • g l⟫_ℝ =
        ∑ k, ∑ l, (T i k-T j k)*(T i l-T j l)*⟪g k,g l⟫_ℝ := by
      rw [sum_inner]
      apply sum_congr rfl; intro k _
      rw [inner_sum]
      apply sum_congr rfl; intro l _
      simp only [real_inner_smul_left, real_inner_smul_right]
      ring
    rw [hvec]
    simp only [sq, real_inner_smul_left, real_inner_smul_right]
    rw [hi]
    ring
  have hquadratic : (∑ i, ∑ j, w i j * sq (x i - x j)) =
      h^2 * ∑ k, ∑ l, (∑ i, ∑ j,
        w i j * (T i k - T j k) * (T i l - T j l)) * ⟪g k, g l⟫_ℝ := by
    simp_rw [hsquare, mul_sum, sum_mul]
    calc
      _ = h^2 * ∑ i, ∑ j, ∑ k, ∑ l,
          w i j * (T i k - T j k) * (T i l - T j l) * ⟪g k, g l⟫_ℝ := by
        simp only [mul_sum]
        apply sum_congr rfl; intro i _
        apply sum_congr rfl; intro j _
        apply sum_congr rfl; intro k _
        apply sum_congr rfl; intro l _
        ring
      _ = _ := by rw [sum_four_swap]; simp only [mul_sum]
  have hraw : (∑ i, ∑ j, w i j * Q μ (x i) (x j) (g i) (g j) (f i) (f j)) =
      2*(1-μ) * (∑ i, ∑ j, w i j * (f i - f j)) -
      2 * (∑ i, ∑ j, w i j * ⟪g j - μ • g i, x i - x j⟫_ℝ) -
      (∑ i, ∑ j, w i j * (sq (g i) + sq (g j))) +
      2 * (∑ i, ∑ j, w i j * ⟪g i, g j⟫_ℝ) -
      μ * (∑ i, ∑ j, w i j * sq (x i - x j)) := by
    simp only [Q, sq, inner_sub_left, inner_sub_right, mul_sum,
      ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    rw [real_inner_comm (g j) (g i)]
    ring
  rw [hraw, hlinear, hquadratic, sum_weighted_difference, sum_weighted_pair]
  simp only [historyCoefficient, sub_mul, add_mul, sum_sub_distrib, sum_add_distrib,
    ← mul_sum, mul_assoc]
  ring

theorem weighted_interpolation_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w T : ι → ι → ℝ) (c f : ι → ℝ) (x g : ι → E) (X : E) (μ h : ℝ)
    (hx : ∀ i, x i = X - h • ∑ j, (T i j) • g j)
    (hoff : ∀ i j, i ≠ j → historyCoefficient w T μ h i j +
      historyCoefficient w T μ h j i = 0)
    (hdiag : ∀ i, 2 * historyCoefficient w T μ h i i -
      (∑ j, (w i j + w j i)) = c i) :
    (∑ i, ∑ j, w i j * Q μ (x i) (x j) (g i) (g j) (f i) (f j)) =
      (∑ i, 2 * (1-μ) * (∑ j, (w i j - w j i)) * f i) +
      ∑ i, c i * sq (g i) := by
  rw [weighted_interpolation_expansion w T f x g X μ h hx,
    symmetric_bilinear_sum (historyCoefficient w T μ h) g hoff]
  rw [add_sub_assoc]
  congr 1
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [← hdiag i]
  ring

theorem weighted_distance_telescope (N : ℕ) (μ h : ℝ) (x g : ℕ → E)
    (α : ℕ → ℝ) (hα0 : α 0 = 1)
    (hα : ∀ i < N, α i = (1-μ*h) * α (i+1))
    (hx : ∀ i < N, x (i+1) = x i - h • g i) :
    (∑ i ∈ range N, (h * α (i+1)) *
      (2 * ⟪g i,x i⟫_ℝ - h * sq (g i) - μ * sq (x i))) =
      sq (x 0) - α N * sq (x N) := by
  induction N with
  | zero => simp [hα0]
  | succ N ih =>
    rw [sum_range_succ, ih (fun i hi => hα i (by omega))
      (fun i hi => hx i (by omega)), hx N (by omega), hα N (by omega)]
    simp only [sq, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (x N) (g N)]
    ring

theorem balanced_history_completion (N : ℕ) (μ h S W : ℝ)
    (x g : ℕ → E) (f α : ℕ → ℝ)
    (hα0 : α 0 = 1)
    (hα : ∀ i < N, α i = (1-μ*h) * α (i+1))
    (hx : ∀ i < N, x (i+1) = x i - h • g i)
    (hW : W = 2*(1-μ)*((∑ i ∈ range N, (h*α (i+1))*f i)-S*f N) -
      (h-1)*(∑ i ∈ range N, (h*α (i+1))*sq (g i)) - S*(S+1)*sq (g N)) :
    sq (x 0) = α N * sq (x N) + 2*(1-μ)*S*f N + S*(S+1)*sq (g N) +
      W + ∑ i ∈ range N, (h*α (i+1)) * Q μ 0 (x i) 0 (g i) 0 (f i) := by
  have ht := weighted_distance_telescope N μ h x g α hα0 hα hx
  have hs : (∑ i ∈ range N, (h*α (i+1)) * Q μ 0 (x i) 0 (g i) 0 (f i)) =
      -2*(1-μ)*(∑ i ∈ range N, (h*α (i+1))*f i) +
      (h-1)*(∑ i ∈ range N, (h*α (i+1))*sq (g i)) +
      ∑ i ∈ range N, (h*α (i+1)) *
        (2*⟪g i,x i⟫_ℝ-h*sq (g i)-μ*sq (x i)) := by
    simp only [Q, sub_zero, zero_sub, smul_zero, sq,
      inner_neg_left, inner_neg_right, inner_zero_left, inner_zero_right,
      mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hs, ht, hW]
  ring

theorem sum_fin_prefix (N k : ℕ) (hk : k ≤ N+1) (g : ℕ → E) :
    (∑ j : Fin (N+1), (if (j : ℕ) < k then (1 : ℝ) else 0) • g j) =
      ∑ j ∈ range k, g j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (if j < k then (1 : ℝ) else 0) • g j)]
  simp only [ite_smul, one_smul, zero_smul]
  rw [← sum_filter]
  congr 1
  ext j
  simp only [mem_filter, mem_range]
  omega

/-- The finite coefficient conditions imply the exact balanced identity.
The public sharp-rate theorem must instantiate these conditions using the
explicit scalar construction; they are not assumptions on the objective. -/
theorem balanced_weighted_identity (N : ℕ) (μ h S : ℝ)
    (w : Fin (N+1) → Fin (N+1) → ℝ)
    (x g : ℕ → E) (f α : ℕ → ℝ)
    (hα0 : α 0 = 1)
    (hα : ∀ i < N, α i = (1-μ*h) * α (i+1))
    (hx : ∀ i < N, x (i+1) = x i - h • g i)
    (hoff : ∀ i j : Fin (N+1), i ≠ j →
      historyCoefficient w (fun i j => if j < i then 1 else 0) μ h i j +
      historyCoefficient w (fun i j => if j < i then 1 else 0) μ h j i = 0)
    (hdiv : ∀ i : Fin (N+1), (∑ j, (w i j-w j i)) =
      if (i : ℕ) < N then h*α (i+1) else -S)
    (hdiag : ∀ i : Fin (N+1),
      2*historyCoefficient w (fun i j => if j < i then 1 else 0) μ h i i -
      (∑ j, (w i j+w j i)) =
      if (i : ℕ) < N then -(h-1)*(h*α (i+1)) else -S*(S+1)) :
    sq (x 0) = α N * sq (x N) + 2*(1-μ)*S*f N + S*(S+1)*sq (g N) +
      (∑ i, ∑ j, w i j * Q μ (x i) (x j) (g i) (g j) (f i) (f j)) +
      ∑ i ∈ range N, (h*α (i+1)) * Q μ 0 (x i) 0 (g i) 0 (f i) := by
  let T : Fin (N+1) → Fin (N+1) → ℝ := fun i j => if j < i then 1 else 0
  have hxf (i : Fin (N+1)) : x i = x 0-h • ∑ j : Fin (N+1), T i j • g j := by
    dsimp [T]
    change x i = x 0-h • ∑ j : Fin (N+1),
      (if (j : ℕ) < (i : ℕ) then (1 : ℝ) else 0) • g j
    rw [sum_fin_prefix N i (by omega)]
    exact trajectory_closed N h x g hx i (by omega)
  have hw := weighted_interpolation_diagonal w T
    (fun i : Fin (N+1) => if (i : ℕ) < N then -(h-1)*(h*α (i+1)) else -S*(S+1))
    (fun i : Fin (N+1) => f i) (fun i : Fin (N+1) => x i)
    (fun i : Fin (N+1) => g i) (x 0) μ h hxf hoff hdiag
  have hsumf : (∑ i : Fin (N+1), 2*(1-μ)*(∑ j, (w i j-w j i))*f i) =
      2*(1-μ)*((∑ i ∈ range N, (h*α (i+1))*f i)-S*f N) := by
    simp_rw [hdiv]
    rw [Fin.sum_univ_eq_sum_range (fun i => 2*(1-μ)*
      (if i < N then h*α (i+1) else -S)*f i), sum_range_succ]
    simp only [lt_self_iff_false, ite_false]
    have hp : (∑ i ∈ range N, 2*(1-μ)*(if i < N then h*α (i+1) else -S)*f i) =
        ∑ i ∈ range N, 2*(1-μ)*((h*α (i+1))*f i) := by
      apply sum_congr rfl; intro i hi
      rw [if_pos (mem_range.mp hi)]
      ring
    rw [hp, ← mul_sum]
    ring
  have hsumg : (∑ i : Fin (N+1),
      (if (i : ℕ) < N then -(h-1)*(h*α (i+1)) else -S*(S+1))*sq (g i)) =
      -(h-1)*(∑ i ∈ range N, (h*α (i+1))*sq (g i)) - S*(S+1)*sq (g N) := by
    rw [Fin.sum_univ_eq_sum_range (fun i =>
      (if i < N then -(h-1)*(h*α (i+1)) else -S*(S+1))*sq (g i)), sum_range_succ]
    simp only [lt_self_iff_false, ite_false]
    have hp : (∑ i ∈ range N,
        (if i < N then -(h-1)*(h*α (i+1)) else -S*(S+1))*sq (g i)) =
        ∑ i ∈ range N, -(h-1)*((h*α (i+1))*sq (g i)) := by
      apply sum_congr rfl; intro i hi
      rw [if_pos (mem_range.mp hi)]
      ring
    rw [hp, ← mul_sum]
    ring
  rw [hsumf, hsumg] at hw
  apply balanced_history_completion N μ h S _ x g f α hα0 hα hx
  rw [hw]
  ring

#print axioms weighted_interpolation_expansion
#print axioms weighted_interpolation_diagonal
#print axioms weighted_distance_telescope
#print axioms balanced_history_completion
#print axioms balanced_weighted_identity

end THGStrong
