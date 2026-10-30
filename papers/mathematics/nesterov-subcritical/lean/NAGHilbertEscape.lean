import NAGHilbertModel
import NAGVelocity

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology NNReal ENNReal
set_option autoImplicit false

namespace DiscreteNesterov
open NesterovThresholdModel NesterovHilbert

def excursionTarget (n : ℕ) : ℝ := 2+((n:ℝ)+1)/weight n
lemma excursionTarget_ge_two (n : ℕ) : 2≤excursionTarget n := by
  have h : 0≤((n:ℝ)+1)/weight n := div_nonneg (by positivity) (weight_pos n).le
  unfold excursionTarget
  linarith
lemma scaled_excursionTarget (n : ℕ) : (n:ℝ)+1≤weight n*excursionTarget n := by
  have h : weight n*excursionTarget n=2*weight n+((n:ℝ)+1) := by
    unfold excursionTarget
    field_simp [ne_of_gt (weight_pos n)]
  rw [h]
  linarith [weight_pos n]

lemma hilbert_normalGradient_first_nonpos (e : PowerExponent) (ε : ℝ) (x : Plane) :
    normalGradient e ε x 0≤0 := by
  change (ε^2/4)*(gradient e ε x 0)≤0
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (gradient_first_nonpos e ε x)

lemma planar_iterates_first_monotone {r h : ℝ} (hr : 0<r) (e : PowerExponent) (ε : ℝ) :
    Monotone (fun k => nagX r h (normalGradient e ε) (point 2 1) k 0) :=
  nagX_coordinate_monotone hr (normalGradient e ε) (point 2 1)
    (EuclideanSpace.proj 0) (hilbert_normalGradient_first_nonpos e ε)

/-- Diagonal assembly of permanent finite excursions. The sequence in this
statement is the literal, recursively defined, fixed-unit-step Nesterov sequence. -/
theorem discrete_escape_from_blocks {r : ℝ} (hr : 0<r) (e : PowerExponent)
    (ε h : ℕ → ℝ) (he : ∀ n, 0<ε n ∧ ε n≤1) (hh : ∀ n, 0<h n ∧ h n≤1)
    (hblocks : ∀ n, ∃ N : ℕ,
      excursionTarget n<nagX r (h n) (normalGradient e (ε n)) (point 2 1) N 0) :
    Tendsto (fun k => ‖nagX r 1 (discreteGradient e ε h) (initialData (point 2 1)) k‖)
      atTop atTop := by
  let X := nagX r 1 (discreteGradient e ε h) (initialData (point 2 1))
  have hn (n : ℕ) : ∃ N : ℕ, ∀ k≥N, (n:ℝ)+1≤‖X k‖ := by
    obtain ⟨N,hN⟩ := hblocks n
    refine ⟨N,?_⟩
    intro k hk
    have hm := planar_iterates_first_monotone (h := h n) hr e (ε n) hk
    have hbig := mul_le_mul_of_nonneg_left (hN.le.trans hm) (weight_pos n).le
    have hx : X k n 0=weight n*nagX r (h n) (normalGradient e (ε n)) (point 2 1) k 0 := by
      have hd := congrArg (fun z : Plane => z 0) (discrete_iterate_coordinate (r := r) e he hh n k)
      exact hd
    rw [← hx] at hbig
    have hcoord : X k n 0≤‖X k n‖ :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (X k n) 0)
    have hnorm : ‖X k n‖≤‖X k‖ := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) (X k) n
    exact (scaled_excursionTarget n).trans (hbig.trans (hcoord.trans hnorm))
  apply tendsto_atTop.2
  intro B
  obtain ⟨n,hnB⟩ := exists_nat_gt B
  obtain ⟨N,hN⟩ := hn n
  apply eventually_atTop.2
  refine ⟨N,fun k hk => ?_⟩
  exact (by linarith : B≤(n:ℝ)+1).trans (hN k hk)

end DiscreteNesterov
