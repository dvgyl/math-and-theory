import TransferRoots
import FlowerPolynomial

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Transfer
open Lambert Reciprocal

def flowerBracket (n : ℕ) (z : ℂ) : ℂ :=
  z * (z ^ 2 + 3 * z + 3) ^ n + (z ^ 2 + 3 * z + 1) ^ n - 1

def numerator (n : ℕ) (w : ℂ) : ℂ := P w ^ n + w * Q w ^ n - w ^ (2 * n + 1)

theorem reciprocal_monomials (n : ℕ) (w a b : ℂ) (hw : w ≠ 0) :
    w ^ (2 * n + 1) * (w⁻¹ * a ^ n + b ^ n - 1) =
      (w ^ 2 * a) ^ n + w * (w ^ 2 * b) ^ n - w ^ (2 * n + 1) := by
  simp only [mul_pow, pow_add, pow_one, pow_mul]
  field_simp [hw]
  ring

theorem reciprocal_identity (n : ℕ) {w : ℂ} (hw : w ≠ 0) :
    w ^ (2 * n + 1) * flowerBracket n w⁻¹ = numerator n w := by
  have hp : w ^ 2 * ((w⁻¹) ^ 2 + 3 * w⁻¹ + 3) = P w := by
    dsimp [P]
    field_simp [hw]
    ring
  have hq : w ^ 2 * ((w⁻¹) ^ 2 + 3 * w⁻¹ + 1) = Q w := by
    dsimp [Q]
    field_simp [hw]
    ring
  rw [flowerBracket, reciprocal_monomials n w _ _ hw, hp, hq]
  rfl

theorem H_times_denominator {n : ℕ} {lam v : ℂ}
    (hp : P (reciprocalCoordinate lam v) ≠ 0)
    (hq : Q (reciprocalCoordinate lam v) ≠ 0) :
    H n lam v * P (reciprocalCoordinate lam v) ^ n = numerator n (reciprocalCoordinate lam v) := by
  rw [H, A_eq_rational hp hq, B_eq_rational hp]
  dsimp [numerator]
  field_simp [hp]

theorem coordinate_ne_zero {lam v : ℂ} (hlam : lam ≠ 0) (hv : lam + v ≠ 0) :
    reciprocalCoordinate lam v ≠ 0 := by
  apply mul_ne_zero (initialCoordinate_ne_zero lam)
  have heq : 1 + v / lam = (lam + v) / lam := by rw [add_div, div_self hlam]
  rw [heq]
  exact div_ne_zero hv hlam

theorem H_zero_returns_graph_root {n : ℕ} {lam v : ℂ}
    (hlam : lam ≠ 0) (hv : lam + v ≠ 0)
    (hw : ‖reciprocalCoordinate lam v‖ ≤ (1 / 16 : ℝ)) (hH : H n lam v = 0) :
    (Counting.complexDominationPolynomial n).eval (reciprocalCoordinate lam v)⁻¹ = 0 := by
  have hw0 := coordinate_ne_zero hlam hv
  obtain ⟨hp, hq⟩ := slitPlane_bounds hw
  have h := H_times_denominator (n := n) (Complex.slitPlane_ne_zero hp) (Complex.slitPlane_ne_zero hq)
  rw [hH, zero_mul] at h
  have hnum : numerator n (reciprocalCoordinate lam v) = 0 := h.symm
  have hbr : flowerBracket n (reciprocalCoordinate lam v)⁻¹ = 0 := by
    rw [← reciprocal_identity n hw0] at hnum
    exact (mul_eq_zero.mp hnum).resolve_left (pow_ne_zero _ hw0)
  apply (Counting.eval_eq_zero_iff_bracket (inv_ne_zero hw0)).2
  exact hbr

/-- A sequence of genuine roots of the actual finite graph's ordinary domination polynomial. -/
theorem exists_actual_graph_roots : ∃ lam v z : ℕ → ℂ,
    Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0) ∧ Tendsto v atTop (𝓝 0) ∧
    (∀ n, z n = (reciprocalCoordinate (lam n) (v n))⁻¹) ∧
    ∀ᶠ (n : ℕ) in atTop, z n ≠ 0 ∧
      (Counting.complexDominationPolynomial n).eval (z n) = 0 ∧
      lam n * Complex.exp (lam n) = -(4 * (n : ℂ)) := by
  obtain ⟨lam, hd, he⟩ := exists_square_flower_lambert
  have hle := he.mono fun n hn => hn.2.2
  obtain ⟨v, hvlim, hvzero⟩ := exists_perturbed_zeros lam hd hle
  let z : ℕ → ℂ := fun n => (reciprocalCoordinate (lam n) (v n))⁻¹
  refine ⟨lam, v, z, hd, hvlim, (fun n => rfl), ?_⟩
  have hn := lam_norm_tendsto_atTop logScale lam logScale_tendsto_atTop hd
  have hε := epsilon_tendsto_zero logScale lam logScale_tendsto_atTop hd
  filter_upwards [hle, hvzero, hn.eventually_gt_atTop (1 / 4),
    hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))] with n he hv hn hεn
  have hvnorm : ‖v n‖ ≤ (1 / 4 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv.1
  have hlam : lam n ≠ 0 := by intro h; simp only [h, norm_zero] at hn; linarith
  have hv0 : lam n + v n ≠ 0 := by
    intro h
    have ht := norm_sub_norm_le (lam n) (-v n)
    rw [norm_neg, sub_neg_eq_add, h, norm_zero] at ht
    linarith
  have hw : ‖reciprocalCoordinate (lam n) (v n)‖ ≤ (1 / 16 : ℝ) :=
    (reciprocalCoordinate_bound _ _ hvnorm).trans hεn.le
  exact ⟨inv_ne_zero (coordinate_ne_zero hlam hv0), H_zero_returns_graph_root hlam hv0 hw hv.2.1, he⟩

#print axioms reciprocal_identity
#print axioms H_zero_returns_graph_root
#print axioms exists_actual_graph_roots
end Transfer
end SquareFlowerCompletion
