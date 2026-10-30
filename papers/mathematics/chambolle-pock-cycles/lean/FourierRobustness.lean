import FiniteCycle

/-!+# Persistence of finite CP cycles with zero primal normals

The hypotheses refer to the actual finite lists of primal and dual iterates.
The conclusion is a certificate for the original projection update at every
extrapolation parameter in an explicit positive interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace AsymptoticCP

open FiniteCP

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {n d : ℕ} [NeZero n]

theorem inner_le_of_equal_norm_sq (u v : Space d) {M : ℝ}
    (hu : ‖u‖ ^ 2 = M) (hv : ‖v‖ ^ 2 = M) : ⟪u, v⟫ ≤ M := by
  have h : 0 ≤ ⟪u - v, u - v⟫ := real_inner_self_nonneg
  simp only [inner_sub_left, inner_sub_right, real_inner_comm u v,
    real_inner_self_eq_norm_sq, hu, hv] at h
  linarith

theorem neg_inner_le_of_equal_norm_sq (u v : Space d) {M : ℝ}
    (hu : ‖u‖ ^ 2 = M) (hv : ‖v‖ ^ 2 = M) : -⟪u, v⟫ ≤ M := by
  have h : 0 ≤ ⟪u + v, u + v⟫ := real_inner_self_nonneg
  simp only [inner_add_left, inner_add_right, real_inner_comm u v,
    real_inner_self_eq_norm_sq, hu, hv] at h
  linarith

theorem normal_perturbation_bound (x y : Fin n → Space d) {M : ℝ}
    (hp : ∀ i, y i = x i - x (nextIndex i))
    (hn : ∀ i, ‖y i‖ ^ 2 = M) (i j : Fin n) :
    ⟪x (nextIndex i) - x i, y j - y (nextIndex i)⟫ ≤ 2 * M := by
  have he : x (nextIndex i) - x i = -y i := by rw [hp i]; abel
  rw [he, inner_neg_left, inner_sub_right]
  have h₁ := inner_le_of_equal_norm_sq (y i) (y (nextIndex i)) (hn i) (hn _)
  have h₂ := neg_inner_le_of_equal_norm_sq (y i) (y j) (hn i) (hn j)
  linarith

theorem positive_theta_normal_certificate (x y : Fin n → Space d)
    {κ θ s M : ℝ} (hκ : 0 < κ) (hθ : 0 ≤ θ) (hs : 0 ≤ s) (hM : 0 < M)
    (hθM : θ ≤ s ^ 3 / M)
    (hp : ∀ i, y i = x i - x (nextIndex i))
    (hn : ∀ i, ‖y i‖ ^ 2 = M)
    (hb : ∀ i j, j ≠ nextIndex i →
      ⟪y i + κ • x (nextIndex i) - y (nextIndex i),
        y j - y (nextIndex i)⟫ ≤ -4 * κ * s ^ 3) :
    NormalCertificate x y κ θ := by
  constructor
  · intro i j
    have he : x i - y i - x (nextIndex i) = 0 := by rw [hp i]; abel
    rw [he, inner_zero_left]
  · intro i j
    by_cases hj : j = nextIndex i
    · rw [hj, sub_self, inner_zero_right]
    · have he : y i + κ • ((1 + θ) • x (nextIndex i) - θ • x i) - y (nextIndex i) =
          (y i + κ • x (nextIndex i) - y (nextIndex i)) +
            (κ * θ) • (x (nextIndex i) - x i) := by module
      rw [he, inner_add_left, real_inner_smul_left]
      have hm := (le_div_iff₀ hM).mp hθM
      have hc : 0 ≤ κ * θ := mul_nonneg hκ.le hθ
      have hp' := mul_le_mul_of_nonneg_left (normal_perturbation_bound x y hp hn i j) hc
      have hb' := hb i j hj
      have hs3 : 0 ≤ s ^ 3 := pow_nonneg hs _
      have hmul := mul_le_mul_of_nonneg_left hm hκ.le
      nlinarith

theorem positive_theta_nonconvergence (x y : Fin n → Space d)
    {κ θ s M : ℝ} (hκ : 0 < κ) (hθ : 0 ≤ θ) (hs : 0 ≤ s) (hM : 0 < M)
    (hθM : θ ≤ s ^ 3 / M)
    (hp : ∀ i, y i = x i - x (nextIndex i))
    (hn : ∀ i, ‖y i‖ ^ 2 = M)
    (hb : ∀ i j, j ≠ nextIndex i →
      ⟪y i + κ • x (nextIndex i) - y (nextIndex i),
        y j - y (nextIndex i)⟫ ≤ -4 * κ * s ^ 3)
    (a b : Fin n) (hne : x a ≠ x b) :
    ¬ ∃ w, Filter.Tendsto (fun k : ℕ => (cpMap x y κ θ)^[k] (x 0, y 0))
      Filter.atTop (nhds w) := by
  exact certified_nonconvergence x y κ θ
    (positive_theta_normal_certificate x y hκ hθ hs hM hθM hp hn hb) a b hne

end AsymptoticCP

#print axioms AsymptoticCP.positive_theta_nonconvergence
