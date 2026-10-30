import NAGBasic

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace DiscreteNesterov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The finite-difference velocity paired with position x_(k+1). -/
def nagVelocity (r h : ℝ) (G : E → E) (b : E) (k : ℕ) : E :=
  h⁻¹ • (nagX r h G b (k+1) - nagX r h G b k)

lemma smul_nagVelocity {r h : ℝ} (hh : h ≠ 0) (G : E → E) (b : E) (k : ℕ) :
    h • nagVelocity r h G b k = nagX r h G b (k+1) - nagX r h G b k := by
  rw [nagVelocity, smul_smul, mul_inv_cancel₀ hh, one_smul]

lemma nagVelocity_zero {r h : ℝ} (hh : h ≠ 0) (G : E → E) (b : E) :
    nagVelocity r h G b 0 = -(h • G b) := by
  have he : h⁻¹ * h^2 = h := by field_simp; ring
  change h⁻¹ • (nagX r h G b (0+1) - nagX r h G b 0) = _
  rw [nagX_succ, nagY_zero, nagX_zero]
  calc
    h⁻¹ • (b - h^2 • G b - b) = -(h⁻¹ * h^2) • G b := by module
    _ = -(h • G b) := by rw [he, neg_smul]

lemma nagY_succ_velocity {r h : ℝ} (hh : h ≠ 0) (G : E → E) (b : E) (k : ℕ) :
    nagY r h G b (k+1) =
      nagX r h G b (k+1) + (h * momentum r k) • nagVelocity r h G b k := by
  rw [nagY_succ, ← smul_nagVelocity hh G b k, smul_smul, mul_comm]

lemma nagVelocity_succ {r h : ℝ} (hh : h ≠ 0) (G : E → E) (b : E) (k : ℕ) :
    nagVelocity r h G b (k+1) =
      momentum r k • nagVelocity r h G b k - h • G (nagY r h G b (k+1)) := by
  have he1 : h⁻¹ * (h * momentum r k) = momentum r k := by field_simp
  have he2 : h⁻¹ * h^2 = h := by field_simp; ring
  have hd : nagX r h G b (k+1+1) - nagX r h G b (k+1) =
      (h * momentum r k) • nagVelocity r h G b k - h^2 • G (nagY r h G b (k+1)) := by
    calc
      _ = (nagY r h G b (k+1) - nagX r h G b (k+1)) -
          h^2 • G (nagY r h G b (k+1)) := by rw [nagX_succ]; module
      _ = _ := by rw [nagY_succ_velocity hh]; module
  change h⁻¹ • (nagX r h G b (k+1+1) - nagX r h G b (k+1)) = _
  rw [hd, smul_sub, smul_smul, smul_smul, he1, he2]

lemma nagX_next_velocity {r h : ℝ} (hh : h ≠ 0) (G : E → E) (b : E) (k : ℕ) :
    nagX r h G b (k+1+1) =
      nagX r h G b (k+1) + h • nagVelocity r h G b (k+1) := by
  rw [smul_nagVelocity hh]
  abel

/-- A nonpositive gradient coordinate makes the actual Nesterov positions
nondecreasing in that coordinate, for every nonnegative momentum. -/
theorem nagX_coordinate_monotone {r h : ℝ} (hr : 0 < r) (G : E → E) (b : E)
    (l : E →L[ℝ] ℝ) (hG : ∀ x, l (G x) ≤ 0) :
    Monotone (fun k => l (nagX r h G b k)) := by
  have hd : ∀ k : ℕ, 0 ≤ l (nagX r h G b (k+1)) - l (nagX r h G b k) := by
    intro k
    induction k with
    | zero =>
      rw [nagX_succ, nagY_zero, nagX_zero, map_sub, map_smul]
      simp only [smul_eq_mul]
      have hn := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg h) (hG b)
      linarith only [hn]
    | succ k ih =>
      rw [nagX_succ, nagY_succ, map_sub, map_add, map_smul, map_sub, map_smul]
      simp only [smul_eq_mul]
      have h1 := mul_nonneg (momentum_nonneg hr k) ih
      have h2 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg h) (hG (nagY r h G b (k+1)))
      rw [nagY_succ] at h2
      linarith only [h1, h2]
  exact monotone_nat_of_le_succ (fun k => sub_nonneg.mp (hd k))

end DiscreteNesterov
