import THGStrong.Analytic
import THGStrong.Reduction

noncomputable section
open scoped InnerProductSpace

namespace THGStrong
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Transfer of the complete finite interpolation bound to an actual strongly
convex differentiable function, for curvature strictly below smoothness. -/
theorem analytic_gradient_rate_lt (cert : BalancedHistoryBound E)
    (f : E → ℝ) (g : E → E) (x : ℕ → E) (xstar : E)
    (μ L h : ℝ) (N : ℕ)
    (hμ0 : 0 ≤ μ) (hμL : μ < L) (hL : 0 < L) (hh : 0 ≤ h) (hh2 : h ≤ 2)
    (hf : StrongConvexOn Set.univ μ f)
    (hg : ∀ z, HasGradientAt f (g z) z)
    (hLip : ∀ y z, ‖g y-g z‖ ≤ L*‖y-z‖)
    (hmin : ∀ z, f xstar ≤ f z)
    (hstep : ∀ i < N, x (i+1) = x i-(h/L) • g (x i)) :
    ‖g (x N)‖ ≤ L*gradientRate (μ/L) h N*‖x 0-xstar‖ := by
  let X : ℕ → E := fun i => x i-xstar
  let G : ℕ → E := fun i => L⁻¹ • g (x i)
  let F : ℕ → ℝ := fun i => (f (x i)-f xstar)/L
  have hgz : g xstar = 0 := gradient_eq_zero_of_minimizer hg hmin
  have hκ0 : 0 ≤ μ/L := div_nonneg hμ0 (le_of_lt hL)
  have hκ1 : μ/L < 1 := (div_lt_one hL).mpr hμL
  have hXstep (i : ℕ) (hi : i < N) : X (i+1) = X i-h • G i := by
    dsimp [X, G]
    rw [hstep i hi, smul_smul, div_eq_mul_inv]
    abel
  have hQ (i : ℕ) (_hi : i ≤ N) (j : ℕ) (_hj : j ≤ N) :
      0 ≤ Q (μ/L) (X i) (X j) (G i) (G j) (F i) (F j) :=
    normalized_strong_interpolation hμL hL hf hg hLip xstar (x i) (x j)
  have hfrom (i : ℕ) (_hi : i ≤ N) : 0 ≤ Q (μ/L) 0 (X i) 0 (G i) 0 (F i) := by
    simpa only [hgz, sub_self, smul_zero, zero_div] using
      normalized_strong_interpolation hμL hL hf hg hLip xstar xstar (x i)
  have hto (i : ℕ) (_hi : i ≤ N) : 0 ≤ Q (μ/L) (X i) 0 (G i) 0 (F i) 0 := by
    simpa only [hgz, sub_self, smul_zero, zero_div] using
      normalized_strong_interpolation hμL hL hf hg hLip xstar (x i) xstar
  have hn := interpolated_gradient_rate_closed cert N h (μ/L) X G F
    hh hh2 hκ0 hκ1 hXstep hQ hfrom hto
  dsimp [G, X] at hn
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] at hn
  have hm := mul_le_mul_of_nonneg_left hn (le_of_lt hL)
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hL), one_mul] using hm

/-- When strong convexity and smoothness coincide, the centered gradient is
exactly the scalar linear map with that common constant. -/
theorem gradient_of_equal_curvature
    (f : E → ℝ) (g : E → E) (xstar : E) (L : ℝ) (hL : 0 < L)
    (hf : StrongConvexOn Set.univ L f)
    (hg : ∀ z, HasGradientAt f (g z) z)
    (hLip : ∀ y z, ‖g y-g z‖ ≤ L*‖y-z‖)
    (hmin : ∀ z, f xstar ≤ f z) (z : E) :
    g z = L • (z-xstar) := by
  have hgz := gradient_eq_zero_of_minimizer hg hmin
  have h1 := strong_first_order hf hg xstar z
  have h2 := strong_first_order hf hg z xstar
  simp only [hgz, inner_zero_left, add_zero] at h1
  have hd : xstar-z = -(z-xstar) := by abel
  rw [hd, inner_neg_right, norm_neg] at h2
  have hlower : L*‖z-xstar‖^2 ≤ ⟪g z,z-xstar⟫_ℝ := by linarith
  have hnorm := gradient_norm_le_distance hg hLip hmin z
  have hnorm2 : ‖g z‖^2 ≤ L^2*‖z-xstar‖^2 := by
    have hm := mul_self_le_mul_self (norm_nonneg (g z)) hnorm
    nlinarith only [hm]
  have hlower2 := mul_le_mul_of_nonneg_left hlower (le_of_lt hL)
  have hzero : ‖g z-L • (z-xstar)‖^2 ≤ 0 := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hL,
      real_inner_smul_right, mul_pow]
    nlinarith only [hnorm2, hlower2]
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (g z-L • (z-xstar))]

theorem equal_curvature_gradient_rate
    (f : E → ℝ) (g : E → E) (x : ℕ → E) (xstar : E)
    (L h : ℝ) (N : ℕ) (hL : 0 < L)
    (hf : StrongConvexOn Set.univ L f)
    (hg : ∀ z, HasGradientAt f (g z) z)
    (hLip : ∀ y z, ‖g y-g z‖ ≤ L*‖y-z‖)
    (hmin : ∀ z, f xstar ≤ f z)
    (hstep : ∀ i < N, x (i+1) = x i-(h/L) • g (x i)) :
    ‖g (x N)‖ = L*|1-h|^N*‖x 0-xstar‖ := by
  have hform := gradient_of_equal_curvature f g xstar L hL hf hg hLip hmin
  have hlinear (i : ℕ) (hi : i < N) :
      x (i+1)-xstar = (1-h) • (x i-xstar) := by
    rw [hstep i hi, hform, smul_smul, div_mul_cancel₀ _ (ne_of_gt hL),
      sub_smul, one_smul]
    abel
  have htraj (i : ℕ) (hi : i ≤ N) :
      x i-xstar = (1-h)^i • (x 0-xstar) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [hlinear i (Nat.lt_of_succ_le hi), ih (by omega), smul_smul, pow_succ]
      congr 1
      ring
  rw [hform, htraj N le_rfl, smul_smul, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_of_pos hL, abs_pow]

/-- Closed-parameter form of the proposed Taylor--Hendrickx--Glineur
last-gradient theorem.  The only auxiliary hypothesis is the explicit
balanced certificate; the final public theorem supplies its proof. -/
theorem analytic_gradient_rate_of_certificate (cert : BalancedHistoryBound E)
    (f : E → ℝ) (g : E → E) (x : ℕ → E) (xstar : E)
    (μ L h : ℝ) (N : ℕ)
    (hμ0 : 0 ≤ μ) (hμL : μ ≤ L) (hL : 0 < L) (hh : 0 ≤ h) (hh2 : h ≤ 2)
    (hf : StrongConvexOn Set.univ μ f)
    (hg : ∀ z, HasGradientAt f (g z) z)
    (hLip : ∀ y z, ‖g y-g z‖ ≤ L*‖y-z‖)
    (hmin : ∀ z, f xstar ≤ f z)
    (hstep : ∀ i < N, x (i+1) = x i-(h/L) • g (x i)) :
    ‖g (x N)‖ ≤ L*gradientRate (μ/L) h N*‖x 0-xstar‖ := by
  by_cases heq : μ = L
  · subst μ
    rw [equal_curvature_gradient_rate f g x xstar L h N hL hf hg hLip hmin hstep]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (oscillation_le_gradientRate (L/L) h N) (le_of_lt hL))
      (norm_nonneg _)
  · exact analytic_gradient_rate_lt cert f g x xstar μ L h N hμ0
      (lt_of_le_of_ne hμL heq) hL hh hh2 hf hg hLip hmin hstep

#print axioms gradient_of_equal_curvature
#print axioms equal_curvature_gradient_rate
#print axioms analytic_gradient_rate_of_certificate

end THGStrong
