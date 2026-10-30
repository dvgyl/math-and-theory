import TriangleCycle
import ThreeCycleFunctions
import ParameterBoundary

set_option autoImplicit false

noncomputable section

namespace CPSharpness

/-- An actual nonconstant proximal three-cycle for convex functions on their
effective domains, with identity coupling, primal step one and dual step `κ`.
The finite data are three consecutive states, with indices interpreted cyclically. -/
structure IsIdentityThreeCycle (κ θ : ℝ) (K J : Set Plane)
    (f g : Plane → ℝ) (x y : Fin 3 → Plane) : Prop where
  convex_f : ConvexOn ℝ K f
  convex_g : ConvexOn ℝ J g
  primal : ∀ i, IsProx K f (x (prev i) - y (prev i)) (x i)
  dual : ∀ i, IsProx J (fun z => κ * g z)
    (y (prev i) + κ • ((1 + θ) • x i - θ • x (prev i))) (y i)
  nonconstant : ¬ (x 0 = x 1 ∧ x 1 = x 2 ∧ y 0 = y 1 ∧ y 1 = y 2)

def HasConvexThreeCycle (κ θ : ℝ) : Prop :=
  ∃ (K J : Set Plane) (f g : Plane → ℝ) (x y : Fin 3 → Plane),
    IsIdentityThreeCycle κ θ K J f g x y

theorem actual_three_cycle_necessity {κ θ : ℝ} (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    {K J : Set Plane} {f g : Plane → ℝ} {x y : Fin 3 → Plane}
    (h : IsIdentityThreeCycle κ θ K J f g x y) :
    0 ≤ threeCyclePolynomial κ θ := by
  apply proximal_three_cycle_polynomial_nonneg h.convex_f h.convex_g
    (ContinuousLinearMap.id ℝ Plane) (by simp) hκ hθ
    (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)
  · simpa [prev, Matrix.cons_val_two] using h.primal 0
  · simpa [prev, Matrix.cons_val_two] using h.primal 1
  · simpa [prev, Matrix.cons_val_two] using h.primal 2
  · simpa [prev, Matrix.cons_val_two] using h.dual 0
  · simpa [prev, Matrix.cons_val_two] using h.dual 1
  · simpa [prev, Matrix.cons_val_two] using h.dual 2
  · exact h.nonconstant

theorem sharp_triangle_is_three_cycle (κ θ : ℝ) (hκ : 0 < κ) (hθ : 0 ≤ θ)
    (hΔ : 0 ≤ κ ^ 2 * (1 + θ) ^ 2 - 2 * κ * (1 + 3 * θ) - 3) :
    IsIdentityThreeCycle κ θ C (D (κ * (1 + θ) / 2) (1 / 2))
      (fun _ => 0) (fun _ => 0) X (Y (κ * (1 + θ) / 2) (1 / 2)) := by
  obtain ⟨hs, h₁, h₂⟩ := sharp_parameters κ θ hκ hθ hΔ
  refine ⟨convexOn_const 0 C_convex, convexOn_const 0 (D_convex _ _), ?_, ?_, ?_⟩
  · intro i
    exact primal_isProx _ _ (by norm_num) hs i
  · intro i
    simpa only [mul_zero] using dual_isProx _ _ κ θ h₁ h₂ i
  · intro h
    exact X_zero_ne_one h.1

/-- Sharp existence/nonexistence classification for actual nonconstant convex
proximal three-cycles. Necessity holds even for arbitrary contraction couplings
and real Hilbert spaces, as proved in `proximal_three_cycle_polynomial_nonneg`.
Sufficiency here is attained by compact triangles with an existing saddle. -/
theorem sharp_three_cycle_iff (κ θ : ℝ) (hκ : 0 < κ) (hθ : 0 ≤ θ) :
    HasConvexThreeCycle κ θ ↔ threeCycleBoundary θ ≤ κ := by
  constructor
  · rintro ⟨K, J, f, g, x, y, h⟩
    apply (polynomial_iff_boundary hκ.le hθ).mp
    exact actual_three_cycle_necessity hκ.le hθ h
  · intro hbound
    have hΔ := (polynomial_iff_boundary hκ.le hθ).mpr hbound
    exact ⟨C, D (κ * (1 + θ) / 2) (1 / 2), (fun _ => 0), (fun _ => 0),
      X, Y (κ * (1 + θ) / 2) (1 / 2), sharp_triangle_is_three_cycle κ θ hκ hθ hΔ⟩

/-- The attained sharp boundary gives genuine, nonconvergent algorithm iterates
on compact convex domains with a saddle; it is not merely a finite-data witness. -/
theorem sharp_three_cycle_counterexample (κ θ : ℝ) (hκ : 0 < κ) (hθ : 0 ≤ θ)
    (hbound : threeCycleBoundary θ ≤ κ) :
    IsCompact C ∧ IsCompact (D (κ * (1 + θ) / 2) (1 / 2)) ∧
    Convex ℝ C ∧ Convex ℝ (D (κ * (1 + θ) / 2) (1 / 2)) ∧
    IsBilinearSaddle C (D (κ * (1 + θ) / 2) (1 / 2)) 0 0 ∧
    (∀ n : ℕ, cycle (κ * (1 + θ) / 2) (1 / 2) (n + 1) =
      cpMap (κ * (1 + θ) / 2) (1 / 2) κ θ
        (cycle (κ * (1 + θ) / 2) (1 / 2) n)) ∧
    ¬ ∃ w : Plane × Plane,
      Filter.Tendsto
        (fun n : ℕ => (cpMap (κ * (1 + θ) / 2) (1 / 2) κ θ)^[n]
          (X 0, Y (κ * (1 + θ) / 2) (1 / 2) 0)) Filter.atTop (nhds w) := by
  have hΔ := (polynomial_iff_boundary hκ.le hθ).mpr hbound
  obtain ⟨hs, h₁, h₂⟩ := sharp_parameters κ θ hκ hθ hΔ
  exact ⟨C_compact, D_compact _ _, C_convex, D_convex _ _, zero_saddle _ _,
    cycle_recursion _ _ _ _ (by norm_num) hs h₁ h₂,
    sharp_cycle_nonconvergence κ θ hκ hθ hΔ⟩

/-- A fixed, rational-coordinate example strictly inside the usual quadratic
stability range for every positive extrapolation less than one sixth. -/
theorem counterexample_inside_quadratic_range (θ : ℝ) (hθ : 0 < θ) (hsmall : θ < 1 / 6) :
    (3 : ℝ) < 4 / (1 + 2 * θ) ∧
    IsCompact C ∧ IsCompact (D (3 / 2) (1 / 2)) ∧
    Convex ℝ C ∧ Convex ℝ (D (3 / 2) (1 / 2)) ∧
    IsBilinearSaddle C (D (3 / 2) (1 / 2)) 0 0 ∧
    ¬ ∃ w : Plane × Plane,
      Filter.Tendsto
        (fun n : ℕ => (cpMap (3 / 2) (1 / 2) 3 θ)^[n]
          (X 0, Y (3 / 2) (1 / 2) 0)) Filter.atTop (nhds w) := by
  exact ⟨product_three_below_quadratic hθ.le hsmall, C_compact, D_compact _ _,
    C_convex, D_convex _ _, zero_saddle _ _, step_three_nonconvergence θ hθ.le⟩

end CPSharpness
