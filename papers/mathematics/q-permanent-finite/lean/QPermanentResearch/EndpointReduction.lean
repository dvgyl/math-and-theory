import QPermanentResearch.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Genuine endpoint-to-counterexample reductions for the finite q-permanent.
The matrix derivative is the actual derivative proved in Basic.lean.
-/

namespace QPermanentResearch

open Filter Set Topology
open scoped BigOperators

theorem exists_rational_interior_decrease {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hneg : qPermanentDerivative A 1 < 0) :
    ∃ q₁ q₂ : ℚ, 0 < q₁ ∧ q₁ < q₂ ∧ q₂ < 1 ∧
      qPermanent A (q₂ : ℝ) < qPermanent A (q₁ : ℝ) := by
  have hev : ∀ᶠ q in 𝓝 (1 : ℝ), qPermanentDerivative A q < 0 :=
    (continuous_qPermanentDerivative A).continuousAt.eventually_lt
      continuousAt_const hneg
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp hev
  let a : ℝ := max 0 (1 - ε / 2)
  have ha0 : 0 ≤ a := le_max_left _ _
  have ha1 : a < 1 := by
    dsimp [a]
    exact max_lt_iff.mpr ⟨by norm_num, by linarith⟩
  have haε : 1 - ε / 2 ≤ a := le_max_right _ _
  have hneg_interval : ∀ x ∈ Icc a 1, qPermanentDerivative A x < 0 := by
    intro x hx
    apply hb
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.2)]
    linarith [hx.1]
  have hanti : StrictAntiOn (qPermanent A) (Icc a 1) :=
    strictAntiOn_of_deriv_neg (convex_Icc a 1)
      (continuous_qPermanent A).continuousOn (fun x hx => by
        rw [deriv_qPermanent]
        exact hneg_interval x (interior_subset hx))
  obtain ⟨q₂, hq₂a, hq₂1⟩ := exists_rat_btwn ha1
  obtain ⟨q₁, hq₁a, hq₁₂⟩ := exists_rat_btwn hq₂a
  have hq₁0 : (0 : ℝ) < q₁ := lt_of_le_of_lt ha0 hq₁a
  have hq₁1 : (q₁ : ℝ) < 1 := lt_trans hq₁₂ hq₂1
  refine ⟨q₁, q₂, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hq₁0
  · exact_mod_cast hq₁₂
  · exact_mod_cast hq₂1
  · exact hanti ⟨hq₁a.le, hq₁1.le⟩ ⟨hq₂a.le, hq₂1.le⟩ hq₁₂

def diagonalRegularization {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A + Matrix.diagonal (fun _ => η)

@[simp] theorem diagonalRegularization_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : diagonalRegularization A 0 = A := by
  simp [diagonalRegularization]

theorem continuous_diagonalRegularization {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Continuous (diagonalRegularization A) := by
  unfold diagonalRegularization
  fun_prop

theorem diagonalRegularization_posDef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {η : ℝ} (hη : 0 < η) : (diagonalRegularization A η).PosDef := by
  exact Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.diagonal (fun _ => hη))

theorem exists_posdef_regularization {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hneg : qPermanentDerivative A 1 < 0)
    {bound : ℝ} (hbound : 0 < bound) :
    ∃ η : ℝ, 0 < η ∧ η < bound ∧
      (diagonalRegularization A η).PosDef ∧
      qPermanentDerivative (diagonalRegularization A η) 1 < 0 := by
  have hc : Continuous (fun η : ℝ =>
      qPermanentDerivative (diagonalRegularization A η) 1) :=
    (continuous_qPermanentDerivative_matrix 1).comp
      (continuous_diagonalRegularization A)
  have hev : ∀ᶠ η in 𝓝 (0 : ℝ),
      qPermanentDerivative (diagonalRegularization A η) 1 < 0 :=
    hc.continuousAt.eventually_lt continuousAt_const (by simpa using hneg)
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp hev
  let η : ℝ := min ε bound / 2
  have hmin : 0 < min ε bound := lt_min hε hbound
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : η < ε := by
    dsimp [η]
    have := min_le_left ε bound
    linarith
  have hηbound : η < bound := by
    dsimp [η]
    have := min_le_right ε bound
    linarith
  refine ⟨η, hη, hηbound, diagonalRegularization_posDef hA hη, ?_⟩
  apply hb
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hη] using hηε

/-- A real PSD negative endpoint witness yields a real PD witness and rational
    parameters strictly inside the conjectured interval. No polynomial is
    supplied as a surrogate: all expressions are the permutation q-permanent. -/
theorem posSemidef_endpoint_to_posDef_interior {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hneg : qPermanentDerivative A 1 < 0) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef ∧
      ∃ q₁ q₂ : ℚ, 0 < q₁ ∧ q₁ < q₂ ∧ q₂ < 1 ∧
        qPermanent B (q₂ : ℝ) < qPermanent B (q₁ : ℝ) := by
  obtain ⟨η, hη, _, hPD, hD⟩ := exists_posdef_regularization A hA hneg
    (bound := 1) (by norm_num)
  exact ⟨diagonalRegularization A η, hPD,
    exists_rational_interior_decrease _ hD⟩

end QPermanentResearch
