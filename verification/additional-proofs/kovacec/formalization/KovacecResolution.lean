import KovacecGraph
import KovacecLoop

/-!
Exact failure of the polygon enclosure defined in this package.
The motivating proposal is attributed to A. Kovacec, DMUC Preprint 26-11.
Its identity with the package definitions has not been verified.
The theorem names retain the package's original identifiers.

The example satisfies the ordinary Marcus--de Oliveira convex-hull inclusion.
The determinant lies outside the closure of every bounded component of
this exact boundary complement. A nonempty bounded component is exhibited,
and the boundary has a continuous simple closed parametrization.
-/
noncomputable section
namespace KovacecResolution
open Set Matrix Complex KovacecCertificate KovacecJordan KovacecExterior KovacecGraph

/-- A simple closed curve, expressed by a continuous closed parametrization
that has no repetitions except the identified endpoints. -/
def IsJordanBoundary (Γ : Set ℂ) : Prop := ∃ T : ℝ, 0 < T ∧
  ∃ f : ℝ → ℂ, ContinuousOn f (Icc 0 T) ∧ f 0 = f T ∧
    Set.InjOn f (Ico 0 T) ∧ f '' Icc 0 T = Γ

def permutationPoint {n : ℕ} (a b : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) : ℂ :=
  ∏ i, (a i + b (σ i))

/-- The union of all segments between transposition-related permutation points. -/
def transpositionGraph {n : ℕ} (a b : Fin n → ℂ) : Set ℂ := {z |
  ∃ σ τ : Equiv.Perm (Fin n),
    (∃ i j : Fin n, i ≠ j ∧ τ = σ * Equiv.swap i j) ∧
      z ∈ segment ℝ (permutationPoint a b σ) (permutationPoint a b τ)}

/-- The boundary uses arbitrarily long straight segments, not arbitrary paths. -/
def sourceBoundary {n : ℕ} (a b : Fin n → ℂ) : Set ℂ :=
  frontier (RayExterior (transpositionGraph a b))

def IsUnitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  U * Uᴴ = 1 ∧ Uᴴ * U = 1

def determinantValue {n : ℕ} (a b : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (Matrix.diagonal a + U * Matrix.diagonal b * Uᴴ).det

/-- The package-defined enclosure predicate requires the determinant in
some bounded component closure under the displayed Jordan hypothesis.
The name Conjecture7 does not authenticate an external conjecture.
Refuting every bounded component closure avoids assuming uniqueness. -/
def Conjecture7 : Prop := ∀ (n : ℕ), 0 < n →
  ∀ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
    IsUnitary U → IsJordanBoundary (sourceBoundary a b) →
      ∃ x : ℂ, x ∉ sourceBoundary a b ∧
        Bornology.IsBounded (connectedComponentIn (sourceBoundary a b)ᶜ x) ∧
        determinantValue a b U ∈ closure (connectedComponentIn (sourceBoundary a b)ᶜ x)

theorem candidate_boundary_eq : sourceBoundary a b = J :=
  frontier_source_eq_J

theorem candidate_unitary : IsUnitary U := U_unitary

theorem candidate_determinant : determinantValue a b U = p := determinant_exact

theorem candidate_boundary_isJordan : IsJordanBoundary (sourceBoundary a b) := by
  refine ⟨6, by norm_num, q, q_continuous.continuousOn,
    q_zero_eq_six, q_injective_on_Ico, ?_⟩
  rw [candidate_boundary_eq]
  exact q_image_Icc_eq_J

theorem candidate_has_bounded_component : ∃ x : ℂ, x ∉ sourceBoundary a b ∧
    (connectedComponentIn (sourceBoundary a b)ᶜ x).Nonempty ∧
    Bornology.IsBounded (connectedComponentIn (sourceBoundary a b)ᶜ x) := by
  simpa only [candidate_boundary_eq] using exists_bounded_J_component

theorem candidate_outside_every_bounded_closure (x : ℂ)
    (hb : Bornology.IsBounded (connectedComponentIn (sourceBoundary a b)ᶜ x)) :
    determinantValue a b U ∉ closure (connectedComponentIn (sourceBoundary a b)ᶜ x) := by
  rw [candidate_boundary_eq, candidate_determinant]
  exact p_not_mem_closure_bounded_component x
    (by simpa only [candidate_boundary_eq] using hb)

/-- Complete certificate for the displayed hypotheses, including normality, exact
unitary spectral representation, actual ray-exterior boundary, Jordan
condition, existence of a bounded component, and failure of every possible
bounded-component enclosure. -/
theorem completed_counterexample :
    IsUnitary U ∧ A * Aᴴ = Aᴴ * A ∧ B * Bᴴ = Bᴴ * B ∧
    determinantValue a b U = (2/3 : ℂ) + (2/9 : ℂ) * Complex.I ∧
    IsJordanBoundary (sourceBoundary a b) ∧
    (∃ x : ℂ, x ∉ sourceBoundary a b ∧
      (connectedComponentIn (sourceBoundary a b)ᶜ x).Nonempty ∧
      Bornology.IsBounded (connectedComponentIn (sourceBoundary a b)ᶜ x)) ∧
    (∀ x : ℂ, Bornology.IsBounded (connectedComponentIn (sourceBoundary a b)ᶜ x) →
      determinantValue a b U ∉ closure (connectedComponentIn (sourceBoundary a b)ᶜ x)) := by
  exact ⟨candidate_unitary, A_normal, B_normal, candidate_determinant,
    candidate_boundary_isJordan, candidate_has_bounded_component,
    candidate_outside_every_bounded_closure⟩

/-- The witness remains an explicit convex combination of ordinary
permutation points; it does not contradict the classical convex-hull claim. -/
theorem ordinary_convex_combination :
    p = (1/9 : ℝ) • v 0 + (4/9 : ℝ) • v 3 + (4/9 : ℝ) • v 4 := by
  apply Complex.ext <;> norm_num [p, v, Complex.smul_re, Complex.smul_im]

/-- The polygon enclosure predicate defined in this package is false. -/
theorem conjecture7_false : ¬ Conjecture7 := by
  intro h
  obtain ⟨x, hx, hb, henclosure⟩ := h 3 (by decide) a b U
    candidate_unitary candidate_boundary_isJordan
  exact candidate_outside_every_bounded_closure x hb henclosure

#print axioms completed_counterexample
#print axioms conjecture7_false
#print axioms ordinary_convex_combination
end KovacecResolution
