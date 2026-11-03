import EllipsoidCounterexample
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Dimension.Finite
import Lean.Elab.Tactic.Omega

/-!
# Nonzero product vectors in two-dimensional two-qubit subspaces

This module proves the algebraic heart of the finite rank-reduction argument:
an independent pair of two-qubit vectors spans a nonzero product vector. The
proof uses the genuine algebraic closedness theorem for C from mathlib, an
exact determinant-pencil identity, and an explicit pivot factorization.
-/

namespace ProductVector

noncomputable section

open EllipsoidCounterexample

/-- The determinant of the 2×2 coefficient matrix of a two-qubit vector. -/
def coefficientDet (v : V4) : ℂ := v 0 * v 3 - v 1 * v 2

def pencilCross (A B : V4) : ℂ :=
  A 0 * B 3 + B 0 * A 3 - A 1 * B 2 - B 1 * A 2

/-- Linear independence of a pair, expanded as scalar injectivity. -/
def IndependentPair (A B : V4) : Prop :=
  ∀ c d : ℂ, c • A + d • B = 0 → c = 0 ∧ d = 0

theorem product_determinant_zero (a b : Fin 2 → ℂ) :
    coefficientDet (product a b) = 0 := by
  simp [coefficientDet, product]
  ring

/-- The rank-one coefficient-matrix criterion, including the zero vector.
When `v ≠ 0`, the resulting product vector is nonzero automatically. -/
theorem determinant_zero_iff_product (v : V4) :
    coefficientDet v = 0 ↔ ∃ a b : Fin 2 → ℂ, product a b = v := by
  constructor
  · intro hdet
    by_cases h0 : v 0 = 0
    · by_cases h1 : v 1 = 0
      · refine ⟨![0, 1], ![v 2, v 3], ?_⟩
        ext i
        fin_cases i <;> simp [product, h0, h1]
      · have h2 : v 2 = 0 := by
          have hmul : v 1 * v 2 = 0 := by simpa [coefficientDet, h0] using hdet
          exact (mul_eq_zero.mp hmul).resolve_left h1
        refine ⟨![v 1, v 3], ![0, 1], ?_⟩
        ext i
        fin_cases i <;> simp [product, h0, h2]
    · have hcross : v 1 * v 2 = v 0 * v 3 := by
        exact (sub_eq_zero.mp hdet).symm
      refine ⟨![v 0, v 2], ![1, v 1 / v 0], ?_⟩
      ext i
      fin_cases i
      · change v 0 * 1 = v 0
        ring
      · change v 0 * (v 1 / v 0) = v 1
        simpa only [mul_comm] using div_mul_cancel₀ (v 1) h0
      · change v 2 * 1 = v 2
        ring
      · change v 2 * (v 1 / v 0) = v 3
        rw [← mul_div_assoc]
        apply (div_eq_iff h0).mpr
        simpa [mul_comm] using hcross
  · rintro ⟨a, b, rfl⟩
    exact product_determinant_zero a b

theorem determinant_pencil (A B : V4) (t : ℂ) :
    coefficientDet (A + t • B) =
      coefficientDet A + t * pencilCross A B + t ^ 2 * coefficientDet B := by
  simp [coefficientDet, pencilCross, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- An exact quadratic root, obtained from mathlib's fundamental theorem of
algebra and checked by field identities. -/
theorem complex_quadratic_has_root (a b c : ℂ) (ha : a ≠ 0) :
    ∃ t : ℂ, a * t ^ 2 + b * t + c = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (b ^ 2 - 4 * a * c)
    (n := 2) (by decide)
  refine ⟨(-b + s) / (2 * a), ?_⟩
  have hid : a * ((-b + s) / (2 * a)) ^ 2 + b * ((-b + s) / (2 * a)) + c =
      (s ^ 2 - (b ^ 2 - 4 * a * c)) / (4 * a) := by
    field_simp [ha] <;> ring_nf <;> simp
  rw [hid, hs]
  simp

theorem independent_right_ne_zero (A B : V4) (hind : IndependentPair A B) : B ≠ 0 := by
  intro hB
  have h := hind 0 1 (by simp [hB])
  norm_num at h

theorem independent_pencil_ne_zero (A B : V4) (hind : IndependentPair A B) (t : ℂ) :
    A + t • B ≠ 0 := by
  intro hp
  have h := hind 1 t (by simpa using hp)
  norm_num at h

/-- Any independent two-vector pencil contains a nonzero product vector.
The coefficients and both tensor factors are returned as witnesses. -/
theorem independent_pair_contains_product (A B : V4) (hind : IndependentPair A B) :
    ∃ c d : ℂ, ∃ a b : Fin 2 → ℂ,
      c • A + d • B ≠ 0 ∧ product a b = c • A + d • B := by
  by_cases hdetB : coefficientDet B = 0
  · obtain ⟨a, b, hab⟩ := (determinant_zero_iff_product B).mp hdetB
    exact ⟨0, 1, a, b, by simpa using independent_right_ne_zero A B hind,
      by simpa using hab⟩
  · obtain ⟨t, ht⟩ := complex_quadratic_has_root
      (coefficientDet B) (pencilCross A B) (coefficientDet A) hdetB
    have hdet : coefficientDet (A + t • B) = 0 := by
      rw [determinant_pencil]
      calc
        coefficientDet A + t * pencilCross A B + t ^ 2 * coefficientDet B =
          coefficientDet B * t ^ 2 + pencilCross A B * t + coefficientDet A := by ring
        _ = 0 := ht
    obtain ⟨a, b, hab⟩ := (determinant_zero_iff_product _).mp hdet
    exact ⟨1, t, a, b, by simpa using independent_pencil_ne_zero A B hind t,
      by simpa using hab⟩

theorem subspace_with_independent_pair_contains_product
    (S : Submodule ℂ V4) (A B : V4) (hA : A ∈ S) (hB : B ∈ S)
    (hind : IndependentPair A B) :
    ∃ a b : Fin 2 → ℂ, product a b ∈ S ∧ product a b ≠ 0 := by
  obtain ⟨c, d, a, b, hnon, heq⟩ := independent_pair_contains_product A B hind
  refine ⟨a, b, ?_, ?_⟩
  · rw [heq]
    exact S.add_mem (S.smul_mem c hA) (S.smul_mem d hB)
  · rwa [heq]

/-- Every complex two-qubit subspace of dimension at least two contains a
nonzero product vector. This is the unconditional finite-dimensional theorem
used by the mathematical rank-reduction argument. -/
theorem dimension_at_least_two_contains_product (S : Submodule ℂ V4)
    (hdim : 2 ≤ Module.finrank ℂ S) :
    ∃ a b : Fin 2 → ℂ, product a b ∈ S ∧ product a b ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := ℂ) (M := S) hdim
  have hind : IndependentPair (f 0 : V4) (f 1 : V4) := by
    intro c d heq
    have heqS : c • f 0 + d • f 1 = 0 := by
      apply Subtype.ext
      exact heq
    have hsum : ∑ i : Fin 2, (![c, d] i) • f i = 0 := by
      simpa [Fin.sum_univ_succ] using heqS
    have hz := (linearIndependent_iff'.mp hf) Finset.univ ![c, d] hsum
    exact ⟨by simpa using hz 0 (Finset.mem_univ 0),
      by simpa using hz 1 (Finset.mem_univ 1)⟩
  exact subspace_with_independent_pair_contains_product S (f 0) (f 1)
    (f 0).property (f 1).property hind

/-- The sharp two-qubit upper bound on a completely entangled subspace. -/
theorem completely_entangled_subspace_dimension_le_one (S : Submodule ℂ V4)
    (hprod : ∀ a b : Fin 2 → ℂ, product a b ∈ S → product a b = 0) :
    Module.finrank ℂ S ≤ 1 := by
  by_contra h
  have hdim : 2 ≤ Module.finrank ℂ S := by omega
  obtain ⟨a, b, hab, hnon⟩ := dimension_at_least_two_contains_product S hdim
  exact hnon (hprod a b hab)

#print axioms determinant_zero_iff_product
#print axioms complex_quadratic_has_root
#print axioms independent_pair_contains_product
#print axioms subspace_with_independent_pair_contains_product
#print axioms dimension_at_least_two_contains_product
#print axioms completely_entangled_subspace_dimension_le_one

end

end ProductVector
