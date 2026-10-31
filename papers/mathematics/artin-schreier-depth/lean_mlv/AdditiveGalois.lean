import LegacyCompat

/-!
# Algebraic pieces for NT-C-AS-DEPTH

These are actual statements about fields, polynomials, and algebra automorphisms.
They do not formalize Hahn-series truncation or the full intrinsic-depth theorem.
All proofs use the pinned mathlib library. The generated-field splitting argument
adapts the proof pattern of `AddSubgroup.isSplittingField_additivePolynomial_sub_C`
from Tau Ceti, copyright 2026 the Tau Ceti contributors, Apache-2.0:
https://github.com/TauCetiProject/TauCeti/blob/343f4606bc2693cfa7e778296dd0fe4dbb041a39/TauCeti/FieldTheory/ArtinSchreier/Additive.lean
The linearized-polynomial, Ore, and translation proofs here were written directly
against Lean 4.19 mathlib. This file makes no novelty claim for these algebraic facts.
-/

noncomputable section

open scoped BigOperators Polynomial IntermediateField
open Polynomial

namespace NTCThird

section Ore

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- A finite-dimensional extension gives a nontrivial finite relation among
the actual Frobenius powers. This is the Ore relation used in the manuscript. -/
theorem ore_relation [FiniteDimensional K E] (p : ℕ) (z : E) :
    ∃ s : Finset ℕ, ∃ a : ℕ → K,
      (∑ i ∈ s, algebraMap K E (a i) * z ^ (p ^ i) = 0) ∧
      ∃ i ∈ s, a i ≠ 0 := by
  obtain ⟨s, a, hsum, i, hi, hai⟩ :=
    (not_linearIndependent_iff.mp
      (Module.Finite.not_linearIndependent_of_infinite
        (R := K) (fun i : ℕ => z ^ (p ^ i))))
  exact ⟨s, a, by simpa only [Algebra.smul_def] using hsum, i, hi, hai⟩

/-- The genuine linearized polynomial attached to a finite coefficient family. -/
def linearized (p : ℕ) (s : Finset ℕ) (a : ℕ → K) : K[X] :=
  ∑ i ∈ s, monomial (p ^ i) (a i)

theorem aeval_linearized (p : ℕ) (s : Finset ℕ) (a : ℕ → K) (z : E) :
    aeval z (linearized p s a) =
      ∑ i ∈ s, algebraMap K E (a i) * z ^ (p ^ i) := by
  simp [linearized]

theorem coeff_linearized (p : ℕ) (hp : 2 ≤ p) (s : Finset ℕ) (a : ℕ → K)
    (i : ℕ) (hi : i ∈ s) :
    (linearized p s a).coeff (p ^ i) = a i := by
  classical
  simp only [linearized, finset_sum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hpow : p ^ j ≠ p ^ i := fun h => hji (Nat.pow_right_injective hp h)
    simp [hpow]
  · exact fun h => False.elim (h hi)

theorem linearized_ne_zero (p : ℕ) (hp : 2 ≤ p) (s : Finset ℕ) (a : ℕ → K)
    (h : ∃ i ∈ s, a i ≠ 0) :
    linearized p s a ≠ 0 := by
  obtain ⟨i, hi, hai⟩ := h
  intro heq
  apply hai
  have hc := congrArg (fun q : K[X] => q.coeff (p ^ i)) heq
  simpa only [coeff_linearized p hp s a i hi, coeff_zero] using hc

/-- An actual nonzero linearized annihilator, with no formal proxy for
finite-dimensionality or polynomial evaluation. -/
theorem ore_nonzero_annihilator [FiniteDimensional K E]
    (p : ℕ) (hp : 2 ≤ p) (z : E) :
    ∃ s : Finset ℕ, ∃ a : ℕ → K,
      linearized p s a ≠ 0 ∧ aeval z (linearized p s a) = 0 := by
  obtain ⟨s, a, hsum, hnonzero⟩ := ore_relation (K := K) p z
  exact ⟨s, a, linearized_ne_zero p hp s a hnonzero,
    (aeval_linearized p s a z).trans hsum⟩

theorem aeval_linearized_sub (p : ℕ) [Fact p.Prime] [CharP E p]
    (s : Finset ℕ) (a : ℕ → K) (x y : E) :
    aeval (x - y) (linearized p s a) =
      aeval x (linearized p s a) - aeval y (linearized p s a) := by
  simp only [aeval_linearized, sub_pow_char_pow, mul_sub, Finset.sum_sub_distrib]

theorem linearized_comp_X_sub_C (p : ℕ) [Fact p.Prime] [CharP K p]
    (s : Finset ℕ) (a : ℕ → K) (z : K) :
    (linearized p s a).comp (X - C z) =
      linearized p s a - C ((linearized p s a).eval z) := by
  simp only [linearized, sum_comp, monomial_comp, sub_pow_char_pow,
    mul_sub, Finset.sum_sub_distrib, eval_finset_sum, eval_monomial,
    map_sum, map_mul, map_pow]
  simp only [C_mul_X_pow_eq_monomial]

theorem map_linearized {F : Type*} [Field F] (f : K →+* F)
    (p : ℕ) (s : Finset ℕ) (a : ℕ → K) :
    (linearized p s a).map f = linearized p s (fun i => f (a i)) := by
  simp only [linearized, Polynomial.map_sum, map_monomial]

theorem derivative_linearized (p : ℕ) [CharP K p]
    (s : Finset ℕ) (a : ℕ → K) (h0 : 0 ∈ s) :
    (linearized p s a).derivative = C (a 0) := by
  classical
  simp only [linearized, derivative_sum, derivative_monomial]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    simp [Nat.cast_pow, CharP.cast_eq_zero]
  · exact fun h => False.elim (h h0)

theorem linearized_sub_C_separable (p : ℕ) [CharP K p]
    (s : Finset ℕ) (a : ℕ → K) (h0 : 0 ∈ s) (ha0 : a 0 ≠ 0) (d : K) :
    (linearized p s a - C d).Separable := by
  rw [separable_def, derivative_sub, derivative_C, sub_zero,
    derivative_linearized p s a h0]
  refine ⟨0, C (a 0)⁻¹, ?_⟩
  simp [← C_mul, ha0]

theorem linearized_sub_C_ne_zero (p : ℕ) [CharP K p]
    (s : Finset ℕ) (a : ℕ → K) (h0 : 0 ∈ s) (ha0 : a 0 ≠ 0) (d : K) :
    linearized p s a - C d ≠ 0 := by
  intro h
  have hd := congrArg derivative h
  simp only [derivative_sub, derivative_C, sub_zero,
    derivative_linearized p s a h0, derivative_zero] at hd
  exact ha0 (C_eq_zero.mp hd)

theorem linearized_sub_C_ne_zero_of_nonzero (p : ℕ) (hp : 2 ≤ p)
    (s : Finset ℕ) (a : ℕ → K) (hn : ∃ i ∈ s, a i ≠ 0) (d : K) :
    linearized p s a - C d ≠ 0 := by
  obtain ⟨i, hi, hai⟩ := hn
  intro h
  have hc := congrArg (fun f : K[X] => f.coeff (p ^ i)) h
  change (linearized p s a - C d).coeff (p ^ i) = (0 : K[X]).coeff (p ^ i) at hc
  have hp0 : p ≠ 0 := by omega
  rw [coeff_sub, coeff_linearized p hp s a i hi,
    coeff_C_ne_zero (pow_ne_zero _ hp0), sub_zero, coeff_zero] at hc
  exact hai hc

end Ore

section Constants

variable {k E : Type*} [Field k] [Field E] [Algebra k E] [IsAlgClosed k]

/-- A root in any field extension of a nonzero polynomial over an algebraically
closed coefficient field actually belongs to that coefficient field. -/
theorem polynomial_root_is_constant (P : k[X]) (hP : P ≠ 0) (z : E)
    (hz : aeval z P = 0) :
    ∃ c : k, algebraMap k E c = z := by
  have hi : IsIntegral k z := (show IsAlgebraic k z from ⟨P, hP, hz⟩).isIntegral
  have hs : ((minpoly k z).map (algebraMap k k)).Splits :=
    IsAlgClosed.splits_domain _
  exact hi.mem_range_algebraMap_of_minpoly_splits hs

end Constants

section Translation

variable {k K E : Type*}
  [Field k] [Field K] [Field E]
  [Algebra k K] [Algebra K E] [Algebra k E] [IsScalarTower k K E]

/-- Algebra automorphisms of an actually generated algebra are determined by
their value on its generator. -/
theorem aut_eq_of_generator (z : E) (hgen : Algebra.adjoin K ({z} : Set E) = ⊤)
    (σ τ : E ≃ₐ[K] E) (h : σ z = τ z) : σ = τ := by
  have hh : σ.toAlgHom = τ.toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact h
  ext x
  exact congrArg (fun f : E →ₐ[K] E => f x) hh

/-- Constant differences give the genuine translation homomorphism from the
algebra automorphism group to the additive group of the ambient field. -/
noncomputable def translationHom (z : E)
    (hconst : ∀ σ : E ≃ₐ[K] E, ∃ c : k, algebraMap k E c = σ z - z) :
    (E ≃ₐ[K] E) →* Multiplicative E where
  toFun σ := Multiplicative.ofAdd (σ z - z)
  map_one' := by simp
  map_mul' σ τ := by
    change σ (τ z) - z = (σ z - z) + (τ z - z)
    obtain ⟨c, hc⟩ := hconst τ
    have hfix : σ (τ z - z) = τ z - z := by
      rw [← hc]
      exact (σ.restrictScalars k).commutes c
    rw [map_sub] at hfix
    linear_combination hfix

theorem translationHom_injective (z : E)
    (hgen : Algebra.adjoin K ({z} : Set E) = ⊤)
    (hconst : ∀ σ : E ≃ₐ[K] E, ∃ c : k, algebraMap k E c = σ z - z) :
    Function.Injective (translationHom z hconst) := by
  intro σ τ h
  apply aut_eq_of_generator z hgen σ τ
  have hd : σ z - z = τ z - z := congrArg Multiplicative.toAdd h
  exact sub_left_inj.mp hd

theorem translation_aut_commute (z : E)
    (hgen : Algebra.adjoin K ({z} : Set E) = ⊤)
    (hconst : ∀ σ : E ≃ₐ[K] E, ∃ c : k, algebraMap k E c = σ z - z)
    (σ τ : E ≃ₐ[K] E) :
    σ * τ = τ * σ := by
  apply translationHom_injective z hgen hconst
  simp only [map_mul]
  exact mul_comm _ _

theorem translation_aut_pow (p : ℕ) [CharP E p] (z : E)
    (hgen : Algebra.adjoin K ({z} : Set E) = ⊤)
    (hconst : ∀ σ : E ≃ₐ[K] E, ∃ c : k, algebraMap k E c = σ z - z)
    (σ : E ≃ₐ[K] E) :
    σ ^ p = 1 := by
  apply translationHom_injective z hgen hconst
  rw [map_pow, map_one]
  change p • (σ z - z) = 0
  simp [nsmul_eq_mul, CharP.cast_eq_zero]

/-- The additive polynomial equation itself forces each automorphism difference
to lie in the algebraically closed constant field. -/
theorem linearized_aut_difference [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP E p]
    (s : Finset ℕ) (a : ℕ → k) (hP : linearized p s a ≠ 0)
    (z : E) (d : K) (hz : aeval z (linearized p s a) = algebraMap K E d)
    (σ : E ≃ₐ[K] E) :
    ∃ c : k, algebraMap k E c = σ z - z := by
  apply polynomial_root_is_constant (linearized p s a) hP
  rw [aeval_linearized_sub]
  have heq := aeval_algHom_apply (σ.restrictScalars k) z (linearized p s a)
  change aeval (σ z) (linearized p s a) = σ (aeval z (linearized p s a)) at heq
  rw [heq, hz, σ.commutes, sub_self]

/-- A generated extension satisfying an actual nonzero additive equation over
algebraically closed constants has a commutative automorphism group of exponent p.
Normality is not assumed here. -/
theorem linearized_aut_elementary [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP E p]
    (s : Finset ℕ) (a : ℕ → k) (hP : linearized p s a ≠ 0)
    (z : E) (d : K) (hz : aeval z (linearized p s a) = algebraMap K E d)
    (hgen : Algebra.adjoin K ({z} : Set E) = ⊤) :
    (∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) ∧
      ∀ σ : E ≃ₐ[K] E, σ ^ p = 1 := by
  have hc := linearized_aut_difference p s a hP z d hz
  exact ⟨translation_aut_commute z hgen hc, translation_aut_pow p z hgen hc⟩

end Translation

section Galois

variable {k K E : Type*}
  [Field k] [Field K] [Field E]
  [Algebra k K] [Algebra K E] [Algebra k E] [IsScalarTower k K E]
  [IsAlgClosed k]

/-- One root of a constant-coefficient linearized equation makes the entire
polynomial split: all the other roots are obtained by constant translations. -/
theorem linearized_splits_of_root
    (p : ℕ) [Fact p.Prime] [CharP E p]
    (s : Finset ℕ) (a : ℕ → k) (z : E) (d : K)
    (hz : aeval z (linearized p s a) = algebraMap K E d) :
    (((linearized p s a).map (algebraMap k K) - C d).map (algebraMap K E)).Splits := by
  have hs : ((linearized p s a).map (algebraMap k E)).Splits :=
    IsAlgClosed.splits_domain _
  have ht := hs.comp_X_sub_C z
  rw [map_linearized, linearized_comp_X_sub_C] at ht
  have hz' : (linearized p s (fun i => algebraMap k E (a i))).eval z =
      algebraMap K E d := by
    rw [aeval_linearized] at hz
    simpa only [linearized, eval_finset_sum, eval_monomial] using hz
  rw [hz'] at ht
  simpa only [Polynomial.map_sub, Polynomial.map_C, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq k K E, map_linearized,
    ← IsScalarTower.algebraMap_apply k K E] using ht

/-- The separability and splitting proof for an actual generated field. The
nonzero coefficient of X is the explicit separability condition. -/
theorem linearized_isSplittingField
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP E p]
    (s : Finset ℕ) (a : ℕ → k) (h0 : 0 ∈ s) (ha0 : a 0 ≠ 0)
    (z : E) (d : K) (hz : aeval z (linearized p s a) = algebraMap K E d)
    (hgen : K⟮z⟯ = ⊤) :
    IsSplittingField K E ((linearized p s a).map (algebraMap k K) - C d) := by
  let f : K[X] := (linearized p s a).map (algebraMap k K) - C d
  have hnz : f ≠ 0 := by
    dsimp [f]
    rw [map_linearized]
    exact linearized_sub_C_ne_zero p s (fun i => algebraMap k K (a i)) h0
      ((_root_.map_ne_zero (algebraMap k K)).mpr ha0) d
  have hroot : aeval z f = 0 := by
    simp only [f, map_sub, aeval_map_algebraMap, aeval_C, hz, sub_self]
  have hint : IsIntegral K z :=
    (show IsAlgebraic K z from ⟨f, hnz, hroot⟩).isIntegral
  have hg : Algebra.adjoin K ({z} : Set E) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral hint,
      hgen, IntermediateField.top_toSubalgebra]
  refine ⟨linearized_splits_of_root p s a z d hz, top_unique ?_⟩
  rw [← hg]
  apply Algebra.adjoin_mono
  rw [Set.singleton_subset_iff, mem_rootSet_of_ne hnz]
  exact hroot

theorem linearized_isGalois
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP E p]
    (s : Finset ℕ) (a : ℕ → k) (h0 : 0 ∈ s) (ha0 : a 0 ≠ 0)
    (z : E) (d : K) (hz : aeval z (linearized p s a) = algebraMap K E d)
    (hgen : K⟮z⟯ = ⊤) : IsGalois K E := by
  letI := linearized_isSplittingField p s a h0 ha0 z d hz hgen
  apply IsGalois.of_separable_splitting_field
    (p := (linearized p s a).map (algebraMap k K) - C d)
  rw [map_linearized]
  exact linearized_sub_C_separable p s (fun i => algebraMap k K (a i)) h0
    ((_root_.map_ne_zero (algebraMap k K)).mpr ha0) d

theorem linearized_finiteDimensional
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP E p]
    (s : Finset ℕ) (a : ℕ → k) (h0 : 0 ∈ s) (ha0 : a 0 ≠ 0)
    (z : E) (d : K) (hz : aeval z (linearized p s a) = algebraMap K E d)
    (hgen : K⟮z⟯ = ⊤) : FiniteDimensional K E := by
  letI := linearized_isSplittingField p s a h0 ha0 z d hz hgen
  exact IsSplittingField.finiteDimensional E
    ((linearized p s a).map (algebraMap k K) - C d)

/-- The full constant-coefficient algebraic step: a field generated by a root
of a separable linearized equation over algebraically closed constants is finite
Galois, with commutative Galois group of exponent p. -/
theorem linearized_galois_elementary
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP E p]
    (s : Finset ℕ) (a : ℕ → k) (h0 : 0 ∈ s) (ha0 : a 0 ≠ 0)
    (z : E) (d : K) (hz : aeval z (linearized p s a) = algebraMap K E d)
    (hgen : K⟮z⟯ = ⊤) :
    IsGalois K E ∧ FiniteDimensional K E ∧
      (∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) ∧
      ∀ σ : E ≃ₐ[K] E, σ ^ p = 1 := by
  letI := linearized_finiteDimensional p s a h0 ha0 z d hz hgen
  have hg : Algebra.adjoin K ({z} : Set E) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral
      (IsIntegral.of_finite K z), hgen, IntermediateField.top_toSubalgebra]
  have hP : linearized p s a ≠ 0 :=
    linearized_ne_zero p (Fact.out : p.Prime).two_le s a ⟨0, h0, ha0⟩
  exact ⟨linearized_isGalois p s a h0 ha0 z d hz hgen, inferInstance,
    linearized_aut_elementary p s a hP z d hz hg⟩

/-- The splitting-field assertion only needs a nonzero coefficient, even if
the defining additive polynomial has an inseparable Frobenius factor. -/
theorem linearized_isSplittingField_of_nonzero
    (p : ℕ) [Fact p.Prime] [CharP E p]
    (s : Finset ℕ) (a : ℕ → k) (hn : ∃ i ∈ s, a i ≠ 0)
    (z : E) (d : K) (hz : aeval z (linearized p s a) = algebraMap K E d)
    (hgen : K⟮z⟯ = ⊤) :
    IsSplittingField K E ((linearized p s a).map (algebraMap k K) - C d) := by
  let f : K[X] := (linearized p s a).map (algebraMap k K) - C d
  have hn' : ∃ i ∈ s, algebraMap k K (a i) ≠ 0 := by
    obtain ⟨i, hi, hai⟩ := hn
    exact ⟨i, hi, (_root_.map_ne_zero (algebraMap k K)).mpr hai⟩
  have hnz : f ≠ 0 := by
    dsimp [f]
    rw [map_linearized]
    exact linearized_sub_C_ne_zero_of_nonzero p (Fact.out : p.Prime).two_le s
      (fun i => algebraMap k K (a i)) hn' d
  have hroot : aeval z f = 0 := by
    simp only [f, map_sub, aeval_map_algebraMap, aeval_C, hz, sub_self]
  have hint : IsIntegral K z :=
    (show IsAlgebraic K z from ⟨f, hnz, hroot⟩).isIntegral
  have hg : Algebra.adjoin K ({z} : Set E) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral hint,
      hgen, IntermediateField.top_toSubalgebra]
  refine ⟨linearized_splits_of_root p s a z d hz, top_unique ?_⟩
  rw [← hg]
  apply Algebra.adjoin_mono
  rw [Set.singleton_subset_iff, mem_rootSet_of_ne hnz]
  exact hroot

/-- The version directly matching the manuscript's perfect base field: no
normalization of the least Frobenius exponent is assumed. Any genuinely nonzero
linearized equation over the algebraically closed constants suffices. -/
theorem linearized_galois_elementary_of_perfect [PerfectField K]
    (p : ℕ) [Fact p.Prime] [CharP E p]
    (s : Finset ℕ) (a : ℕ → k) (hn : ∃ i ∈ s, a i ≠ 0)
    (z : E) (d : K) (hz : aeval z (linearized p s a) = algebraMap K E d)
    (hgen : K⟮z⟯ = ⊤) :
    IsGalois K E ∧ FiniteDimensional K E ∧
      (∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) ∧
      ∀ σ : E ≃ₐ[K] E, σ ^ p = 1 := by
  let f : K[X] := (linearized p s a).map (algebraMap k K) - C d
  letI : IsSplittingField K E f :=
    linearized_isSplittingField_of_nonzero p s a hn z d hz hgen
  letI : FiniteDimensional K E := IsSplittingField.finiteDimensional E f
  letI : Normal K E := Normal.of_isSplittingField f
  have hgal : IsGalois K E := ⟨⟩
  have hg : Algebra.adjoin K ({z} : Set E) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral
      (IsIntegral.of_finite K z), hgen, IntermediateField.top_toSubalgebra]
  have hP : linearized p s a ≠ 0 :=
    linearized_ne_zero p (Fact.out : p.Prime).two_le s a hn
  exact ⟨hgal, inferInstance, linearized_aut_elementary p s a hP z d hz hg⟩

end Galois

end NTCThird

#print axioms NTCThird.ore_nonzero_annihilator
#print axioms NTCThird.polynomial_root_is_constant
#print axioms NTCThird.translationHom_injective
#print axioms NTCThird.linearized_galois_elementary
#print axioms NTCThird.linearized_galois_elementary_of_perfect

