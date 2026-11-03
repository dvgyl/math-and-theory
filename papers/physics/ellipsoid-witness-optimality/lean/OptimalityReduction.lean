import EllipsoidCounterexample
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

/-!
# Structural reduction for ellipsoid-constrained witness optimality

This module deliberately separates an abstract, kernel-checked assembly theorem
from the unformalized quantum-specific geometric inputs.  It does NOT assert the
unconditional classification for arbitrary two-qubit ellipsoids.

The assembly theorem takes a cofinal set of candidates, incomparability between
candidates, and injectivity of the detection-set representation.  None of these
inputs is the desired optimality classification itself.  A second theorem checks
the finite rank-descent argument, including a bound on the number of steps.
-/

namespace OptimalityReduction

noncomputable section

variable {α β : Type*}

/-- Maximality for the inclusion order on detection sets, within `S`. -/
def DetectionOptimal (D : α → Set β) (S : Set α) (w : α) : Prop :=
  w ∈ S ∧ ∀ v ∈ S, D w ⊆ D v → D v ⊆ D w

/-- A cofinal antichain, in a faithful detection-set representation, is exactly
the set of optimal elements. This is a structural implication, not a statement
that the geometric hypotheses have been proved for all quantum witnesses. -/
theorem classification_from_cofinal_antichain
    (D : α → Set β) (S C : Set α)
    (hCS : C ⊆ S)
    (hcofinal : ∀ w ∈ S, ∃ u ∈ C, D w ⊆ D u)
    (hantichain : ∀ w ∈ C, ∀ u ∈ C, D w ⊆ D u → D u ⊆ D w)
    (hfaithful : ∀ w ∈ S, ∀ u ∈ S, D w = D u → w = u)
    (w : α) (hw : w ∈ S) :
    DetectionOptimal D S w ↔ w ∈ C := by
  constructor
  · intro hopt
    obtain ⟨u, hu, hwu⟩ := hcofinal w hw
    have huw := hopt.2 u (hCS hu) hwu
    have heq := hfaithful w hw u (hCS hu) (Set.Subset.antisymm hwu huw)
    simpa only [heq] using hu
  · intro hc
    refine ⟨hw, ?_⟩
    intro v hv hwv
    obtain ⟨u, hu, hvu⟩ := hcofinal v hv
    exact Set.Subset.trans hvu (hantichain w hc u hu (Set.Subset.trans hwv hvu))

/-- Even without a faithful representation, all optimal detection sets are
represented by candidates. This is the appropriate quotient-level statement. -/
theorem optimal_detection_set_is_candidate
    (D : α → Set β) (S C : Set α)
    (hCS : C ⊆ S)
    (hcofinal : ∀ w ∈ S, ∃ u ∈ C, D w ⊆ D u)
    (w : α) (hw : DetectionOptimal D S w) :
    ∃ u ∈ C, D w = D u := by
  obtain ⟨u, hu, hwu⟩ := hcofinal w hw.1
  exact ⟨u, hu, Set.Subset.antisymm hwu (hw.2 u (hCS hu) hwu)⟩

/-- An explicitly counted finite chain of refinement steps. -/
inductive ReductionChain (step : α → α → Prop) : α → α → ℕ → Prop where
  | refl (q : α) : ReductionChain step q q 0
  | cons {q r s : α} {n : ℕ} :
      step q r → ReductionChain step r s n → ReductionChain step q s (n + 1)

/-- A positive-remainder step with a strictly smaller source rank. -/
def RankStep [Add β] (rank : α → ℕ) (image : α → β)
    (Positive : β → Prop) (q r : α) : Prop :=
  rank r < rank q ∧ ∃ p, Positive p ∧ image q = image r + p

/-- Exact finite rank reduction.  The positive cone need only contain zero and
be closed under addition.  If every source of rank at least two admits a
positive-remainder rank drop, and rank-zero sources have positive images, then
a nonpositive image refines to rank one.  The number `k` of steps satisfies
`k + 1 ≤ rank q`; hence a source of rank at most four requires at most three
steps.  Product-vector existence and the matrix rank-drop formula are separate
quantum/linear-algebra inputs, not silently assumed to be formalized here. -/
theorem finite_rank_one_refinement [AddCommMonoid β]
    (rank : α → ℕ) (image : α → β) (Positive : β → Prop)
    (hzero : Positive 0)
    (hadd : ∀ x y, Positive x → Positive y → Positive (x + y))
    (hrank0 : ∀ q, rank q = 0 → Positive (image q))
    (hstep : ∀ q, 2 ≤ rank q → ∃ r, RankStep rank image Positive q r)
    (q : α) (hq : ¬ Positive (image q)) :
    ∃ r p k, rank r = 1 ∧ Positive p ∧ image q = image r + p ∧
      ReductionChain (RankStep rank image Positive) q r k ∧ k + 1 ≤ rank q := by
  have aux : ∀ n : ℕ, ∀ q : α, rank q = n → ¬ Positive (image q) →
      ∃ r p k, rank r = 1 ∧ Positive p ∧ image q = image r + p ∧
        ReductionChain (RankStep rank image Positive) q r k ∧ k + 1 ≤ rank q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hqn hnon
      have hn0 : n ≠ 0 := by
        intro hn
        exact hnon (hrank0 q (hqn.trans hn))
      by_cases hn1 : n ≤ 1
      · have hrank : rank q = 1 := by omega
        exact ⟨q, 0, 0, hrank, hzero, by simp,
          ReductionChain.refl q, by omega⟩
      · obtain ⟨r, hqr⟩ := hstep q (by omega)
        obtain ⟨hrank, p, hp, hqp⟩ := hqr
        have hrnon : ¬ Positive (image r) := by
          intro hr
          apply hnon
          rw [hqp]
          exact hadd _ _ hr hp
        obtain ⟨s, p', k, hs, hp', hsp, hchain, hk⟩ :=
          ih (rank r) (by omega) r rfl hrnon
        refine ⟨s, p' + p, k + 1, hs, hadd _ _ hp' hp, ?_, ?_, ?_⟩
        · rw [hqp, hsp, add_assoc]
        · exact ReductionChain.cons ⟨hrank, p, hp, hqp⟩ hchain
        · omega
  exact aux (rank q) q rfl hq

theorem rank_four_requires_at_most_three_steps [AddCommMonoid β]
    (rank : α → ℕ) (image : α → β) (Positive : β → Prop)
    (hzero : Positive 0)
    (hadd : ∀ x y, Positive x → Positive y → Positive (x + y))
    (hrank0 : ∀ q, rank q = 0 → Positive (image q))
    (hstep : ∀ q, 2 ≤ rank q → ∃ r, RankStep rank image Positive q r)
    (q : α) (hq : ¬ Positive (image q)) (hrank : rank q ≤ 4) :
    ∃ r p k, rank r = 1 ∧ Positive p ∧ image q = image r + p ∧
      ReductionChain (RankStep rank image Positive) q r k ∧ k ≤ 3 := by
  obtain ⟨r, p, k, hr, hp, heq, hc, hk⟩ :=
    finite_rank_one_refinement rank image Positive hzero hadd hrank0 hstep q hq
  exact ⟨r, p, k, hr, hp, heq, hc, by omega⟩

/-- Coefficients of the exact refinement path. No limit or numerical argument
is used: every `t > 0` has a strictly positive remainder coefficient and a
strictly subunit witness coefficient. The additional `t ≤ 1` condition is
needed only when the path is used as a convex combination. -/
theorem interpolation_coefficients (a t : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (ht : 0 < t) :
    let k := a + (1 - a) * t
    0 < k ∧ 0 < a / k ∧ a / k < 1 ∧ 0 < t / k ∧
      (a / k) * ((1 - t) * a + t) = a ∧
      (a / k) * (1 - t) + t / k = 1 := by
  dsimp
  have hprod : 0 < (1 - a) * t := mul_pos (sub_pos.mpr ha1) ht
  have hk : 0 < a + (1 - a) * t := add_pos ha0 hprod
  have hak : a < a + (1 - a) * t := lt_add_of_pos_right a hprod
  refine ⟨hk, div_pos ha0 hk, (div_lt_one hk).mpr hak, div_pos ht hk, ?_, ?_⟩
  · rw [show (1 - t) * a + t = a + (1 - a) * t by ring]
    exact div_mul_cancel₀ a (ne_of_gt hk)
  · calc
      a / (a + (1 - a) * t) * (1 - t) + t / (a + (1 - a) * t) =
          (a * (1 - t) + t) / (a + (1 - a) * t) := by ring
      _ = (a + (1 - a) * t) / (a + (1 - a) * t) := by congr 1 <;> ring
      _ = 1 := div_self (ne_of_gt hk)

theorem affine_decomposition_of_coefficients [AddCommGroup β] [Module ℝ β]
    (W U P : β) (a b e t : ℝ)
    (hdecomp : W = a • U + P)
    (hU : b * ((1 - t) * a + t) = a)
    (hP : b * (1 - t) + e = 1) :
    W = b • ((1 - t) • W + t • U) + e • P := by
  calc
    W = a • U + P := hdecomp
    _ = (b * ((1 - t) * a + t)) • U + (b * (1 - t) + e) • P := by
      rw [hU, hP, one_smul]
    _ = b • ((1 - t) • W + t • U) + e • P := by
      rw [hdecomp]
      module

/-- The positive-remainder interpolation identity holds in any real module,
and therefore in particular for Hermitian complex matrices. Cone preservation,
normalization, and chirality continuity are separate applications of it. -/
theorem interpolation_decomposition [AddCommGroup β] [Module ℝ β]
    (W U P : β) (a t : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hdecomp : W = a • U + P) :
    W = (a / (a + (1 - a) * t)) • ((1 - t) • W + t • U) +
      (t / (a + (1 - a) * t)) • P := by
  obtain ⟨hk, hb0, hb1, he0, hU, hP⟩ := interpolation_coefficients a t ha0 ha1 ht
  exact affine_decomposition_of_coefficients W U P a _ _ t hdecomp hU hP

theorem interpolation_difference [AddCommGroup β] [Module ℝ β]
    (W U : β) (t : ℝ) :
    ((1 - t) • W + t • U) - W = t • (U - W) := by
  module

namespace QuantumConnection

open EllipsoidCounterexample

/-- The actual detected density matrices, using the complex matrix definitions
of the counterexample development. -/
def detected (W : M4) : Set M4 := {ρ | State ρ ∧ expect W ρ < 0}

theorem finer_iff_subset (V W : M4) : Finer V W ↔ detected W ⊆ detected V := by
  constructor
  · intro h ρ hρ
    exact ⟨hρ.1, h ρ hρ.1 hρ.2⟩
  · intro h ρ hρ hW
    exact (h ⟨hρ, hW⟩).2

theorem strictly_finer_iff (V W : M4) :
    StrictlyFiner V W ↔ detected W ⊆ detected V ∧ ¬ detected V ⊆ detected W := by
  constructor
  · rintro ⟨hf, ρ, hρ, hV, hW⟩
    refine ⟨(finer_iff_subset V W).mp hf, ?_⟩
    intro hback
    have hneg := (hback ⟨hρ, hV⟩).2
    linarith
  · rintro ⟨hf, hback⟩
    refine ⟨(finer_iff_subset V W).mpr hf, ?_⟩
    classical
    have hbad : ∃ ρ, ρ ∈ detected V ∧ ρ ∉ detected W := by
      by_contra h
      apply hback
      intro ρ hρ
      by_contra hρW
      exact h ⟨ρ, hρ, hρW⟩
    obtain ⟨ρ, hρ, hρW⟩ := hbad
    refine ⟨ρ, hρ.1, hρ.2, ?_⟩
    by_contra hnon
    exact hρW ⟨hρ.1, lt_of_not_ge hnon⟩

theorem optimalAmong_iff_detectionOptimal (S : Set M4) (W : M4) :
    OptimalAmong S W ↔ DetectionOptimal detected S W := by
  constructor
  · rintro ⟨hW, hopt⟩
    refine ⟨hW, ?_⟩
    intro V hV hWV
    by_contra hVW
    exact hopt ⟨V, hV, (strictly_finer_iff V W).mpr ⟨hWV, hVW⟩⟩
  · rintro ⟨hW, hopt⟩
    refine ⟨hW, ?_⟩
    rintro ⟨V, hV, hstrict⟩
    obtain ⟨hWV, hVW⟩ := (strictly_finer_iff V W).mp hstrict
    exact hVW (hopt V hV hWV)

/-- Matrix-specialized version of the abstract classification theorem. The
cofinality, same-orbit incomparability, and faithful-normalization hypotheses
remain explicit.  This theorem is NOT the unconditional ellipsoid theorem. -/
theorem quantum_classification_given_structural_inputs
    (S C : Set M4)
    (hCS : C ⊆ S)
    (hcofinal : ∀ W ∈ S, ∃ U ∈ C, Finer U W)
    (hantichain : ∀ W ∈ C, ∀ U ∈ C, Finer U W → Finer W U)
    (hfaithful : ∀ W ∈ S, ∀ U ∈ S, detected W = detected U → W = U)
    (W : M4) (hW : W ∈ S) :
    OptimalAmong S W ↔ W ∈ C := by
  rw [optimalAmong_iff_detectionOptimal]
  apply classification_from_cofinal_antichain detected S C hCS ?_ ?_ hfaithful W hW
  · intro V hV
    obtain ⟨U, hU, hf⟩ := hcofinal V hV
    exact ⟨U, hU, (finer_iff_subset U V).mp hf⟩
  · intro V hV U hU hVU
    exact (finer_iff_subset V U).mp
      (hantichain V hV U hU ((finer_iff_subset U V).mpr hVU))

end QuantumConnection

#print axioms classification_from_cofinal_antichain
#print axioms finite_rank_one_refinement
#print axioms rank_four_requires_at_most_three_steps
#print axioms interpolation_decomposition
#print axioms QuantumConnection.quantum_classification_given_structural_inputs

end

end OptimalityReduction
