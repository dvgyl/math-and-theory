import MilneOrbitSecular
import Mathlib.Tactic.ComputeDegree

/-!
# A finite algebraic secular equation

The regular shift is a root of an explicit polynomial of degree exactly six.
The sole remaining candidate is the explicitly tested spectral floor. Thus
the exact optimization contains no residual scalar minimization, and the
admissibility test selects exactly one candidate, including every hard case.
-/

open scoped BigOperators Polynomial
open Polynomial

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

noncomputable section
namespace Milne

def trustSecularPolynomial (d h : TrustVector) : Polynomial ℝ :=
  C ((h 0)^2)*(X+C (d 1))^2*(X+C (d 2))^2+
  C ((h 1)^2)*(X+C (d 0))^2*(X+C (d 2))^2+
  C ((h 2)^2)*(X+C (d 0))^2*(X+C (d 1))^2-
  (X+C (d 0))^2*(X+C (d 1))^2*(X+C (d 2))^2

theorem trustSecularPolynomial_coeff_six (d h : TrustVector) :
    (trustSecularPolynomial d h).coeff 6 = -1 := by
  unfold trustSecularPolynomial
  compute_degree!

theorem trustSecularPolynomial_degree (d h : TrustVector) :
    (trustSecularPolynomial d h).natDegree=6 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · unfold trustSecularPolynomial
    compute_degree!
  · rw [trustSecularPolynomial_coeff_six]
    norm_num

theorem trustSecularPolynomial_ne_zero (d h : TrustVector) : trustSecularPolynomial d h ≠ 0 := by
  intro hz
  have he := trustSecularPolynomial_coeff_six d h
  rw [hz] at he
  norm_num at he

theorem trustSecularPolynomial_identity (d h : TrustVector) (l : ℝ)
    (hn : ∀ i, d i+l ≠ 0) :
    (trustSecularPolynomial d h).eval l =
      ((d 0+l)^2*(d 1+l)^2*(d 2+l)^2)*
        (trustSq (trustDiagPoint d h l)-1) := by
  simp only [trustSecularPolynomial,Polynomial.eval_add,Polynomial.eval_sub,
    Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C]
  simp only [trustSq,trustDiagPoint,Fin.sum_univ_three]
  field_simp [hn 0,hn 1,hn 2]
  ring

/-- Multiplying out the secular equation introduces no spurious root above
the spectral floor, because all three denominators are strictly positive. -/
theorem trustSecularPolynomial_regular_iff (d h : TrustVector) (l : ℝ)
    (hl : trustShiftFloor d<l) :
    (trustSecularPolynomial d h).IsRoot l ↔ trustSq (trustDiagPoint d h l)=1 := by
  have hn : ∀ i, d i+l ≠ 0 := fun i => ne_of_gt (trust_regular_weights d l hl i)
  have hp : (d 0+l)^2*(d 1+l)^2*(d 2+l)^2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hn 0)) (pow_ne_zero _ (hn 1)))
      (pow_ne_zero _ (hn 2))
  rw [Polynomial.IsRoot.def,trustSecularPolynomial_identity d h l hn,
    mul_eq_zero,or_iff_right hp,sub_eq_zero]

def trustShiftCandidates (d h : TrustVector) : Finset ℝ :=
  insert (trustShiftFloor d) (trustSecularPolynomial d h).roots.toFinset

theorem trust_admissible_mem_candidates (d h : TrustVector) (l : ℝ)
    (hl : trustShiftAdmissible d h l) : l ∈ trustShiftCandidates d h := by
  rcases hl with ⟨rfl,_⟩ | ⟨hl,hn⟩
  · exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots (trustSecularPolynomial_ne_zero d h)).mpr
    exact (trustSecularPolynomial_regular_iff d h l hl).mpr hn

theorem trustShiftCandidates_card (d h : TrustVector) : (trustShiftCandidates d h).card ≤ 7 := by
  have hroots := Polynomial.card_roots' (trustSecularPolynomial d h)
  rw [trustSecularPolynomial_degree] at hroots
  calc
    (trustShiftCandidates d h).card ≤ (trustSecularPolynomial d h).roots.toFinset.card+1 :=
      Finset.card_insert_le _ _
    _ ≤ (trustSecularPolynomial d h).roots.card+1 :=
      Nat.add_le_add_right (Multiset.toFinset_card_le _) _
    _ ≤ 7 := Nat.add_le_add_right hroots 1

/-- Exact finite algebraic characterization. The first branch is the full
singular-floor/hard-case test; the second is a degree-six root test. -/
theorem trust_admissible_algebraic_iff (d h : TrustVector) (l : ℝ) :
    trustShiftAdmissible d h l ↔
      (l=trustShiftFloor d ∧ trustFloorAdmissible d h) ∨
      (trustShiftFloor d<l ∧ (trustSecularPolynomial d h).IsRoot l) := by
  unfold trustShiftAdmissible
  constructor
  · rintro (hh | ⟨hl,hn⟩)
    · exact Or.inl hh
    · exact Or.inr ⟨hl,(trustSecularPolynomial_regular_iff d h l hl).mpr hn⟩
  · rintro (hh | ⟨hl,hn⟩)
    · exact Or.inl hh
    · exact Or.inr ⟨hl,(trustSecularPolynomial_regular_iff d h l hl).mp hn⟩

/-- The finite set of at most seven candidates contains exactly one
admissible shift. This assertion is unconditional in all spectral data. -/
theorem trust_finite_algebraic_solution (d h : TrustVector) :
    ∃! l : ℝ, l ∈ trustShiftCandidates d h ∧ trustShiftAdmissible d h l := by
  obtain ⟨l,hl,hu⟩ := trust_admissible_existsUnique d h
  exact ⟨l,⟨trust_admissible_mem_candidates d h l hl,hl⟩,fun u hu' => hu u hu'.2⟩

end Milne
