module
public import BellSupport
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


@[expose] public section

/-! A true orthogonal maximally entangled basis in every finite dimension. -/
open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey

namespace WeylBell
noncomputable section
variable {d : ℕ} [NeZero d]
abbrev A (d : ℕ) := ZMod d

def phase (x : A d) : ℂ := ZMod.stdAddChar x

theorem phase_star (x : A d) : star (phase x) = phase (-x) := by
  change star ((ZMod.toCircle x : Circle) : ℂ) = ((ZMod.toCircle (-x) : Circle) : ℂ)
  rw [AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle x)).symm

theorem phase_add (x y : A d) : phase (x+y) = phase x * phase y :=
  AddChar.map_add_eq_mul _ _ _

@[simp] theorem phase_zero : phase (0 : A d) = 1 := AddChar.map_zero_eq_one _

@[simp] theorem phase_star_mul (x : A d) : star (phase x) * phase x = 1 := by
  rw [phase_star, ← phase_add]
  simp

@[simp] theorem phase_mul_star (x : A d) : phase x * star (phase x) = 1 := by
  rw [mul_comm]
  exact phase_star_mul x

theorem phase_sum_mul (b : A d) :
    ∑ x : A d, phase (b*x) = if b = 0 then (d : ℂ) else 0 := by
  by_cases hb : b=0
  · simp [hb, ZMod.card]
  · simp only [if_neg hb]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar d hb)

/-- Unnormalized Bell vector with squared norm d. -/
def rawKet (i : A d × A d) (p : A d × A d) : ℂ :=
  if p.2 = p.1+i.1 then phase (i.2*p.1) else 0

theorem raw_inner (i j : A d × A d) :
    star (rawKet i) ⬝ᵥ rawKet j = if i=j then (d : ℂ) else 0 := by
  rcases i with ⟨a,b⟩
  rcases j with ⟨c,e⟩
  by_cases hac : a=c
  · subst c
    have hp (x : A d) : star (phase (b*x)) * phase (e*x) = phase ((e-b)*x) := by
      rw [phase_star, ← phase_add]
      congr 1
      ring
    simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type, rawKet,
      apply_ite, star_zero, ite_mul, zero_mul, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, hp]
    rw [phase_sum_mul]
    by_cases hbe : b=e <;> simp [Prod.mk.injEq, sub_eq_zero, eq_comm, hbe]
  · have hne (x : A d) : x+a ≠ x+c := fun h => hac (add_left_cancel h)
    simp [dotProduct, rawKet, Fintype.sum_prod_type, hne, hac, Ne.symm hac, Prod.mk.injEq]

def projector (i : A d × A d) : Matrix (A d × A d) (A d × A d) ℂ :=
  ((d : ℝ)⁻¹) • BellSupport.outer (rawKet i)

theorem projector_positive (i : A d × A d) : (projector i).PosSemidef :=
  posSemidef_real_smul _ (BellSupport.outer_posSemidef _) _ (by positivity)

theorem projector_marginal (i : A d × A d) :
    partialTraceMatrix (projector i) =
      ((d : ℝ)⁻¹) • (1 : Matrix (A d) (A d) ℂ) := by
  rw [projector, partialTraceMatrix_smul]
  congr 1
  ext x z
  by_cases hxz : x=z
  · subst z
    simp [partialTraceMatrix, BellSupport.outer, rawKet, Matrix.one_apply]
    simpa only [Complex.star_def] using phase_mul_star (i.2*x)
  · have hne : x+i.1 ≠ z+i.1 := fun h => hxz (add_right_cancel h)
    simp [partialTraceMatrix, BellSupport.outer, rawKet, Matrix.one_apply, hxz, hne]

theorem projector_trace (i : A d × A d) : (projector i).trace = 1 := by
  rw [← partialTraceMatrix_trace, projector_marginal, Matrix.trace_smul, Matrix.trace_one]
  simp only [ZMod.card, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  exact inv_mul_cancel₀ (by exact_mod_cast (NeZero.ne d))

theorem projector_multiply (i j : A d × A d) :
    projector i * projector j = if i=j then projector i else 0 := by
  have hi := raw_inner i j
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  ext p q
  simp only [projector, BellSupport.outer, Matrix.mul_apply, Matrix.smul_apply,
    Complex.real_smul, Matrix.ite_apply, Matrix.zero_apply, Complex.ofReal_inv,
    Complex.ofReal_natCast]
  have he : (∑ x, (d : ℂ)⁻¹ * (rawKet i p * star (rawKet i x)) *
      ((d : ℂ)⁻¹ * (rawKet j x * star (rawKet j q)))) =
      ((d : ℂ)⁻¹ * (d : ℂ)⁻¹ * rawKet i p * star (rawKet j q)) *
        (star (rawKet i) ⬝ᵥ rawKet j) := by
    simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he,hi]
  by_cases hij : i=j
  · subst j
    simp only [if_true, Complex.ofReal_inv, Complex.ofReal_natCast]
    field_simp [hd]
    all_goals ring
  · simp [hij]

def rawBasis : Matrix (A d × A d) (A d × A d) ℂ := fun p i => rawKet i p

theorem basis_left_inverse :
    (rawBasis (d:=d))ᴴ * (((d : ℝ)⁻¹) • rawBasis) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
    rawBasis, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  have he : (∑ p, star (rawKet i p) * ((d : ℂ)⁻¹ * rawKet j p)) =
      (d : ℂ)⁻¹ * (star (rawKet i) ⬝ᵥ rawKet j) := by
    simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he,raw_inner]
  by_cases hij : i=j
  · subst j
    simp only [if_true, Matrix.one_apply_eq, Complex.ofReal_inv, Complex.ofReal_natCast]
    exact inv_mul_cancel₀ (by exact_mod_cast (NeZero.ne d))
  · simp [hij,Matrix.one_apply]

theorem projector_resolution : ∑ i : A d × A d, projector i = 1 := by
  have h := Matrix.mul_eq_one_comm.mp (basis_left_inverse (d:=d))
  rw [← h]
  ext p q
  simp only [Matrix.sum_apply, projector, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, rawBasis, BellSupport.outer, Complex.real_smul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The same cyclic phase, repeated over the second Bell label, supplies the
two-row tight frame used by the sharp conditional witness. -/
def framePhase (i : A d × A d) : ℂ := phase i.1

theorem framePhase_unit (i : A d × A d) : star (framePhase i) * framePhase i = 1 :=
  phase_star_mul _

theorem framePhase_sum (hd : 2 ≤ d) : ∑ i : A d × A d, framePhase i = 0 := by
  have h1 : (1 : A d) ≠ 0 := by
    intro h
    have hh : d ∣ 1 := (ZMod.natCast_zmod_eq_zero_iff_dvd 1 d).mp (by simpa using h)
    have he := Nat.eq_one_of_dvd_one hh
    omega
  have hs := phase_sum_mul (d:=d) 1
  simp only [one_mul, if_neg h1] at hs
  simp only [framePhase, Fintype.sum_prod_type, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [← Finset.mul_sum, hs, mul_zero]

end
end WeylBell
