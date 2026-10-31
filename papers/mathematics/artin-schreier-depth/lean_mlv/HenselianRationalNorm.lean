import Mathlib

/-!
# Rational valuations from the finite norm formula

The auxiliary constructions below retain the rational value group. The map
`q ↦ exp(-q)`, with `∞ ↦ 0`, is injective and reverses order, so an actual
nonarchimedean absolute-value formula verifies all the valuation axioms of the
rational norm formula. This module does not postulate an extension theorem.
-/

noncomputable section

namespace NTCThird

noncomputable def rationalValueExp : WithTop ℚ → ℝ
  | none => 0
  | some q => Real.exp (-(q : ℝ))

@[simp] theorem rationalValueExp_top :
    rationalValueExp ⊤ = 0 := rfl

@[simp] theorem rationalValueExp_coe (q : ℚ) :
    rationalValueExp (q : WithTop ℚ) = Real.exp (-(q : ℝ)) := rfl

@[simp] theorem rationalValueExp_zero :
    rationalValueExp (0 : WithTop ℚ) = 1 := by
  change Real.exp (-((0 : ℚ) : ℝ)) = 1
  simp

theorem rationalValueExp_add (a b : WithTop ℚ) :
    rationalValueExp (a + b) = rationalValueExp a * rationalValueExp b := by
  cases a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
      cases b using WithTop.recTopCoe with
      | top => simp
      | coe b =>
          rw [← WithTop.coe_add]
          simp only [rationalValueExp_coe, Rat.cast_add, neg_add, Real.exp_add]

theorem rationalValueExp_le_iff (a b : WithTop ℚ) :
    rationalValueExp a ≤ rationalValueExp b ↔ b ≤ a := by
  cases a using WithTop.recTopCoe with
  | top =>
      cases b using WithTop.recTopCoe with
      | top => simp
      | coe b => simp [Real.exp_nonneg]
  | coe a =>
      cases b using WithTop.recTopCoe with
      | top => simp [not_le.mpr (Real.exp_pos (-(a : ℝ)))]
      | coe b =>
          rw [rationalValueExp_coe, rationalValueExp_coe,
            Real.exp_le_exp, neg_le_neg_iff, WithTop.coe_le_coe]
          exact Rat.cast_le

theorem rationalValueExp_injective : Function.Injective rationalValueExp := by
  intro a b h
  exact le_antisymm
    ((rationalValueExp_le_iff b a).mp h.symm.le)
    ((rationalValueExp_le_iff a b).mp h.le)

theorem rationalValueExp_min (a b : WithTop ℚ) :
    rationalValueExp (min a b) = max (rationalValueExp a) (rationalValueExp b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left ((rationalValueExp_le_iff b a).mpr h)]
  · rw [min_eq_right h, max_eq_right ((rationalValueExp_le_iff a b).mpr h)]

/-- An explicitly supplied rational function is a valuation if its exponential
is an actual nonarchimedean absolute value. -/
noncomputable def rationalAddValuationOfExponential
    {E : Type*} [Field E] (w : AbsoluteValue E ℝ)
    (hstrong : ∀ x y : E, w (x + y) ≤ max (w x) (w y))
    (f : E → WithTop ℚ) (hf : ∀ x, rationalValueExp (f x) = w x) :
    AddValuation E (WithTop ℚ) :=
  AddValuation.of f
    (rationalValueExp_injective (by rw [hf, map_zero, rationalValueExp_top]))
    (rationalValueExp_injective (by rw [hf, map_one, rationalValueExp_zero]))
    (fun x y => (rationalValueExp_le_iff (f (x + y)) (min (f x) (f y))).mp
      (by rw [rationalValueExp_min, hf, hf, hf]; exact hstrong x y))
    (fun x y => rationalValueExp_injective
      (by rw [rationalValueExp_add, hf, hf, hf, map_mul]))

@[simp] theorem rationalAddValuationOfExponential_apply
    {E : Type*} [Field E] (w : AbsoluteValue E ℝ)
    (hstrong : ∀ x y : E, w (x + y) ≤ max (w x) (w y))
    (f : E → WithTop ℚ) (hf : ∀ x, rationalValueExp (f x) = w x) (x : E) :
    rationalAddValuationOfExponential w hstrong f hf x = f x := rfl

noncomputable def rationalValueDivide (d : ℕ) : WithTop ℚ → WithTop ℚ
  | none => ⊤
  | some q => ((q / (d : ℚ) : ℚ) : WithTop ℚ)

@[simp] theorem rationalValueDivide_top (d : ℕ) :
    rationalValueDivide d ⊤ = ⊤ := rfl

@[simp] theorem rationalValueDivide_coe (d : ℕ) (q : ℚ) :
    rationalValueDivide d (q : WithTop ℚ) = ((q / (d : ℚ) : ℚ) : WithTop ℚ) := rfl

theorem rationalValueExp_divide (d : ℕ) (hd : 0 < d) (a : WithTop ℚ) :
    rationalValueExp (rationalValueDivide d a) =
      Real.rpow (rationalValueExp a) (1 / (d : ℝ)) := by
  cases a using WithTop.recTopCoe with
  | top =>
      simp only [rationalValueDivide_top, rationalValueExp_top]
      symm
      apply Real.zero_rpow
      positivity
  | coe a =>
      simp only [rationalValueDivide_coe, rationalValueExp_coe, Rat.cast_div, Rat.cast_natCast]
      calc
        Real.exp (-(a / d : ℝ)) = Real.exp ((-(a : ℝ)) * (1 / (d : ℝ))) := by
          congr 1
          ring
        _ = _ := Real.exp_mul _ _

/-- The fixed rational finite-extension norm formula, before any valuation
axioms are asserted. -/
noncomputable def rationalNormValue
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (v : AddValuation F (WithTop ℚ)) (x : E) : WithTop ℚ :=
  rationalValueDivide (Module.finrank F E) (v (Algebra.norm F x))

/-- The actual nonarchimedean finite norm formula supplies a rational-valued
valuation, pointwise the norm formula. -/
noncomputable def rationalNormValuation
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (v : AddValuation F (WithTop ℚ))
    (w : AbsoluteValue E ℝ)
    (hstrong : ∀ x y : E, w (x + y) ≤ max (w x) (w y))
    (hnorm : ∀ x : E, w x =
      Real.rpow (rationalValueExp (v (Algebra.norm F x)))
        (1 / (Module.finrank F E : ℝ))) :
    AddValuation E (WithTop ℚ) :=
  rationalAddValuationOfExponential w hstrong (rationalNormValue v)
    (fun x => (rationalValueExp_divide _ Module.finrank_pos _).trans (hnorm x).symm)

theorem rationalValueExp_nonneg (a : WithTop ℚ) : 0 ≤ rationalValueExp a := by
  cases a using WithTop.recTopCoe with
  | top => simp
  | coe a => exact (Real.exp_pos _).le

theorem rationalValueExp_eq_zero_iff (a : WithTop ℚ) :
    rationalValueExp a = 0 ↔ a = ⊤ := by
  rw [← rationalValueExp_top]
  exact rationalValueExp_injective.eq_iff

theorem rationalValuationExp_strongTriangle
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℚ)) (x y : F) :
    rationalValueExp (v (x + y)) ≤
      max (rationalValueExp (v x)) (rationalValueExp (v y)) := by
  rw [← rationalValueExp_min]
  exact (rationalValueExp_le_iff _ _).mpr (v.map_add x y)

/-- The actual nonarchimedean absolute value associated with a rational
additive valuation, normalized by the ordinary real exponential. -/
noncomputable def rationalValuationAbsoluteValue
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℚ)) :
    AbsoluteValue F ℝ where
  toFun := fun x => rationalValueExp (v x)
  map_mul' x y := by rw [v.map_mul, rationalValueExp_add]
  nonneg' x := rationalValueExp_nonneg _
  eq_zero' x := (rationalValueExp_eq_zero_iff _).trans v.top_iff
  add_le' x y := (rationalValuationExp_strongTriangle v x y).trans
    (max_le (le_add_of_nonneg_right (rationalValueExp_nonneg _))
      (le_add_of_nonneg_left (rationalValueExp_nonneg _)))

@[simp] theorem rationalValuationAbsoluteValue_apply
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    rationalValuationAbsoluteValue v x = rationalValueExp (v x) := rfl

theorem rationalValueDivide_nsmul (d : ℕ) (hd : 0 < d) (a : WithTop ℚ) :
    rationalValueDivide d (d • a) = a := by
  cases a using WithTop.recTopCoe with
  | top =>
      cases d with
      | zero => omega
      | succ d => simp [succ_nsmul]
  | coe a =>
      rw [← WithTop.coe_nsmul, rationalValueDivide_coe]
      congr 1
      rw [nsmul_eq_mul]
      have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
      field_simp

theorem rationalNormValue_algebraMap
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (v : AddValuation F (WithTop ℚ)) (x : F) :
    rationalNormValue v (algebraMap F E x) = v x := by
  unfold rationalNormValue
  rw [Algebra.norm_algebraMap, v.map_pow]
  exact rationalValueDivide_nsmul _ Module.finrank_pos _

theorem rationalNormValuation_algebraMap
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (v : AddValuation F (WithTop ℚ))
    (w : AbsoluteValue E ℝ)
    (hstrong : ∀ x y : E, w (x + y) ≤ max (w x) (w y))
    (hnorm : ∀ x : E, w x =
      Real.rpow (rationalValueExp (v (Algebra.norm F x)))
        (1 / (Module.finrank F E : ℝ))) (x : F) :
    rationalNormValuation v w hstrong hnorm (algebraMap F E x) = v x :=
  rationalNormValue_algebraMap v x

end NTCThird

