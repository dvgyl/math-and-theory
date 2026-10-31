import HenselianBridge
import HenselianKrasner
import HenselianRationalNorm
import HenselianAlgebraicGlue
import Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionUniqueness
import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue

/-!
# Standard henselianity implies exact rational valuation extension

The assumption is mathlib's simple-root lifting on the specified valuation
ring. NYLL supplies the standard factorization and uniqueness-of-valuation-ring
theorems, with its original Apache 2.0 notices retained in the vendored sources.

Finite existence uses the actual field norm and its proved nonarchimedean
absolute value. Arbitrary algebraic existence is obtained by gluing the finite
extensions. Rational normalization turns ring uniqueness into pointwise
uniqueness using a base element of value one.
-/

noncomputable section

namespace NTCThird

open AlgebraicNumberTheory.Valuations

universe u

theorem rationalValuationAbsoluteValue_nonarchimedean
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℚ)) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue (rationalValuationAbsoluteValue v) :=
  LubinTate.Valuations.nonarchimedean_of_strong_triangle
    (rationalValuationAbsoluteValue v) (rationalValuationExp_strongTriangle v)

theorem rationalValuationAbsoluteValue_valuationSubring
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℚ)) :
    absoluteValueValuationSubring (rationalValuationAbsoluteValue v)
      (rationalValuationAbsoluteValue_nonarchimedean v) =
      (AddValuation.toValuation v).valuationSubring := by
  ext x
  rw [mem_absoluteValueValuationSubring_iff]
  change rationalValueExp (v x) ≤ 1 ↔ 0 ≤ v x
  rw [← rationalValueExp_zero]
  exact rationalValueExp_le_iff _ _

/-- Genuine simple-root lifting on the specified valuation ring gives a
rational-valued extension on every finite field extension. -/
theorem exists_finite_rationalAddValuation_of_henselianLocalRing
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (v : AddValuation F (WithTop ℚ))
    [HenselianLocalRing (AddValuation.toValuation v).valuationSubring] :
    ∃ w : AddValuation E (WithTop ℚ),
      ∀ a : F, w (algebraMap F E a) = v a := by
  let av := rationalValuationAbsoluteValue v
  have hna : LubinTate.Valuations.NonarchimedeanAbsoluteValue av :=
    rationalValuationAbsoluteValue_nonarchimedean v
  let V := absoluteValueValuationSubring av hna
  have hV : V = (AddValuation.toValuation v).valuationSubring :=
    rationalValuationAbsoluteValue_valuationSubring v
  letI : HenselianRing V (IsLocalRing.maximalIdeal V) := by
    rw [hV]
    infer_instance
  have hfactor : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty V :=
    DiscreteValuationField.henselFactorization_of_henselianRing V
  let aw : AbsoluteValue E ℝ :=
    normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization av hna hfactor
  have hstrong : ∀ x y : E, aw (x + y) ≤ max (aw x) (aw y) :=
    normFormula_finiteExtensionNormFormulaValue_strong_triangle_of_henselFactorization
      av hna hfactor
  have hnorm : ∀ x : E, aw x =
      Real.rpow (rationalValueExp (v (Algebra.norm F x)))
        (1 / (Module.finrank F E : ℝ)) := fun _ => rfl
  exact ⟨rationalNormValuation v aw hstrong hnorm,
    rationalNormValuation_algebraMap v aw hstrong hnorm⟩

/-- Exact restriction of rational additive valuations supplies the standard
extension class for the canonical valuation of the specified valuation ring. -/
theorem canonical_hasExtension_of_rational_extends
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (v : AddValuation F (WithTop ℚ)) (w : AddValuation E (WithTop ℚ))
    (hext : ∀ a : F, w (algebraMap F E a) = v a) :
    (AddValuation.toValuation v).valuationSubring.valuation.HasExtension
      (AddValuation.toValuation w) := by
  constructor
  have hbase : (AddValuation.toValuation v).IsEquiv
      ((AddValuation.toValuation w).comap (algebraMap F E)) := by
    apply Valuation.IsEquiv.of_eq
    apply Valuation.ext
    intro a
    exact (hext a).symm
  exact (Valuation.isEquiv_valuation_valuationSubring _).symm.trans hbase

/-- Standard henselianity plus one fixed nonzero rational value gives
pointwise uniqueness of rational extensions on each algebraic field. -/
theorem unique_rationalAddValuation_of_henselianLocalRing
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]
    (v : AddValuation F (WithTop ℚ))
    [HenselianLocalRing (AddValuation.toValuation v).valuationSubring]
    (t : F) (ht : v t = (1 : WithTop ℚ)) :
    UniqueAddValuationExtension v E := by
  intro w₁ w₂ hext₁ hext₂
  letI := canonical_hasExtension_of_rational_extends v w₁ hext₁
  letI := canonical_hasExtension_of_rational_extends v w₂ hext₂
  have hring :
      (AddValuation.toValuation w₁).valuationSubring =
        (AddValuation.toValuation w₂).valuationSubring :=
    ValuationTheory.Henselian.valuationSubring_eq_of_henselianRing
      (AddValuation.toValuation v).valuationSubring
      (AddValuation.toValuation w₁) (AddValuation.toValuation w₂)
  exact rationalAddValuation_eq_of_valuationSubring_eq_of_one
    w₁ w₂ hring (algebraMap F E t) ((hext₁ t).trans ht) ((hext₂ t).trans ht)

/-- The full bridge: genuine simple-root henselianity of the specified
valuation ring implies existence and pointwise uniqueness of an exact
rational-valued extension to every algebraic field extension. -/
theorem rationalValuedHenselian_of_henselianLocalRing
    {F : Type u} [Field F] (v : AddValuation F (WithTop ℚ))
    [HenselianLocalRing (AddValuation.toValuation v).valuationSubring]
    (t : F) (ht : v t = (1 : WithTop ℚ)) :
    RationalValuedHenselian v := by
  intro E _ _ _
  obtain ⟨w, hw⟩ := exists_rationalAddValuation_of_finite_extensions (E := E) v
    (fun S hS => by
      letI : FiniteDimensional F S := hS
      exact exists_finite_rationalAddValuation_of_henselianLocalRing v)
    (fun S _ => unique_rationalAddValuation_of_henselianLocalRing v t ht)
  refine ⟨w, hw, ?_⟩
  intro w' hw'
  exact unique_rationalAddValuation_of_henselianLocalRing v t ht w' w hw' hw

/-- The bridge specialized to the precise Hahn base occurring in the tower
theorems. The actual monomial y supplies the normalization element. -/
theorem hahn_rationalValuedHenselian_of_henselianLocalRing
    {k : Type u} [Field k]
    (K : IntermediateField k (HahnSeries ℚ k))
    [HenselianLocalRing (AddValuation.toValuation
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K))).valuationSubring]
    (hy : HahnSeries.single (1 : ℚ) (1 : k) ∈ K) :
    RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)) := by
  apply rationalValuedHenselian_of_henselianLocalRing _
    (⟨HahnSeries.single (1 : ℚ) (1 : k), hy⟩ : K)
  change (HahnSeries.single (1 : ℚ) (1 : k)).orderTop = (1 : WithTop ℚ)
  exact HahnSeries.orderTop_single one_ne_zero

end NTCThird

