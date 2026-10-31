import Mathlib

/-! Exact compatibility lemmas for the pinned 4.19 source during the isolated
4.35 migration. Each wrapper proves the same proposition using current mathlib.
No mathematical hypothesis or conclusion is changed. -/

namespace IntermediateField

theorem adjoin_simple_toSubalgebra_of_integral
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {a : E} (ha : IsIntegral F a) :
    (adjoin F ({a} : Set E)).toSubalgebra = Algebra.adjoin F ({a} : Set E) :=
  adjoin_simple_toSubalgebra_of_isAlgebraic ha.isAlgebraic

end IntermediateField
