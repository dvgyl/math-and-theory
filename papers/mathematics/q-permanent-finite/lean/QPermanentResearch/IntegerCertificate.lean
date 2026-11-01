import QPermanentResearch.IntegerD2

/-!
Soundness of a fully computable integer D2 endpoint certificate. A certificate
contains the orbit inputs, not a postulated real norm inequality. Its decidable
arithmetic test is connected to the actual q-permanent and to a rational
positive-definite strict decrease at two rational interior parameters.

No input passing the negative test is asserted in this module.
-/

namespace QPermanentResearch

def integerD2Ordered (S : IntegerD2State) : Prop :=
  integerPolyOrdered S.F ∧ integerPolyOrdered S.U01 ∧ integerPolyOrdered S.U02 ∧
  integerPolyOrdered S.U12 ∧ integerPolyOrdered S.V01 ∧ integerPolyOrdered S.V12

instance (S : IntegerD2State) : Decidable (integerD2Ordered S) := inferInstanceAs
  (Decidable (integerPolyOrdered S.F ∧ integerPolyOrdered S.U01 ∧ integerPolyOrdered S.U02 ∧
    integerPolyOrdered S.U12 ∧ integerPolyOrdered S.V01 ∧ integerPolyOrdered S.V12))

def integerD2ProductNorm (k : ℕ) (S : IntegerD2State) : ℤ :=
  integerParityNorm k (power3 0 0 0) S.F

def integerD2ThreeNorm (k : ℕ) (S : IntegerD2State) : ℤ :=
  integerParityNorm k (power3 0 1 1) S.U01 +
  integerParityNorm k (power3 0 0 0) S.U02 +
  integerParityNorm k (power3 1 1 0) S.U12

def integerD2CorrectionNorm (k : ℕ) (S : IntegerD2State) : ℤ :=
  integerParityNorm k (power3 1 0 1) S.V01 +
  integerParityNorm k (power3 0 0 0) S.V12

def integerD2Delta (L : List IntegerOrbit) : ℤ :=
  let S := integerD2Recurrence L
  let n := 4 * L.length
  (n.choose 2 : ℤ) * integerD2ProductNorm n S -
    (integerD2ThreeNorm (n - 2) S + integerD2CorrectionNorm (n - 2) S)

def IntegerD2Certificate (L : List IntegerOrbit) : Prop :=
  integerD2Ordered (integerD2Recurrence L) ∧ integerD2Delta L < 0

def integerD2ThreeDelta (L : List IntegerOrbit) : ℤ :=
  let S := integerD2Recurrence L
  let n := 4 * L.length
  (n.choose 2 : ℤ) * integerD2ProductNorm n S - integerD2ThreeNorm (n - 2) S

def IntegerD2ThreeCertificate (L : List IntegerOrbit) : Prop :=
  let S := integerD2Recurrence L
  (integerPolyOrdered S.F ∧ integerPolyOrdered S.U01 ∧
    integerPolyOrdered S.U02 ∧ integerPolyOrdered S.U12) ∧ integerD2ThreeDelta L < 0

instance (L : List IntegerOrbit) : Decidable (IntegerD2Certificate L) := inferInstanceAs
  (Decidable (integerD2Ordered (integerD2Recurrence L) ∧ integerD2Delta L < 0))

instance (L : List IntegerOrbit) : Decidable (IntegerD2ThreeCertificate L) := inferInstanceAs
  (Decidable ((integerPolyOrdered (integerD2Recurrence L).F ∧
    integerPolyOrdered (integerD2Recurrence L).U01 ∧
    integerPolyOrdered (integerD2Recurrence L).U02 ∧
    integerPolyOrdered (integerD2Recurrence L).U12) ∧ integerD2ThreeDelta L < 0))

private theorem power000 : powerExponent (power3 0 0 0) = 0 := by
  ext i
  fin_cases i <;> rfl

private theorem power011 : powerExponent (power3 0 1 1) = parity011 := by
  ext i
  fin_cases i <;> simp [powerExponent, powerCoord, power3, powerX, powerY, powerZ,
    parity011, Finsupp.single_apply, Fin.ext_iff]

private theorem power101 : powerExponent (power3 1 0 1) = parity101 := by
  ext i
  fin_cases i <;> simp [powerExponent, powerCoord, power3, powerX, powerY, powerZ,
    parity101, Finsupp.single_apply, Fin.ext_iff]

private theorem power110 : powerExponent (power3 1 1 0) = parity110 := by
  ext i
  fin_cases i <;> simp [powerExponent, powerCoord, power3, powerX, powerY, powerZ,
    parity110, Finsupp.single_apply, Fin.ext_iff]

theorem integerD2ProductNorm_semantics (k : ℕ) (S : IntegerD2State)
    (h : integerPolyOrdered S.F) :
    d2ProductNorm k (integerStateSemantics S) = (integerD2ProductNorm k S : ℝ) := by
  have hf := integerParityNorm_semantics k (power3 0 0 0) S.F
    (integerPolyOrdered_nodup _ h)
  simpa only [power000, parityPolynomial_zero, d2ProductNorm, integerStateSemantics,
    integerD2ProductNorm] using hf

theorem integerD2ThreeNorm_semantics (k : ℕ) (S : IntegerD2State)
    (h01 : integerPolyOrdered S.U01) (h02 : integerPolyOrdered S.U02)
    (h12 : integerPolyOrdered S.U12) :
    d2ThreeNorm k (integerStateSemantics S) = (integerD2ThreeNorm k S : ℝ) := by
  have h1 := integerParityNorm_semantics k (power3 0 1 1) S.U01
    (integerPolyOrdered_nodup _ h01)
  have h2 := integerParityNorm_semantics k (power3 0 0 0) S.U02
    (integerPolyOrdered_nodup _ h02)
  have h3 := integerParityNorm_semantics k (power3 1 1 0) S.U12
    (integerPolyOrdered_nodup _ h12)
  simp only [power000, power011, power110, parityPolynomial_zero] at h1 h2 h3
  simp only [d2ThreeNorm, integerStateSemantics, integerD2ThreeNorm, Int.cast_add,
    h1, h2, h3]

theorem integerD2CorrectionNorm_semantics (k : ℕ) (S : IntegerD2State)
    (h01 : integerPolyOrdered S.V01) (h12 : integerPolyOrdered S.V12) :
    d2CorrectionNorm k (integerStateSemantics S) = (integerD2CorrectionNorm k S : ℝ) := by
  have h1 := integerParityNorm_semantics k (power3 1 0 1) S.V01
    (integerPolyOrdered_nodup _ h01)
  have h2 := integerParityNorm_semantics k (power3 0 0 0) S.V12
    (integerPolyOrdered_nodup _ h12)
  simp only [power000, power101, parityPolynomial_zero] at h1 h2
  simp only [d2CorrectionNorm, integerStateSemantics, integerD2CorrectionNorm, Int.cast_add,
    h1, h2]

theorem integerD2_endpoint_value (L : List IntegerOrbit)
    (h : integerD2Ordered (integerD2Recurrence L)) :
    2 * qPermanentDerivative
      (d2Word (L.map integerOrbitReal) * (d2Word (L.map integerOrbitReal)).transpose) 1 =
      (integerD2Delta L : ℝ) := by
  rcases h with ⟨hF, h01, h02, h12, hv01, hv12⟩
  have hrep := d2Recurrence_represents (L.map integerOrbitReal)
  rw [← integerD2Recurrence_semantics] at hrep
  have hid := d2_exact_endpoint _ _ hrep
  rw [integerD2ProductNorm_semantics _ _ hF,
    integerD2ThreeNorm_semantics _ _ h01 h02 h12,
    integerD2CorrectionNorm_semantics _ _ hv01 hv12] at hid
  simpa only [d2WordSize_eq, List.length_map, integerD2Delta, Int.cast_sub,
    Int.cast_mul, Int.cast_add, Int.cast_natCast] using hid

theorem integerD2Certificate_negative (L : List IntegerOrbit) (h : IntegerD2Certificate L) :
    qPermanentDerivative
      (d2Word (L.map integerOrbitReal) * (d2Word (L.map integerOrbitReal)).transpose) 1 < 0 := by
  have hid := integerD2_endpoint_value L h.1
  have hneg : (integerD2Delta L : ℝ) < 0 := by exact_mod_cast h.2
  linarith

theorem integerD2Certificate_rational_counterexample (L : List IntegerOrbit)
    (h : IntegerD2Certificate L) :
    ∃ B : Matrix (Fin (4 * L.length)) (Fin (4 * L.length)) ℚ,
      (rationalMatrixCast B).PosDef ∧ ∃ q₁ q₂ : ℚ,
      0 < q₁ ∧ q₁ < q₂ ∧ q₂ < 1 ∧
      qPermanent (rationalMatrixCast B) (q₂ : ℝ) <
        qPermanent (rationalMatrixCast B) (q₁ : ℝ) := by
  have ht := gram_endpoint_to_rational_posDef_interior
    (d2Word (L.map integerOrbitReal)) (integerD2Certificate_negative L h)
  have hn : d2WordSize (L.map integerOrbitReal) = 4 * L.length := by
    rw [d2WordSize_eq, List.length_map]
  rw [← hn]
  exact ht

theorem integerD2ThreeCertificate_negative (L : List IntegerOrbit)
    (h : IntegerD2ThreeCertificate L) :
    qPermanentDerivative
      (d2Word (L.map integerOrbitReal) * (d2Word (L.map integerOrbitReal)).transpose) 1 < 0 := by
  rcases h with ⟨⟨hF, h01, h02, h12⟩, hneg⟩
  have hrep := d2Recurrence_represents (L.map integerOrbitReal)
  rw [← integerD2Recurrence_semantics] at hrep
  apply d2_negative_of_three_certificate _ _ hrep
  rw [integerD2ProductNorm_semantics _ _ hF,
    integerD2ThreeNorm_semantics _ _ h01 h02 h12, d2WordSize_eq, List.length_map]
  have hc : (((4 * L.length).choose 2 : ℤ) *
      integerD2ProductNorm (4 * L.length) (integerD2Recurrence L)) <
      integerD2ThreeNorm (4 * L.length - 2) (integerD2Recurrence L) := sub_neg.mp hneg
  exact_mod_cast hc

theorem integerD2ThreeCertificate_rational_counterexample (L : List IntegerOrbit)
    (h : IntegerD2ThreeCertificate L) :
    ∃ B : Matrix (Fin (4 * L.length)) (Fin (4 * L.length)) ℚ,
      (rationalMatrixCast B).PosDef ∧ ∃ q₁ q₂ : ℚ,
      0 < q₁ ∧ q₁ < q₂ ∧ q₂ < 1 ∧
      qPermanent (rationalMatrixCast B) (q₂ : ℝ) <
        qPermanent (rationalMatrixCast B) (q₁ : ℝ) := by
  have ht := gram_endpoint_to_rational_posDef_interior
    (d2Word (L.map integerOrbitReal)) (integerD2ThreeCertificate_negative L h)
  have hn : d2WordSize (L.map integerOrbitReal) = 4 * L.length := by
    rw [d2WordSize_eq, List.length_map]
  rw [← hn]
  exact ht

#print axioms integerD2_endpoint_value
#print axioms integerD2Certificate_negative
#print axioms integerD2Certificate_rational_counterexample
#print axioms integerD2ThreeCertificate_negative
#print axioms integerD2ThreeCertificate_rational_counterexample

end QPermanentResearch
