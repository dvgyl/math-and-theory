import QPermanentResearch.IdentityPadding
import QPermanentResearch.RowMinorRank
import QPermanentResearch.IntegerCertificate

/-!
The frozen 896-row witness: definitions, exact rank three, and the reductions
from its exact integer certificate.

The orbit list is the file `certificate/witness896_cap32_orbits.txt` read in
reverse, because `d2Word` wraps the head of the list outermost, whereas the file
lists the wrapping operations from inner to outer.
Frozen orbit file SHA-256:
7220026a9fb5b2d9e62ef46b9b7196b2ff768b4841f71ccb45275ee445987751

Trust boundary. Nothing in this module evaluates the 896-row certificate.
The concrete inequality `IntegerD2ThreeCertificate orbits`, equivalently the
Fischer-norm inequality for `rows`, appears only as an explicit hypothesis.
It is checked outside Lean by the exact integer programs in `certificate/`.
The rank statements are proved outright, from a determinant-480 minor of the
outermost orbit, without expanding the 224 nested row constructors.
-/

namespace QPermanentResearch.Witness896

set_option maxRecDepth 100000

def orbits : List IntegerOrbit := [
  (3,2,20),
  (3,2,19),
  (5,0,22),
  (6,0,25),
  (4,0,15),
  (9,0,31),
  (3,0,10),
  (5,6,29),
  (5,6,28),
  (4,7,31),
  (3,6,25),
  (11,0,28),
  (5,0,12),
  (11,0,26),
  (4,0,9),
  (14,0,31),
  (9,0,19),
  (12,0,25),
  (1,0,2),
  (10,0,19),
  (8,0,15),
  (5,0,9),
  (9,0,16),
  (17,0,29),
  (13,0,22),
  (8,0,13),
  (16,0,25),
  (9,0,14),
  (7,9,23),
  (3,4,10),
  (12,11,27),
  (13,12,29),
  (5,10,24),
  (3,10,29),
  (3,10,29),
  (12,1,15),
  (12,1,15),
  (19,2,23),
  (19,2,23),
  (18,1,21),
  (15,1,17),
  (15,1,17),
  (28,1,30),
  (29,1,31),
  (30,1,31),
  (31,1,32),
  (9,9,17),
  (21,16,31),
  (20,15,29),
  (7,13,24),
  (9,17,31),
  (7,10,17),
  (13,19,31),
  (17,12,21),
  (16,16,25),
  (9,9,14),
  (16,7,15),
  (16,7,15),
  (8,3,7),
  (8,3,7),
  (22,17,25),
  (11,6,10),
  (11,6,10),
  (18,2,13),
  (18,2,13),
  (13,1,9),
  (13,1,9),
  (6,17,30),
  (3,14,31),
  (1,5,11),
  (12,18,23),
  (15,23,29),
  (17,20,24),
  (17,20,24),
  (23,22,26),
  (23,18,21),
  (32,25,29),
  (27,9,17),
  (24,8,15),
  (16,3,9),
  (16,3,9),
  (12,25,30),
  (9,22,30),
  (8,20,27),
  (25,13,16),
  (27,14,17),
  (25,10,14),
  (25,10,14),
  (31,19,20),
  (17,13,12),
  (17,13,12),
  (9,12,11),
  (9,12,11),
  (24,25,22),
  (24,25,22),
  (13,28,28),
  (15,26,24),
  (15,26,24),
  (31,3,13),
  (31,3,13),
  (20,1,8),
  (20,1,8),
  (21,19,14),
  (25,29,21),
  (28,32,23),
  (10,3,4),
  (10,3,4),
  (30,6,11),
  (30,6,11),
  (5,21,29),
  (1,7,12),
  (1,7,12),
  (29,15,12),
  (27,14,11),
  (31,12,11),
  (31,12,11),
  (4,3,2),
  (32,20,13),
  (32,20,13),
  (14,30,23),
  (14,30,23),
  (20,32,21),
  (20,32,21),
  (10,29,27),
  (6,23,25),
  (6,23,25),
  (28,24,13),
  (28,24,13),
  (20,21,11),
  (20,21,11),
  (19,24,12),
  (19,28,14),
  (4,6,3),
  (24,1,5),
  (24,1,5),
  (14,2,3),
  (14,2,3),
  (4,12,9),
  (16,31,16),
  (16,31,16),
  (29,7,6),
  (29,7,6),
  (19,7,4),
  (19,7,4),
  (19,9,4),
  (26,15,6),
  (26,15,6),
  (8,21,12),
  (8,21,12),
  (6,25,20),
  (6,25,20),
  (16,11,4),
  (31,26,9),
  (25,21,7),
  (17,21,7),
  (17,21,7),
  (30,31,9),
  (30,31,9),
  (10,17,6),
  (5,11,4),
  (5,11,4),
  (6,19,8),
  (6,19,8),
  (7,29,16),
  (7,29,16),
  (23,31,8),
  (9,15,4),
  (9,15,4),
  (3,27,22),
  (3,27,22),
  (4,27,17),
  (4,27,17),
  (13,29,7),
  (7,21,6),
  (7,21,6),
  (2,24,31),
  (2,24,31),
  (1,11,11),
  (2,23,23),
  (29,1,1),
  (28,3,2),
  (18,2,1),
  (31,7,2),
  (31,7,2),
  (14,5,1),
  (14,5,1),
  (6,29,10),
  (3,23,10),
  (3,23,10),
  (32,22,3),
  (32,22,3),
  (19,16,2),
  (30,25,3),
  (20,9,1),
  (29,16,2),
  (29,16,2),
  (18,28,3),
  (18,28,3),
  (15,28,3),
  (15,28,3),
  (12,31,5),
  (11,25,2),
  (11,25,2),
  (31,32,3),
  (31,32,3),
  (19,24,2),
  (19,24,2),
  (1,30,20),
  (1,23,11),
  (1,23,11),
  (0,1,0),
  (0,1,0),
  (0,1,0),
  (0,1,0),
  (0,1,0),
  (0,1,0),
  (0,1,0),
  (0,1,0),
  (0,1,0),
  (0,1,0),
  (0,1,0),
  (0,1,0),
  (0,1,0),
  (0,1,0)
]

theorem orbit_count : orbits.length = 224 := by decide

/-- The ordered 896 by 3 row matrix of the witness. -/
noncomputable def rows := d2Word (orbits.map integerOrbitReal)

/-- The Gram matrix `B = V Vᵀ` of the witness. -/
noncomputable def gram := rows * rows.transpose

theorem row_count : d2WordSize (orbits.map integerOrbitReal) = 896 := by
  rw [d2WordSize_eq, List.length_map, orbit_count]

theorem gram_posSemidef : gram.PosSemidef := by
  simpa only [gram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose rows

private theorem inner_word_size :
    d2WordSize (orbits.tail.map integerOrbitReal) = 892 := by
  rw [d2WordSize_eq, List.length_map, List.length_tail, orbit_count]

/-- The three actual rows selected by the generic outer-orbit minor. -/
def rankMinorRows : Fin 3 → Fin (d2WordSize (orbits.map integerOrbitReal)) :=
  d2OuterMinorRows (d2WordSize (orbits.tail.map integerOrbitReal))

noncomputable def rankMinor : Matrix (Fin 3) (Fin 3) ℝ :=
  rows.submatrix rankMinorRows id

theorem rankMinor_row_positions :
    (fun i => (rankMinorRows i).val) = ![0, 1, 894] := by
  change (fun i => (d2OuterMinorRows (d2WordSize (orbits.tail.map integerOrbitReal)) i).val) = _
  rw [d2OuterMinorRows_values, inner_word_size]

theorem rankMinor_entries :
    rankMinor = !![-3, 2, 20; -3, -2, 20; 3, 2, 20] := by
  change ((d2Wrap (d2Word (orbits.tail.map integerOrbitReal)) 3 2 20).submatrix
    (d2OuterMinorRows (d2WordSize (orbits.tail.map integerOrbitReal))) id) = _
  exact d2Wrap_outer_minor _ 3 2 20

theorem rankMinor_det : rankMinor.det = 480 := by
  change ((d2Wrap (d2Word (orbits.tail.map integerOrbitReal)) 3 2 20).submatrix
    (d2OuterMinorRows (d2WordSize (orbits.tail.map integerOrbitReal))) id).det = 480
  rw [d2Wrap_outer_minor_det]
  norm_num

theorem rows_rank_three : rows.rank = 3 := by
  apply matrix_rank_eq_width_of_nonsingular_row_minor rows rankMinorRows
  change rankMinor.det ≠ 0
  rw [rankMinor_det]
  norm_num

theorem gram_rank_three : gram.rank = 3 := by
  rw [gram, Matrix.rank_self_mul_transpose, rows_rank_three]

/-- The Fischer-norm form of the certificate gives the negative endpoint. -/
theorem gram_endpoint_negative_of_fischer
    (h : ((d2WordSize (orbits.map integerOrbitReal)).choose 2 : ℝ) *
      productFischerNorm rows < wedgeFischerNorm rows) :
    qPermanentDerivative gram 1 < 0 :=
  (endpointDerivative_neg_iff_fischer rows).mpr h

/-- The integer three-component certificate gives the negative endpoint. -/
theorem gram_endpoint_negative_of_certificate
    (h : IntegerD2ThreeCertificate orbits) :
    qPermanentDerivative gram 1 < 0 :=
  integerD2ThreeCertificate_negative orbits h

/-- From the negative endpoint: a rational positive-definite matrix of order 896
and rational `0 < q₁ < q₂ < 1` with `P_{q₂} < P_{q₁}`. -/
theorem rational_counterexample_of_endpoint
    (h : qPermanentDerivative gram 1 < 0) :
    ∃ B : Matrix (Fin 896) (Fin 896) ℚ, (rationalMatrixCast B).PosDef ∧
      ∃ q₁ q₂ : ℚ, 0 < q₁ ∧ q₁ < q₂ ∧ q₂ < 1 ∧
      qPermanent (rationalMatrixCast B) (q₂ : ℝ) <
        qPermanent (rationalMatrixCast B) (q₁ : ℝ) := by
  have ht := gram_endpoint_to_rational_posDef_interior rows h
  rw [row_count] at ht
  exact ht

/-- One rational pair works in every dimension `N ≥ 896`, by identity padding. -/
theorem all_large_dimensions_of_endpoint
    (h : qPermanentDerivative gram 1 < 0) :
    ∃ q₁ q₂ : ℚ, 0 < q₁ ∧ q₁ < q₂ ∧ q₂ < 1 ∧
      ∀ N : ℕ, 896 ≤ N →
        ∃ B : Matrix (Fin N) (Fin N) ℚ,
          (rationalMatrixCast B).PosDef ∧
          qPermanent (rationalMatrixCast B) (q₂ : ℝ) <
            qPermanent (rationalMatrixCast B) (q₁ : ℝ) := by
  obtain ⟨A, hA, q₁, q₂, h₁, h₁₂, h₂, hdec⟩ := rational_counterexample_of_endpoint h
  refine ⟨q₁, q₂, h₁, h₁₂, h₂, ?_⟩
  intro N hN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  exact ⟨identityPadding A k,
    rational_posDef_decrease_identityPadding A hA q₁ q₂ hdec k⟩

/-- The all-dimensions conclusion from the Fischer-norm certificate. -/
theorem all_large_dimensions_of_fischer
    (h : ((d2WordSize (orbits.map integerOrbitReal)).choose 2 : ℝ) *
      productFischerNorm rows < wedgeFischerNorm rows) :
    ∃ q₁ q₂ : ℚ, 0 < q₁ ∧ q₁ < q₂ ∧ q₂ < 1 ∧
      ∀ N : ℕ, 896 ≤ N →
        ∃ B : Matrix (Fin N) (Fin N) ℚ,
          (rationalMatrixCast B).PosDef ∧
          qPermanent (rationalMatrixCast B) (q₂ : ℝ) <
            qPermanent (rationalMatrixCast B) (q₁ : ℝ) :=
  all_large_dimensions_of_endpoint (gram_endpoint_negative_of_fischer h)

/-- The all-dimensions conclusion from the integer certificate. -/
theorem all_large_dimensions_of_certificate
    (h : IntegerD2ThreeCertificate orbits) :
    ∃ q₁ q₂ : ℚ, 0 < q₁ ∧ q₁ < q₂ ∧ q₂ < 1 ∧
      ∀ N : ℕ, 896 ≤ N →
        ∃ B : Matrix (Fin N) (Fin N) ℚ,
          (rationalMatrixCast B).PosDef ∧
          qPermanent (rationalMatrixCast B) (q₂ : ℝ) <
            qPermanent (rationalMatrixCast B) (q₁ : ℝ) :=
  all_large_dimensions_of_endpoint (gram_endpoint_negative_of_certificate h)

end QPermanentResearch.Witness896
