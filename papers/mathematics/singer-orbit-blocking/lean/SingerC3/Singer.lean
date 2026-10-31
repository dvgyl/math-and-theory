import SingerC3.Model

/-!
# The Singer cycle on concrete triples

`nextN` is multiplication by `θ` on coefficient triples modulo 13, so `singer (pt u) = pt (nextN u)`.
The Singer cycle has order 183 and `hgen = singer^[61]` has no fixed point.
-/

namespace SingerC3

open Projectivization

/-- Multiplication by `θ`: `θ (a + bθ + cθ²) = -6c + (a - c)θ + bθ²`. -/
def nextN (u : Tri) : Tri := (7 * u.2.2 % 13, (u.1 + 12 * u.2.2) % 13, u.2.1 % 13)

theorem mulVec_vecOf (u : Tri) : singerMatrix.mulVec (vecOf u) = vecOf (nextN u) := by
  ext i
  fin_cases i <;>
    simp [singerMatrix, vecOf, nextN, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      ZMod.natCast_mod]

theorem nz_of_vecOf_ne_zero {u : Tri} (h : vecOf u ≠ 0) : nz u = true := by
  by_contra hc
  apply h
  simp only [nz, Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hc
  ext i; fin_cases i <;>
    simp [vecOf, ← ZMod.natCast_mod _ 13, hc.1.1, hc.1.2, hc.2] <;> rfl

theorem nz_nextN {u : Tri} (h : nz u = true) : nz (nextN u) = true := by
  apply nz_of_vecOf_ne_zero
  rw [← mulVec_vecOf]
  intro h0
  apply vecOf_ne_zero h
  apply singerMatrix_injective
  simpa [Matrix.mulVecLin_apply] using h0

theorem singer_pt {u : Tri} (h : nz u = true) : singer (pt u) = pt (nextN u) := by
  rw [pt_eq h, pt_eq (nz_nextN h), singer, map_mk]
  congr 1
  simp [mulVec_vecOf]

theorem nz_iterate_nextN {u : Tri} (h : nz u = true) (n : ℕ) : nz (nextN^[n] u) = true := by
  induction n with
  | zero => exact h
  | succ n ih => rw [Function.iterate_succ_apply']; exact nz_nextN ih

theorem singer_iterate_pt {u : Tri} (h : nz u = true) (n : ℕ) :
    singer^[n] (pt u) = pt (nextN^[n] u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
      singer_pt (nz_iterate_nextN h n)]

/-- `hgen` on a triple, normalized. -/
def hN (u : Tri) : Tri := normN (nextN^[61] u)

theorem hgen_pt {u : Tri} (h : nz u = true) : hgen (pt u) = pt (hN u) := by
  rw [hgen, singer_iterate_pt h, hN, pt_normN (nz_iterate_nextN h 61)]

/-- `p w` for every normalized triple `w`. -/
def allNorm (p : Tri → Bool) : Bool :=
  (all13 fun x => all13 fun y => p (1, x, y)) && (all13 fun x => p (0, 1, x)) && p (0, 0, 1)

theorem allNorm_spec {p : Tri → Bool} (h : allNorm p = true) : ∀ w, IsNorm w → p w = true := by
  intro w hw
  simp only [allNorm, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨a, b, c⟩ := w
  rcases (isNorm_iff _).1 hw with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · simp only at e1 e2 e3; subst e1; exact all13_spec (all13_spec h1 b e2) c e3
  · simp only at e1 e2 e3; subst e1 e2; exact all13_spec h2 c e3
  · simp only at e1 e2 e3; subst e1 e2 e3; exact h3

/-- `p` holds at some normalized triple. -/
def anyNorm (p : Tri → Bool) : Bool :=
  ((List.range 13).any fun x => (List.range 13).any fun y => p (1, x, y)) ||
    ((List.range 13).any fun x => p (0, 1, x)) || p (0, 0, 1)

theorem anyNorm_spec {p : Tri → Bool} (h : anyNorm p = true) : ∃ w, IsNorm w ∧ p w = true := by
  simp only [anyNorm, Bool.or_eq_true, List.any_eq_true, List.mem_range] at h
  rcases h with (⟨x, hx, y, hy, h⟩ | ⟨x, hx, h⟩) | h
  · exact ⟨(1, x, y), (isNorm_iff _).2 (Or.inl ⟨rfl, hx, hy⟩), h⟩
  · exact ⟨(0, 1, x), (isNorm_iff _).2 (Or.inr (Or.inl ⟨rfl, rfl, hx⟩)), h⟩
  · exact ⟨(0, 0, 1), (isNorm_iff _).2 (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)), h⟩

/-- Finite check: `hgen` moves every point. -/
def hFreeB : Bool := allNorm fun w => !(hN w == w)

theorem hFreeB_eq : hFreeB = true := by decide +kernel

/-- The subgroup of order three has no fixed point. -/
theorem hgen_no_fixed_point (P : Point) : hgen P ≠ P := by
  obtain ⟨w, hw, hnz, rfl⟩ := exists_norm P
  rw [hgen_pt hnz]
  intro h
  have hn : IsNorm (hN w) := (normN_spec (nz_iterate_nextN hnz 61)).2.2
  have := pt_injective hn hw h
  have hc := allNorm_spec hFreeB_eq w hw
  simp [this] at hc

/-- Finite check: `singer^[183]` fixes every normalized triple. -/
def periodB : Bool := allNorm fun w => normN (nextN^[183] w) == w

theorem periodB_eq : periodB = true := by decide +kernel

theorem singer_iterate_183 : singer^[183] = id := by
  funext P
  obtain ⟨w, hw, hnz, rfl⟩ := exists_norm P
  rw [singer_iterate_pt hnz, ← pt_normN (nz_iterate_nextN hnz 183)]
  have := allNorm_spec periodB_eq w hw
  simp only [beq_iff_eq] at this
  rw [this]; rfl

/-- Finite check: the point `[1:0:0]` is moved by `singer^[k]` for `0 < k < 183`. -/
def orbitB : Bool := (List.range 182).all fun k => !(normN (nextN^[k + 1] (1, 0, 0)) == (1, 0, 0))

theorem orbitB_eq : orbitB = true := by decide +kernel

/-- The Singer cycle has order exactly 183. -/
theorem singer_iterate_ne (k : ℕ) (hk0 : 0 < k) (hk : k < 183) : singer^[k] ≠ id := by
  intro h
  have h1 := congrFun h (pt (1, 0, 0))
  have hnz : nz ((1, 0, 0) : Tri) = true := by decide
  rw [singer_iterate_pt hnz, ← pt_normN (nz_iterate_nextN hnz k)] at h1
  have hn : IsNorm (normN (nextN^[k] (1, 0, 0))) := (normN_spec (nz_iterate_nextN hnz k)).2.2
  have e := pt_injective hn (by decide) h1
  have hc := orbitB_eq
  simp only [orbitB, List.all_eq_true, List.mem_range] at hc
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have := hc j (by omega)
  rw [e] at this
  simp at this

theorem hgen_iterate_three : hgen^[3] = id := by
  rw [hgen, ← Function.iterate_mul]
  exact singer_iterate_183

end SingerC3
