import SingerC3.Statement

/-!
# A concrete model of PG(2,13)

Triples of natural numbers stand for coordinate vectors, read modulo 13. All finite checks are
done on natural numbers by `decide` and transferred to `ZMod 13` by the lemmas below.
-/

namespace SingerC3

open Projectivization

/-- A coordinate triple of natural numbers, read modulo 13. -/
abbrev Tri := ℕ × ℕ × ℕ

/-- The coordinate vector of a triple. -/
def vecOf (u : Tri) : V := ![(u.1 : F), (u.2.1 : F), (u.2.2 : F)]

/-- The dot product modulo 13. -/
def dotN (u w : Tri) : ℕ := (u.1 * w.1 + u.2.1 * w.2.1 + u.2.2 * w.2.2) % 13

/-- A triple that is not zero modulo 13. -/
def nz (u : Tri) : Bool := u.1 % 13 != 0 || u.2.1 % 13 != 0 || u.2.2 % 13 != 0

/-- Normalized triples: the first nonzero coordinate is `1` and all coordinates are below 13. -/
def isNormB (u : Tri) : Bool :=
  (u.1 == 1 && decide (u.2.1 < 13) && decide (u.2.2 < 13)) ||
  (u.1 == 0 && u.2.1 == 1 && decide (u.2.2 < 13)) || (u.1 == 0 && u.2.1 == 0 && u.2.2 == 1)

/-- Normalized triples as a proposition. -/
def IsNorm (u : Tri) : Prop := isNormB u = true

instance (u : Tri) : Decidable (IsNorm u) := inferInstanceAs (Decidable (isNormB u = true))

theorem isNorm_iff (u : Tri) : IsNorm u ↔
    (u.1 = 1 ∧ u.2.1 < 13 ∧ u.2.2 < 13) ∨ (u.1 = 0 ∧ u.2.1 = 1 ∧ u.2.2 < 13) ∨
      (u.1 = 0 ∧ u.2.1 = 0 ∧ u.2.2 = 1) := by
  simp [IsNorm, isNormB, and_assoc, or_assoc]

/-- `p a` for every `a < 13`. -/
def all13 (p : ℕ → Bool) : Bool := (List.range 13).all p

theorem all13_spec {p : ℕ → Bool} (h : all13 p = true) : ∀ a < 13, p a = true := by
  intro a ha
  simp only [all13, List.all_eq_true, List.mem_range] at h
  exact h a ha

theorem vecOf_dotProduct (u w : Tri) :
    vecOf u ⬝ᵥ vecOf w = ((u.1 * w.1 + u.2.1 * w.2.1 + u.2.2 * w.2.2 : ℕ) : F) := by
  simp [vecOf, dotProduct, Fin.sum_univ_three]

theorem vecOf_dotProduct_eq_zero (u w : Tri) : vecOf u ⬝ᵥ vecOf w = 0 ↔ dotN u w = 0 := by
  rw [vecOf_dotProduct, ZMod.natCast_eq_zero_iff, dotN, Nat.dvd_iff_mod_eq_zero]

theorem vecOf_ne_zero {u : Tri} (h : nz u = true) : vecOf u ≠ 0 := by
  intro h0
  have h1 := congrFun h0 0
  have h2 := congrFun h0 1
  have h3 := congrFun h0 2
  simp only [vecOf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Pi.zero_apply, Matrix.head_cons, Matrix.tail_cons, ZMod.natCast_eq_zero_iff,
    Nat.dvd_iff_mod_eq_zero] at h1 h2 h3
  simp [nz, h1, h2, h3] at h

/-- The point of a triple; the junk value `[1:0:0]` is used for a zero triple. -/
def pt (u : Tri) : Point :=
  if h : nz u = true then mk F (vecOf u) (vecOf_ne_zero h)
  else mk F (vecOf (1, 0, 0)) (vecOf_ne_zero (by decide))

theorem pt_eq {u : Tri} (h : nz u = true) : pt u = mk F (vecOf u) (vecOf_ne_zero h) := by
  simp [pt, h]

theorem pt_orthogonal {u w : Tri} (hu : nz u = true) (hw : nz w = true) :
    (pt u).orthogonal (pt w) ↔ dotN u w = 0 := by
  rw [pt_eq hu, pt_eq hw, orthogonal_mk, vecOf_dotProduct_eq_zero]

theorem mem_lineSet_pt {u w : Tri} (hu : nz u = true) (hw : nz w = true) :
    pt w ∈ lineSet (pt u) ↔ dotN u w = 0 :=
  pt_orthogonal hu hw

/-! ### Scaling and normalization -/

/-- Inverses modulo 13. -/
def inv13 (a : ℕ) : ℕ := a ^ 11 % 13

/-- Normalization: divide by the first nonzero coordinate. -/
def normN (u : Tri) : Tri :=
  let a := u.1 % 13
  let b := u.2.1 % 13
  let c := u.2.2 % 13
  if a ≠ 0 then (1, b * inv13 a % 13, c * inv13 a % 13)
  else if b ≠ 0 then (0, 1, c * inv13 b % 13)
  else (0, 0, 1)

/-- The first nonzero coordinate. -/
def leadN (u : Tri) : ℕ :=
  if u.1 % 13 ≠ 0 then u.1 % 13 else if u.2.1 % 13 ≠ 0 then u.2.1 % 13 else u.2.2 % 13

/-- Reduction of a triple modulo 13. -/
def red (u : Tri) : Tri := (u.1 % 13, u.2.1 % 13, u.2.2 % 13)

theorem vecOf_red (u : Tri) : vecOf (red u) = vecOf u := by
  ext i; fin_cases i <;> simp [vecOf, red]

theorem vecOf_eq_smul {u w : Tri} (k : ℕ) (h1 : u.1 % 13 = k * w.1 % 13)
    (h2 : u.2.1 % 13 = k * w.2.1 % 13) (h3 : u.2.2 % 13 = k * w.2.2 % 13) :
    vecOf u = (k : F) • vecOf w := by
  have e : ∀ x y : ℕ, x % 13 = y % 13 → (x : F) = (y : F) := fun x y h => by
    rw [← ZMod.natCast_mod, h, ZMod.natCast_mod]
  ext i; fin_cases i
  · simpa [vecOf] using e _ _ h1
  · simpa [vecOf] using e _ _ h2
  · simpa [vecOf] using e _ _ h3

/-- Finite check of the normalization identities. -/
def normCheckB : Bool :=
  all13 fun a => all13 fun b => all13 fun c =>
    !(nz (a, b, c)) ||
      (a % 13 == leadN (a, b, c) * (normN (a, b, c)).1 % 13 &&
       b % 13 == leadN (a, b, c) * (normN (a, b, c)).2.1 % 13 &&
       c % 13 == leadN (a, b, c) * (normN (a, b, c)).2.2 % 13 &&
       nz (normN (a, b, c)) && isNormB (normN (a, b, c)))

theorem normCheckB_eq : normCheckB = true := by decide +kernel

theorem norm_check (u : Tri) (ha : u.1 < 13) (hb : u.2.1 < 13) (hc : u.2.2 < 13)
    (hn : nz u = true) :
    u.1 % 13 = leadN u * (normN u).1 % 13 ∧
    u.2.1 % 13 = leadN u * (normN u).2.1 % 13 ∧
    u.2.2 % 13 = leadN u * (normN u).2.2 % 13 ∧
    nz (normN u) = true ∧ IsNorm (normN u) := by
  obtain ⟨a, b, c⟩ := u
  simp only at ha hb hc
  have h := all13_spec (all13_spec (all13_spec normCheckB_eq a ha) b hb) c hc
  simp only [hn, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem red_lt (u : Tri) : (red u).1 < 13 ∧ (red u).2.1 < 13 ∧ (red u).2.2 < 13 :=
  ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

theorem normN_red (u : Tri) : normN (red u) = normN u := by
  simp [normN, red]

theorem leadN_red (u : Tri) : leadN (red u) = leadN u := by
  simp [leadN, red]

theorem nz_red (u : Tri) : nz (red u) = nz u := by
  simp [nz, red]

theorem normN_spec {u : Tri} (h : nz u = true) :
    vecOf u = (leadN u : F) • vecOf (normN u) ∧ nz (normN u) = true ∧ IsNorm (normN u) := by
  obtain ⟨h1, h2, h3⟩ := red_lt u
  have hr : nz (red u) = true := by rwa [nz_red]
  obtain ⟨e1, e2, e3, e4, e5⟩ := norm_check _ h1 h2 h3 hr
  simp only [normN_red, leadN_red] at e1 e2 e3 e4 e5
  refine ⟨?_, e4, e5⟩
  rw [← vecOf_red]
  exact vecOf_eq_smul _ e1 e2 e3

theorem pt_normN {u : Tri} (h : nz u = true) : pt (normN u) = pt u := by
  obtain ⟨hs, hn, -⟩ := normN_spec h
  rw [pt_eq h, pt_eq hn, mk_eq_mk_iff']
  refine ⟨((leadN u : ℕ) : F)⁻¹, ?_⟩
  rw [hs, smul_smul]
  have hl : ((leadN u : ℕ) : F) ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hs
    exact vecOf_ne_zero h hs
  rw [inv_mul_cancel₀ hl, one_smul]

/-- Every point is the point of a normalized triple. -/
theorem exists_norm (P : Point) : ∃ u, IsNorm u ∧ nz u = true ∧ P = pt u := by
  induction P using Projectivization.ind with
  | h v hv =>
    let u : Tri := ((v 0).val, (v 1).val, (v 2).val)
    have hvu : vecOf u = v := by
      ext i; fin_cases i <;> simp [u, vecOf]
    have hu : nz u = true := by
      by_contra hc
      apply hv
      have h0 : ∀ x : F, x.val % 13 = 0 → x = 0 := fun x hx => by
        rw [Nat.mod_eq_of_lt (ZMod.val_lt x)] at hx
        exact (ZMod.val_eq_zero x).1 hx
      simp only [nz, u, Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hc
      ext i; fin_cases i
      · exact h0 _ hc.1.1
      · exact h0 _ hc.1.2
      · exact h0 _ hc.2
    obtain ⟨-, hn, hN⟩ := normN_spec hu
    refine ⟨normN u, hN, hn, ?_⟩
    rw [pt_normN hu, pt_eq hu]
    congr 1
    exact hvu.symm

theorem isNorm_nz {u : Tri} (h : IsNorm u) : nz u = true := by
  rcases (isNorm_iff u).1 h with ⟨h1, -, -⟩ | ⟨h1, h2, -⟩ | h
  · simp [nz, h1]
  · simp [nz, h1, h2]
  · obtain ⟨a, b, c⟩ := u
    simp only at h
    obtain ⟨h1, h2, h3⟩ := h
    subst h1 h2 h3; decide

theorem isNorm_red {u : Tri} (h : IsNorm u) : red u = u := by
  rcases (isNorm_iff u).1 h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | h
  · obtain ⟨a, b, c⟩ := u
    simp only at h1 h2 h3
    simp [red, h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]
  · obtain ⟨a, b, c⟩ := u
    simp only at h1 h2 h3
    simp [red, h1, h2, Nat.mod_eq_of_lt h3]
  · obtain ⟨a, b, c⟩ := u
    simp only at h
    obtain ⟨h1, h2, h3⟩ := h
    subst h1 h2 h3; decide

/-- Finite check: normalization is invariant under nonzero scaling. -/
def scaleCheckB : Bool :=
  all13 fun k => all13 fun a => all13 fun b => all13 fun c =>
    k == 0 || !(nz (a, b, c)) ||
      normN (k * a % 13, k * b % 13, k * c % 13) == normN (a, b, c)

theorem scaleCheckB_eq : scaleCheckB = true := by decide +kernel

theorem scale_check : ∀ k < 13, k ≠ 0 → ∀ a < 13, ∀ b < 13, ∀ c < 13, nz (a, b, c) = true →
    normN (k * a % 13, k * b % 13, k * c % 13) = normN (a, b, c) := by
  intro k hk hk0 a ha b hb c hc hn
  have h := all13_spec (all13_spec (all13_spec (all13_spec scaleCheckB_eq k hk) a ha) b hb) c hc
  simpa [hk0, hn] using h

/-- Finite check: normalized triples are fixed by normalization. -/
def normFixB : Bool :=
  all13 fun a => all13 fun b => all13 fun c => !(isNormB (a, b, c)) || normN (a, b, c) == (a, b, c)

theorem normFixB_eq : normFixB = true := by decide +kernel

theorem normN_of_isNorm {u : Tri} (h : IsNorm u) : normN u = u := by
  have hlt : u.1 < 13 ∧ u.2.1 < 13 ∧ u.2.2 < 13 := by
    rw [← isNorm_red h]; exact red_lt u
  obtain ⟨a, b, c⟩ := u
  obtain ⟨h1, h2, h3⟩ := hlt
  have e := all13_spec (all13_spec (all13_spec normFixB_eq a h1) b h2) c h3
  have h' : isNormB (a, b, c) = true := h
  simpa [h'] using e

/-- Distinct normalized triples give distinct points. -/
theorem pt_injective {u w : Tri} (hu : IsNorm u) (hw : IsNorm w) (h : pt u = pt w) : u = w := by
  rw [pt_eq (isNorm_nz hu), pt_eq (isNorm_nz hw), mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  -- `a • vecOf w = vecOf u`, read coordinatewise in ℕ.
  have hlt : ∀ {x : Tri}, IsNorm x → x.1 < 13 ∧ x.2.1 < 13 ∧ x.2.2 < 13 := fun hx => by
    rw [← isNorm_red hx]; exact red_lt _
  obtain ⟨wa, wb, wc⟩ := hlt hw
  obtain ⟨ua, ub, uc⟩ := hlt hu
  set k := (a : F).val with hk
  have hk13 : k < 13 := ZMod.val_lt _
  have hk0 : k ≠ 0 := by
    rw [hk, ZMod.val_ne_zero]; exact a.ne_zero
  have coord : ∀ i : Fin 3, (a : F) * vecOf w i = vecOf u i := fun i => by
    have := congrFun ha i
    simpa [Units.smul_def] using this
  have e : ∀ (x y : ℕ), x < 13 → y < 13 → (a : F) * (x : F) = (y : F) → k * x % 13 = y := by
    intro x y hx hy hxy
    have h1 : ((k * x : ℕ) : F) = (y : F) := by
      rw [Nat.cast_mul, hk, ZMod.natCast_zmod_val]; exact hxy
    have h2 := congrArg ZMod.val h1
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hy] at h2
  have c1 := e _ _ wa ua (by simpa [vecOf] using coord 0)
  have c2 := e _ _ wb ub (by simpa [vecOf] using coord 1)
  have c3 := e _ _ wc uc (by simpa [vecOf] using coord 2)
  have hs := scale_check k hk13 hk0 _ wa _ wb _ wc (isNorm_nz hw)
  rw [c1, c2, c3] at hs
  rw [← normN_of_isNorm hu, ← normN_of_isNorm hw]
  obtain ⟨u1, u2, u3⟩ := u
  exact hs

end SingerC3
