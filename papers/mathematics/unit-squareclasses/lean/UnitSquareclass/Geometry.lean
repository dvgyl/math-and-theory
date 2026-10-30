import Mathlib

/-!
# Finite reflection shells over an ordered field

This is the geometric intermediate theorem used in the unit-squareclass argument.
It does not assert arithmetic shell finiteness or identify lattice squareclasses.
The ambient field is any linearly ordered field; no scalar extension is used.
-/

namespace UnitSquareclass

open scoped BigOperators
open LinearMap (BilinForm)

variable {K V I : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V]

/-- Strict Cauchy inequality, with noncollinearity stated over the actual field. -/
theorem strict_cauchy (B : BilinForm K V) (hB : B.IsSymm)
    (hpos : ∀ z : V, z ≠ 0 → 0 < B z z)
    {x y : V} (hx : x ≠ 0) (hy : ∀ a : K, y ≠ a • x) :
    (B x y) ^ 2 < B x x * B y y := by
  have hxx : 0 < B x x := hpos x hx
  have hz : y - (B x y / B x x) • x ≠ 0 := by
    intro hz
    exact hy _ (sub_eq_zero.mp hz)
  have hq := hpos _ hz
  simp only [BilinForm.sub_left, BilinForm.sub_right,
    BilinForm.smul_left, BilinForm.smul_right, ← hB x y, RingHom.id_apply] at hq
  have hid :
      B x x *
        (B y y - (B x y / B x x) * B x y -
          (B x y / B x x) *
            (B x y - (B x y / B x x) * B x x)) =
        B x x * B y y - (B x y) ^ 2 := by
    field_simp
    ring
  have hp := mul_pos hxx hq
  rw [hid] at hp
  linarith

/-- A linear functional positive on all the vectors detects a nonnegative relation. -/
theorem coeff_eq_zero_of_nonneg_sum_eq_zero [Fintype I]
    (h : V →ₗ[K] K) (v : I → V) (hv : ∀ i, 0 < h (v i))
    (c : I → K) (hc : ∀ i, 0 ≤ c i)
    (hs : ∑ i, c i • v i = 0) : ∀ i, c i = 0 := by
  have hs' : ∑ i, c i * h (v i) = 0 := by
    simpa using congrArg h hs
  have ht := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => mul_nonneg (hc i) (hv i).le)).mp hs'
  intro i
  exact (mul_eq_zero.mp (ht i (Finset.mem_univ i))).resolve_right (ne_of_gt (hv i))

/-- Pairwise nonpositive vectors contained in a common open halfspace are independent. -/
theorem linearIndependent_of_pairwise_nonpos [Fintype I]
    (B : BilinForm K V) (hpos : ∀ z : V, z ≠ 0 → 0 < B z z)
    (h : V →ₗ[K] K) (v : I → V)
    (hv : ∀ i, 0 < h (v i))
    (hpair : ∀ i j, i ≠ j → B (v i) (v j) ≤ 0) :
    LinearIndependent K v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let a : I → K := fun i => max (c i) 0
  let b : I → K := fun i => max (-c i) 0
  have ha : ∀ i, 0 ≤ a i := fun i => le_max_right _ _
  have hb : ∀ i, 0 ≤ b i := fun i => le_max_right _ _
  have hab : ∀ i, a i - b i = c i := by
    intro i
    dsimp [a, b]
    rcases le_total 0 (c i) with hi | hi
    · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
      ring
    · rw [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi)]
      ring
  have habzero : ∀ i, a i * b i = 0 := by
    intro i
    dsimp [a, b]
    rcases le_total 0 (c i) with hi | hi
    · rw [max_eq_right (neg_nonpos.mpr hi), mul_zero]
    · rw [max_eq_right hi, zero_mul]
  let u : V := ∑ i, a i • v i
  let w : V := ∑ i, b i • v i
  have huw : u = w := by
    apply sub_eq_zero.mp
    dsimp [u, w]
    rw [← Finset.sum_sub_distrib]
    simpa only [← sub_smul, hab] using hc
  have hcross : B u w ≤ 0 := by
    dsimp [u, w]
    simp only [map_sum, LinearMap.sum_apply, BilinForm.smul_left,
      BilinForm.smul_right]
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    by_cases hij : j = i
    · subst j
      rw [← mul_assoc, mul_comm (b i) (a i), habzero, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (hb i)
        (mul_nonpos_of_nonneg_of_nonpos (ha j) (hpair j i hij))
  have hu : u = 0 := by
    apply Classical.byContradiction
    intro hzero
    have hpu := hpos u hzero
    rw [← huw] at hcross
    exact (not_lt_of_ge hcross) hpu
  have hw : w = 0 := huw ▸ hu
  have haz := coeff_eq_zero_of_nonneg_sum_eq_zero h v hv a ha hu
  have hbz := coeff_eq_zero_of_nonneg_sum_eq_zero h v hv b hb hw
  intro i
  have hi := hab i
  rw [haz i, hbz i] at hi
  simpa using hi.symm

/-- Reflection in the hyperplane perpendicular to `x`. -/
def reflect (B : BilinForm K V) (x y : V) : V :=
  y - (2 * B x y / B x x) • x

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem apply_reflect (B : BilinForm K V) (h : V →ₗ[K] K) (x y : V) :
    h (reflect B x y) = h y - (2 * B x y / B x x) * h x := by
  simp [reflect]

/-- The scalar inequality forced by an absolute minimum under reflection. -/
theorem two_mul_le_of_reflection_minimum {a x y : K}
    (ha : 0 < a) (hx : 0 < x) (hmin : y ≤ |y - a * x|) :
    2 * y ≤ a * x := by
  by_cases hz : 0 ≤ y - a * x
  · rw [abs_of_nonneg hz] at hmin
    have hp := mul_pos ha hx
    linarith
  · rw [abs_of_neg (lt_of_not_ge hz)] at hmin
    linarith

/-- Noncollinear vectors minimal in their reflection-stable shells have nonpositive pairing. -/
theorem pairing_nonpos_of_reflection_minima
    (B : BilinForm K V) (hB : B.IsSymm)
    (hpos : ∀ z : V, z ≠ 0 → 0 < B z z)
    (h : V →ₗ[K] K) {x y : V}
    (hx : 0 < h x) (hy : 0 < h y)
    (hxy : ∀ a : K, y ≠ a • x)
    (hxmin : h x ≤ |h (reflect B y x)|)
    (hymin : h y ≤ |h (reflect B x y)|) :
    B x y ≤ 0 := by
  by_contra! hxypos
  have hxne : x ≠ 0 := by
    intro hxzero
    simp [hxzero] at hx
  have hyne : y ≠ 0 := by
    intro hyzero
    simp [hyzero] at hy
  have hxx := hpos x hxne
  have hyy := hpos y hyne
  have hsym : B y x = B x y := by
    simpa only [RingHom.id_apply] using (hB x y).symm
  rw [apply_reflect, hsym] at hxmin
  rw [apply_reflect] at hymin
  have hboundx := two_mul_le_of_reflection_minimum
    (div_pos (mul_pos (by norm_num) hxypos) hyy) hy hxmin
  have hboundy := two_mul_le_of_reflection_minimum
    (div_pos (mul_pos (by norm_num) hxypos) hxx) hx hymin
  rw [div_mul_eq_mul_div, le_div_iff₀ hyy] at hboundx
  rw [div_mul_eq_mul_div, le_div_iff₀ hxx] at hboundy
  have hfirst : B x x * h y ≤ B x y * h x := by nlinarith [hboundy]
  have hsecond : B y y * h x ≤ B x y * h y := by nlinarith [hboundx]
  have hmul := mul_le_mul hfirst hsecond
    (mul_nonneg hyy.le hx.le) (mul_nonneg hxypos.le hx.le)
  have hineq : (B x x * B y y) * (h x * h y) ≤
      (B x y) ^ 2 * (h x * h y) := by
    nlinarith only [hmul]
  have hc := (mul_le_mul_right (mul_pos hx hy)).mp hineq
  exact (not_le_of_gt (strict_cauchy B hB hpos hxne hxy)) hc

/-- Cardinal bound once representatives minimizing reflection values have been chosen. -/
theorem card_le_finrank_of_reflection_minima [Fintype I] [FiniteDimensional K V]
    (B : BilinForm K V) (hB : B.IsSymm)
    (hpos : ∀ z : V, z ≠ 0 → 0 < B z z)
    (h : V →ₗ[K] K) (v : I → V)
    (hv : ∀ i, 0 < h (v i))
    (hcol : ∀ i j, i ≠ j → ∀ a : K, v j ≠ a • v i)
    (hmin : ∀ i j, h (v j) ≤ |h (reflect B (v i) (v j))|) :
    Fintype.card I ≤ Module.finrank K V := by
  apply LinearIndependent.fintype_card_le_finrank
  apply linearIndependent_of_pairwise_nonpos B hpos h v hv
  intro i j hij
  exact pairing_nonpos_of_reflection_minima B hB hpos h
    (hv i) (hv j) (hcol i j hij) (hmin j i) (hmin i j)

/-- A functional avoiding a finite set of nonzero vectors, by finite forbidden-scalar avoidance. -/
theorem exists_functional_ne_zero
    (B : BilinForm K V) (hpos : ∀ z : V, z ≠ 0 → 0 < B z z)
    (S : Finset V) (hS : ∀ x ∈ S, x ≠ 0) :
    ∃ h : V →ₗ[K] K, ∀ x ∈ S, h x ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert x S hxS ih =>
      obtain ⟨h, hh⟩ := ih (fun y hy => hS y (Finset.mem_insert_of_mem hy))
      by_cases hx : h x ≠ 0
      · exact ⟨h, by
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact hx
          · exact hh y hy⟩
      · have hxzero : h x = 0 := not_ne_iff.mp hx
        let T : Finset K := insert 0 (S.image (fun y => -h y / B x y))
        obtain ⟨t, ht⟩ := Infinite.exists_not_mem_finset T
        have htzero : t ≠ 0 := by
          intro htzero
          apply ht
          simp [T, htzero]
        have hxx : B x x ≠ 0 := ne_of_gt (hpos x (hS x (Finset.mem_insert_self _ _)))
        refine ⟨h + t • B x, ?_⟩
        intro y hy
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        rcases Finset.mem_insert.mp hy with rfl | hy
        · simpa [hxzero] using mul_ne_zero htzero hxx
        · intro hzero
          by_cases hxy : B x y = 0
          · exact hh y hy (by simpa [hxy] using hzero)
          · have hteq : t = -h y / B x y := by
              apply (eq_div_iff hxy).mpr
              linarith
            apply ht
            apply Finset.mem_insert_of_mem
            apply Finset.mem_image.mpr
            exact ⟨y, hy, hteq.symm⟩

/-- Select a positive representative of least absolute functional value in a finite symmetric set. -/
theorem exists_positive_minimum
    (S : Finset V) (hne : S.Nonempty)
    (hneg : ∀ x ∈ S, -x ∈ S)
    (h : V →ₗ[K] K) (hnz : ∀ x ∈ S, h x ≠ 0) :
    ∃ v ∈ S, 0 < h v ∧ ∀ y ∈ S, h v ≤ |h y| := by
  classical
  let P := S.filter (fun x => 0 < h x)
  have hP : P.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    by_cases hp : 0 < h x
    · exact ⟨x, Finset.mem_filter.mpr ⟨hx, hp⟩⟩
    · have hm : h x < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hnz x hx)
      refine ⟨-x, Finset.mem_filter.mpr ⟨hneg x hx, ?_⟩⟩
      simpa using neg_pos.mpr hm
  obtain ⟨v, hv, hvmin⟩ := P.exists_min_image (fun x => h x) hP
  have hvS := Finset.mem_filter.mp hv
  refine ⟨v, hvS.1, hvS.2, ?_⟩
  intro y hy
  by_cases hp : 0 ≤ h y
  · rw [abs_of_nonneg hp]
    apply hvmin y
    exact Finset.mem_filter.mpr ⟨hy, lt_of_le_of_ne hp (Ne.symm (hnz y hy))⟩
  · rw [abs_of_neg (lt_of_not_ge hp)]
    have hm : -y ∈ P := by
      apply Finset.mem_filter.mpr
      refine ⟨hneg y hy, ?_⟩
      simpa using neg_pos.mpr (lt_of_not_ge hp)
    simpa using hvmin (-y) hm

/-- Finite, nonzero, symmetric reflection-stable shells with pairwise noncollinear
directions number at most the ambient dimension. This is the full geometric endpoint. -/
theorem finite_reflection_shells_card_le_finrank
    [Fintype I] [FiniteDimensional K V]
    (B : BilinForm K V) (hB : B.IsSymm)
    (hpos : ∀ z : V, z ≠ 0 → 0 < B z z)
    (S : I → Finset V)
    (hne : ∀ i, (S i).Nonempty)
    (hnz : ∀ i x, x ∈ S i → x ≠ 0)
    (hneg : ∀ i x, x ∈ S i → -x ∈ S i)
    (hreflect : ∀ i j x, x ∈ S i → ∀ y, y ∈ S j → reflect B x y ∈ S j)
    (hcol : ∀ i j, i ≠ j → ∀ x, x ∈ S i → ∀ y, y ∈ S j →
      ∀ a : K, y ≠ a • x) :
    Fintype.card I ≤ Module.finrank K V := by
  classical
  let T := Finset.univ.biUnion S
  have hT : ∀ x ∈ T, x ≠ 0 := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    exact hnz i x hxi
  obtain ⟨h, hh⟩ := exists_functional_ne_zero B hpos T hT
  have hhS : ∀ i x, x ∈ S i → h x ≠ 0 := by
    intro i x hx
    exact hh x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
  have hchoose : ∀ i, ∃ v ∈ S i, 0 < h v ∧ ∀ y ∈ S i, h v ≤ |h y| := by
    intro i
    exact exists_positive_minimum (S i) (hne i) (hneg i) h (hhS i)
  choose v hv hvpos hvmin using hchoose
  apply card_le_finrank_of_reflection_minima B hB hpos h v hvpos
  · intro i j hij
    exact hcol i j hij (v i) (hv i) (v j) (hv j)
  · intro i j
    exact hvmin j _ (hreflect i j _ (hv i) _ (hv j))

end UnitSquareclass

#print axioms UnitSquareclass.strict_cauchy
#print axioms UnitSquareclass.linearIndependent_of_pairwise_nonpos
#print axioms UnitSquareclass.card_le_finrank_of_reflection_minima
#print axioms UnitSquareclass.finite_reflection_shells_card_le_finrank
