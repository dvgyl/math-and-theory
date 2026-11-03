import MilneOrbitDiagonal
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Field

/-!
# Constructive solution of every three-dimensional ball quadratic

The diagonal problem is solved at its spectral floor or at the unique regular
secular root. The floor branch includes the hard case: a null-eigenspace
component fills the remaining sphere radius. No invertibility, nonzero linear
term, or positive-definiteness assumption is made.
-/

open scoped BigOperators
open Set

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000

noncomputable section
namespace Milne

def trustMinEigen (d : TrustVector) : ℝ := min (d 0) (min (d 1) (d 2))

def trustShiftFloor (d : TrustVector) : ℝ := max 0 (-trustMinEigen d)

def trustFloorAdmissible (d h : TrustVector) : Prop :=
  (∀ i, d i+trustShiftFloor d=0 → h i=0) ∧
    trustSq (trustDiagPoint d h (trustShiftFloor d)) ≤ 1

def trustShiftAdmissible (d h : TrustVector) (l : ℝ) : Prop :=
  (l=trustShiftFloor d ∧ trustFloorAdmissible d h) ∨
    (trustShiftFloor d<l ∧ trustSq (trustDiagPoint d h l)=1)

theorem trustMinEigen_le (d : TrustVector) (i : Fin 3) : trustMinEigen d ≤ d i := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem trustMinEigen_attained (d : TrustVector) : ∃ i : Fin 3, d i=trustMinEigen d := by
  by_cases h0 : d 0 ≤ min (d 1) (d 2)
  · exact ⟨0,(min_eq_left h0).symm⟩
  · by_cases h1 : d 1 ≤ d 2
    · refine ⟨1,?_⟩
      have h10 : d 1 ≤ d 0 := by
        simpa only [min_eq_left h1] using le_of_not_ge h0
      simp only [trustMinEigen,min_eq_left h1,min_eq_right h10]
    · refine ⟨2,?_⟩
      have h20 : d 2 ≤ d 0 := by
        simpa only [min_eq_right (le_of_not_ge h1)] using le_of_not_ge h0
      simp only [trustMinEigen,min_eq_right (le_of_not_ge h1),min_eq_right h20]

theorem trustShiftFloor_nonneg (d : TrustVector) : 0 ≤ trustShiftFloor d := le_max_left _ _

theorem trustShiftFloor_weights (d : TrustVector) (i : Fin 3) : 0 ≤ d i+trustShiftFloor d := by
  have h0 := trustMinEigen_le d i
  have h1 : -trustMinEigen d ≤ trustShiftFloor d := le_max_right _ _
  linarith

theorem trustShiftFloor_pole (d : TrustVector) (hl : trustShiftFloor d ≠ 0) :
    ∃ i : Fin 3, d i+trustShiftFloor d=0 := by
  obtain ⟨i,hi⟩ := trustMinEigen_attained d
  by_cases hm : 0 ≤ -trustMinEigen d
  · refine ⟨i,?_⟩
    rw [trustShiftFloor,max_eq_right hm,hi]
    ring
  · have hz : trustShiftFloor d=0 := max_eq_left (le_of_not_ge hm)
    exact False.elim (hl hz)

def trustPadCoordinate (p : TrustVector) (j : Fin 3) (z : ℝ) : TrustVector :=
  fun i => p i+if i=j then z else 0

theorem trustPadCoordinate_sq (p : TrustVector) (j : Fin 3) (z : ℝ) :
    trustSq (trustPadCoordinate p j z)=trustSq p+2*z*p j+z^2 := by
  fin_cases j <;> simp [trustPadCoordinate,trustSq,Fin.sum_univ_three]
  all_goals ring

theorem trustDiagPoint_equation (d h : TrustVector) (l : ℝ)
    (hpoles : ∀ i, d i+l=0 → h i=0) :
    ∀ i, (d i+l)*trustDiagPoint d h l i=h i := by
  intro i
  by_cases hi : d i+l=0
  · simp [trustDiagPoint,hi,hpoles i hi]
  · dsimp only [trustDiagPoint]
    field_simp

/-- Explicit certificate at the spectral floor. When the shift is positive,
one lowest-eigenspace coordinate supplies the missing sphere radius. -/
theorem trust_floor_certificate (d h : TrustVector) (hh : trustFloorAdmissible d h) :
    ∃ p : TrustVector, trustDiagCertificate d h p (trustShiftFloor d) := by
  let l := trustShiftFloor d
  let q := trustDiagPoint d h l
  have hweights : ∀ i, 0 ≤ d i+l := trustShiftFloor_weights d
  have hqeq : ∀ i, (d i+l)*q i=h i := trustDiagPoint_equation d h l hh.1
  by_cases hl : l=0
  · exact ⟨q,trustShiftFloor_nonneg d,hweights,hqeq,hh.2,by
      change l*(1-trustSq q)=0
      rw [hl]; simp⟩
  · obtain ⟨j,hj⟩ := trustShiftFloor_pole d hl
    have hqj : q j=0 := by simp [q,trustDiagPoint,l,hj]
    let z := Real.sqrt (1-trustSq q)
    have hz : z^2=1-trustSq q := Real.sq_sqrt (sub_nonneg.mpr hh.2)
    let p := trustPadCoordinate q j z
    have hpsq : trustSq p=1 := by
      rw [trustPadCoordinate_sq,hqj,mul_zero,hz]
      ring
    refine ⟨p,trustShiftFloor_nonneg d,hweights,?_,by rw [hpsq],by rw [hpsq]; simp⟩
    intro i
    by_cases hi : i=j
    · subst i
      rw [hj,zero_mul,hh.1 j hj]
    · simpa [p,trustPadCoordinate,hi] using hqeq i

/-- Beyond the spectral floor every denominator is strictly positive. -/
theorem trust_regular_weights (d : TrustVector) (l : ℝ) (hl : trustShiftFloor d<l)
    (i : Fin 3) : 0 < d i+l := by
  have h := trustShiftFloor_weights d i
  linarith

theorem trust_regular_certificate (d h : TrustVector) (l : ℝ)
    (hl : trustShiftFloor d<l) (hn : trustSq (trustDiagPoint d h l)=1) :
    trustDiagCertificate d h (trustDiagPoint d h l) l := by
  have hpoles : ∀ i, d i+l=0 → h i=0 := by
    intro i hz
    have hpos := trust_regular_weights d l hl i
    linarith
  exact ⟨le_of_lt ((trustShiftFloor_nonneg d).trans_lt hl),
    fun i => le_of_lt (trust_regular_weights d l hl i),
    trustDiagPoint_equation d h l hpoles,by rw [hn],by rw [hn]; simp⟩

theorem trust_secular_continuousOn (d h : TrustVector) (a : ℝ)
    (ha : ∀ i, 0 ≤ d i+a) (hz : ∀ i, d i+a=0 → h i=0) :
    ContinuousOn (fun l => trustSq (trustDiagPoint d h l)) (Ici a) := by
  unfold trustSq trustDiagPoint
  apply continuousOn_finset_sum
  intro i _
  by_cases hi : h i=0
  · simp only [hi,zero_div,zero_pow (by decide : 2 ≠ 0)]
    exact continuousOn_const
  · apply ContinuousOn.pow
    apply ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
    intro l hl
    have hpos : 0 < d i+a := by
      have hn : d i+a ≠ 0 := fun h0 => hi (hz i h0)
      exact lt_of_le_of_ne (ha i) (Ne.symm hn)
    have hla : a ≤ l := hl
    change d i+l ≠ 0
    linarith

/-- A finite, explicit right endpoint where the secular norm is below one. -/
theorem trust_secular_upper_endpoint (d h : TrustVector) (a : ℝ)
    (ha : ∀ i, 0 ≤ d i+a) :
    ∃ b : ℝ, a<b ∧ trustSq (trustDiagPoint d h b)<1 := by
  let z := Real.sqrt (trustSq h)
  let B := 1+z
  let b := a+B
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hzsq : z^2=trustSq h := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hB : 0 < B := by dsimp [B]; linarith
  have hBsq : 0 < B^2 := sq_pos_of_pos hB
  have hden (i : Fin 3) : B ≤ d i+b := by dsimp [b]; linarith [ha i]
  have hle : trustSq (trustDiagPoint d h b) ≤ trustSq h/B^2 := by
    unfold trustSq trustDiagPoint
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    rw [div_pow]
    apply div_le_div_of_nonneg_left (sq_nonneg _) hBsq
    have hi := hden i
    nlinarith
  have hlt : trustSq h/B^2<1 := by
    apply (div_lt_one hBsq).mpr
    dsimp [B]
    nlinarith
  exact ⟨b,by dsimp [b]; linarith,lt_of_le_of_lt hle hlt⟩

theorem trust_secular_root_from_bracket (d h : TrustVector) (a : ℝ)
    (ha : trustShiftFloor d ≤ a) (hwa : ∀ i, 0 ≤ d i+a)
    (hza : ∀ i, d i+a=0 → h i=0)
    (hna : 1<trustSq (trustDiagPoint d h a)) :
    ∃ l : ℝ, trustShiftFloor d<l ∧ trustSq (trustDiagPoint d h l)=1 := by
  obtain ⟨b,hab,hb⟩ := trust_secular_upper_endpoint d h a hwa
  have hcont : ContinuousOn (fun l => trustSq (trustDiagPoint d h l)) (Icc a b) :=
    (trust_secular_continuousOn d h a hwa hza).mono fun _ hx => hx.1
  obtain ⟨l,hl,he⟩ := intermediate_value_Icc' (le_of_lt hab) hcont
    (show (1:ℝ) ∈ Icc (trustSq (trustDiagPoint d h b)) (trustSq (trustDiagPoint d h a)) from
      ⟨le_of_lt hb,le_of_lt hna⟩)
  have hal : a<l := by
    by_contra hn
    have heq : l=a := le_antisymm (le_of_not_gt hn) hl.1
    rw [heq] at he
    linarith
  exact ⟨l,lt_of_le_of_lt ha hal,he⟩

/-- If the floor is inadmissible, a regular secular root always exists.
The pole case is handled by an explicit finite left endpoint, without
assuming a finite limit at the singular floor. -/
theorem trust_regular_root_exists (d h : TrustVector) (hh : ¬trustFloorAdmissible d h) :
    ∃ l : ℝ, trustShiftFloor d<l ∧ trustSq (trustDiagPoint d h l)=1 := by
  by_cases hz : ∀ i, d i+trustShiftFloor d=0 → h i=0
  · have hn : 1<trustSq (trustDiagPoint d h (trustShiftFloor d)) := by
      by_contra hn
      exact hh ⟨hz,le_of_not_gt hn⟩
    exact trust_secular_root_from_bracket d h (trustShiftFloor d) le_rfl
      (trustShiftFloor_weights d) hz hn
  · push_neg at hz
    obtain ⟨i,hi,hhi⟩ := hz
    let a := trustShiftFloor d+|h i|/2
    have habs : 0 < |h i| := abs_pos.mpr hhi
    have hla : trustShiftFloor d<a := by dsimp [a]; linarith
    have hwa : ∀ j, 0 ≤ d j+a := fun j => le_of_lt (trust_regular_weights d a hla j)
    have hza : ∀ j, d j+a=0 → h j=0 := by
      intro j h0
      have hj := trust_regular_weights d a hla j
      linarith
    have hden : d i+a=|h i|/2 := by dsimp [a]; linarith
    have hterm : (trustDiagPoint d h a i)^2=4 := by
      rw [trustDiagPoint,hden]
      have hn : |h i| ≠ 0 := ne_of_gt habs
      field_simp
      nlinarith [sq_abs (h i)]
    have hsum : (trustDiagPoint d h a i)^2 ≤ trustSq (trustDiagPoint d h a) :=
      Finset.single_le_sum (fun j _ => sq_nonneg (trustDiagPoint d h a j))
        (Finset.mem_univ i)
    have hna : 1<trustSq (trustDiagPoint d h a) := by rw [hterm] at hsum; linarith
    exact trust_secular_root_from_bracket d h a (le_of_lt hla) hwa hza hna

theorem trust_admissible_exists (d h : TrustVector) : ∃ l : ℝ, trustShiftAdmissible d h l := by
  by_cases hh : trustFloorAdmissible d h
  · exact ⟨trustShiftFloor d,Or.inl ⟨rfl,hh⟩⟩
  · obtain ⟨l,hl,hn⟩ := trust_regular_root_exists d h hh
    exact ⟨l,Or.inr ⟨hl,hn⟩⟩

theorem trust_admissible_certificate (d h : TrustVector) (l : ℝ)
    (hl : trustShiftAdmissible d h l) : ∃ p : TrustVector, trustDiagCertificate d h p l := by
  rcases hl with ⟨rfl,hh⟩ | ⟨hl,hn⟩
  · exact trust_floor_certificate d h hh
  · exact ⟨trustDiagPoint d h l,trust_regular_certificate d h l hl hn⟩

/-- Every quadratic, including all singular and hard cases, has exactly one
admissible nonnegative shift. No optimality condition is assumed. -/
theorem trust_admissible_existsUnique (d h : TrustVector) : ∃! l : ℝ, trustShiftAdmissible d h l := by
  obtain ⟨l,hl⟩ := trust_admissible_exists d h
  refine ⟨l,hl,?_⟩
  intro u hu
  obtain ⟨p,hp⟩ := trust_admissible_certificate d h l hl
  obtain ⟨q,hq⟩ := trust_admissible_certificate d h u hu
  exact (trustDiag_certificate_shift_unique d h p q l u hp hq).symm

/-- An unconditional attained exact maximum, expressed through the finite
floor/secular alternatives rather than a scalar minimization. -/
theorem trust_diagonal_exact_maximum (τ : ℝ) (d h : TrustVector) :
    ∃ l : ℝ, trustShiftAdmissible d h l ∧
      IsGreatest (trustDiagSpectrum τ d h) (trustDiagValue τ d h l) := by
  obtain ⟨l,hl⟩ := trust_admissible_exists d h
  obtain ⟨p,hp⟩ := trust_admissible_certificate d h l hl
  exact ⟨l,hl,trustDiag_certificate_isGreatest τ d h p l hp⟩

end Milne
