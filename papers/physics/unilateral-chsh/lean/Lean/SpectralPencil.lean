import UnilateralCHSH
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Set.Card

/-!
Spectral theory for the singular unilateral CHSH pencil.

The definitions use real three-vectors and the stationary equations directly.
No nonsingularity hypothesis is imposed on K = A - s I.  This module does not
assume compactness, existence of a maximum, or the target optimization formula.
-/

set_option autoImplicit false

namespace UnilateralCHSH
namespace Spectral

noncomputable section

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def IsPair (A C : Mat) (s mu : ℝ) (n v : Vec) : Prop :=
  (matVec A n - matVec C v = fun i => mu * n i) ∧
  (matVec (shift A (-s)) v + matVec C n = 0)

def Level (A C : Mat) (s : ℝ) : Set ℝ :=
  {mu | ∃ n v : Vec, n ≠ 0 ∧ IsPair A C s mu n v}

def EligibleLevel (A C : Mat) (s : ℝ) : Set ℝ :=
  {mu | ∃ n v : Vec, n ≠ 0 ∧ IsPair A C s mu n v ∧ normSq v ≤ normSq n}

def StrictEligibleLevel (A C : Mat) (s : ℝ) : Set ℝ :=
  {mu | ∃ n v : Vec, n ≠ 0 ∧ IsPair A C s mu n v ∧ normSq v < normSq n}

def IsFeasible (n v : Vec) : Prop :=
  normSq n = 1 ∧ dot n v = 0 ∧ normSq v ≤ 1

def IsInterior (n v : Vec) : Prop :=
  normSq n = 1 ∧ dot n v = 0 ∧ normSq v < 1

theorem dot_zero_right (x : Vec) : dot x 0 = 0 := by simp [dot]

theorem dot_zero_left (x : Vec) : dot 0 x = 0 := by simp [dot]

theorem pair_scale (A C : Mat) (s mu t : ℝ) (n v : Vec)
    (h : IsPair A C s mu n v) :
    IsPair A C s mu (fun i => t * n i) (fun i => t * v i) := by
  constructor
  · rw [matVec_scale, matVec_scale]
    funext i
    have hi := congrFun h.1 i
    simp only [Pi.sub_apply] at hi ⊢
    rw [← mul_sub, hi]
    ring
  · rw [matVec_scale, matVec_scale]
    funext i
    have hi := congrFun h.2 i
    simp only [Pi.add_apply, Pi.zero_apply] at hi ⊢
    rw [← mul_add, hi, mul_zero]

theorem pair_exchange (A C : Mat) (s : ℝ) (n v m w : Vec)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i) :
    dot m (matVec A n - matVec C v) +
        dot w (matVec (shift A (-s)) v + matVec C n) =
      dot n (matVec A m - matVec C w) +
        dot v (matVec (shift A (-s)) w + matVec C m) := by
  rw [dot_sub_right, dot_add_right, dot_sub_right, dot_add_right]
  have hA := symmetric_dot_exchange A m n hsym
  have hK := symmetric_dot_exchange (shift A (-s)) w v (shift_symmetric A (-s) hsym)
  have hC := skew_dot_exchange C m v hskew
  have hC' := skew_dot_exchange C w n hskew
  linarith

theorem distinct_pair_orthogonality (A C : Mat) (s mu nu : ℝ) (n v m w : Vec)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hmu : IsPair A C s mu n v) (hnu : IsPair A C s nu m w)
    (hne : mu ≠ nu) : dot n m = 0 := by
  have he := pair_exchange A C s n v m w hsym hskew
  rw [hmu.1, hmu.2, hnu.1, hnu.2,
    dot_zero_right, dot_zero_right, dot_scale_right, dot_scale_right,
    dot_symm m n] at he
  have hp : (mu - nu) * dot n m = 0 := by nlinarith
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hne)

theorem pair_orthogonality (A C : Mat) (s mu : ℝ) (n v : Vec)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i)
    (h : IsPair A C s mu n v) (hne : mu ≠ s) : dot n v = 0 :=
  spectral_orthogonality A C n v s mu hsym hskew hne h.1 h.2

theorem pair_value (A C : Mat) (s mu traceA : ℝ) (n v : Vec)
    (hskew : ∀ i j, C i j = -C j i)
    (h : IsPair A C s mu n v) (hn : normSq n = 1) :
    reducedObjective A C s traceA n v = traceA - mu :=
  spectral_stationary_value A C n v s mu traceA hskew hn h.1 h.2

theorem exceptional_pair_real (A C : Mat) (s : ℝ) (n v : Vec)
    (h : IsPair A C s s n v) :
    matVec (shift A (-s)) n - matVec C v = 0 := by
  rw [matVec_shift]
  funext i
  have hi := congrFun h.1 i
  simp only [Pi.sub_apply, Pi.zero_apply] at hi ⊢
  linarith

theorem exceptional_real_pair (A C : Mat) (s : ℝ) (n v : Vec)
    (hr : matVec (shift A (-s)) n - matVec C v = 0)
    (hi : matVec (shift A (-s)) v + matVec C n = 0) :
    IsPair A C s s n v := by
  refine ⟨?_, hi⟩
  rw [matVec_shift] at hr
  funext i
  have hri := congrFun hr i
  simp only [Pi.sub_apply, Pi.zero_apply] at hri ⊢
  linarith

theorem normalize_pair (A C : Mat) (s mu : ℝ) (n v : Vec)
    (h : IsPair A C s mu n v) (hn : n ≠ 0) (horth : dot n v = 0)
    (hsize : normSq v ≤ normSq n) :
    ∃ n' v' : Vec, IsPair A C s mu n' v' ∧ IsFeasible n' v' := by
  have hnp := normSq_pos n hn
  let r := Real.sqrt (normSq n)
  have hrp : 0 < r := Real.sqrt_pos.mpr hnp
  have hrs : r ^ 2 = normSq n := Real.sq_sqrt (le_of_lt hnp)
  have hrn : r ≠ 0 := ne_of_gt hrp
  let t := 1 / r
  let n' : Vec := fun i => t * n i
  let v' : Vec := fun i => t * v i
  have hns : normSq n' = 1 := by
    rw [normSq_scale]
    dsimp only [t]
    rw [← hrs]
    field_simp
  have hvs : normSq v' ≤ 1 := by
    rw [normSq_scale]
    have hm := mul_le_mul_of_nonneg_left hsize (sq_nonneg t)
    rw [normSq_scale] at hns
    linarith
  have hdot : dot n' v' = 0 := by rw [dot_scale_both, horth, mul_zero]
  exact ⟨n', v', pair_scale A C s mu t n v h, hns, hdot, hvs⟩

theorem eligible_iff_feasible_pair (A C : Mat) (s mu : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i) :
    mu ∈ EligibleLevel A C s ↔
      ∃ n v : Vec, IsPair A C s mu n v ∧ IsFeasible n v := by
  constructor
  · rintro ⟨n, v, hn, hp, hsize⟩
    by_cases he : mu = s
    · subst mu
      have hreal := exceptional_pair_real A C s n v hp
      have hnonzero : 0 < normSq n + normSq v := by
        have hnp := normSq_pos n hn
        have hvp := normSq_nonneg v
        linarith
      obtain ⟨n', v', hn', horth, hv', hr, hi⟩ :=
        kernel_pair_feasible (shift A (-s)) C n v hreal hp.2 hnonzero
      exact ⟨n', v', exceptional_real_pair A C s n' v' hr hi, hn', horth, hv'⟩
    · exact normalize_pair A C s mu n v hp hn
        (pair_orthogonality A C s mu n v hsym hskew hp he) hsize
  · rintro ⟨n, v, hp, hn, horth, hv⟩
    have hne : n ≠ 0 := by
      intro hz
      have hzero : normSq n = 0 := (normSq_eq_zero_iff n).mpr hz
      linarith
    exact ⟨n, v, hne, hp, by simpa only [hn] using hv⟩

theorem eligible_candidate_value (A C : Mat) (s mu traceA : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hmu : mu ∈ EligibleLevel A C s) :
    ∃ n v : Vec, IsFeasible n v ∧
      reducedObjective A C s traceA n v = traceA - mu := by
  obtain ⟨n, v, hp, hf⟩ := (eligible_iff_feasible_pair A C s mu hsym hskew).mp hmu
  exact ⟨n, v, hf, pair_value A C s mu traceA n v hskew hp hf.1⟩

theorem eligible_subset_level (A C : Mat) (s : ℝ) :
    EligibleLevel A C s ⊆ Level A C s := by
  rintro mu ⟨n, v, hn, hp, _⟩
  exact ⟨n, v, hn, hp⟩

def dotLinear (x : Vec) : Vec →ₗ[ℝ] ℝ where
  toFun := dot x
  map_add' := dot_add_right x
  map_smul' := by
    intro a y
    change dot x (fun i => a * y i) = a * dot x y
    exact dot_scale_right x y a

@[simp] theorem dotLinear_apply (x y : Vec) : dotLinear x y = dot x y := rfl

theorem orthogonal_family_independent {ι : Type*} (f : ι → Vec)
    (hne : ∀ i, f i ≠ 0) (horth : ∀ i j, i ≠ j → dot (f i) (f j) = 0) :
    LinearIndependent ℝ f := by
  classical
  apply linearIndependent_iff'.mpr
  intro S g hg i hi
  have he := congrArg (dotLinear (f i)) hg
  simp only [map_sum, map_smul, dotLinear_apply, map_zero, smul_eq_mul] at he
  have hsum : ∑ j ∈ S, g j * dot (f i) (f j) = g i * normSq (f i) := by
    rw [Finset.sum_eq_single i]
    · rfl
    · intro j _ hji
      rw [horth i j hji.symm, mul_zero]
    · intro hnot
      exact False.elim (hnot hi)
  rw [hsum] at he
  exact (mul_eq_zero.mp he).resolve_right (ne_of_gt (normSq_pos (f i) (hne i)))

noncomputable def levelN (A C : Mat) (s : ℝ) (mu : Level A C s) : Vec :=
  Classical.choose mu.property

noncomputable def levelV (A C : Mat) (s : ℝ) (mu : Level A C s) : Vec :=
  Classical.choose (Classical.choose_spec mu.property)

theorem level_witness (A C : Mat) (s : ℝ) (mu : Level A C s) :
    levelN A C s mu ≠ 0 ∧
      IsPair A C s mu.val (levelN A C s mu) (levelV A C s mu) :=
  Classical.choose_spec (Classical.choose_spec mu.property)

theorem level_family_independent (A C : Mat) (s : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i) :
    LinearIndependent ℝ (levelN A C s) := by
  apply orthogonal_family_independent
  · intro mu
    exact (level_witness A C s mu).1
  · intro mu nu hne
    have hne' : mu.val ≠ nu.val := by
      intro he
      exact hne (Subtype.ext he)
    exact distinct_pair_orthogonality A C s mu.val nu.val
      (levelN A C s mu) (levelV A C s mu)
      (levelN A C s nu) (levelV A C s nu) hsym hskew
      (level_witness A C s mu).2 (level_witness A C s nu).2 hne'

theorem level_finite (A C : Mat) (s : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i) : (Level A C s).Finite := by
  haveI : Finite (Level A C s) := (level_family_independent A C s hsym hskew).finite
  exact Set.toFinite (Level A C s)

theorem level_ncard_le_three (A C : Mat) (s : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i) : (Level A C s).ncard ≤ 3 := by
  letI := (level_finite A C s hsym hskew).fintype
  have h := (level_family_independent A C s hsym hskew).fintype_card_le_finrank
  rw [← Set.Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  simpa only [Vec, Module.finrank_fin_fun] using h

theorem eligible_finite (A C : Mat) (s : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i) : (EligibleLevel A C s).Finite :=
  (level_finite A C s hsym hskew).subset (eligible_subset_level A C s)

theorem eligible_ncard_le_three (A C : Mat) (s : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i) : (EligibleLevel A C s).ncard ≤ 3 :=
  (Set.ncard_le_ncard (eligible_subset_level A C s)
    (level_finite A C s hsym hskew)).trans (level_ncard_le_three A C s hsym hskew)

theorem phase_gap_identity (n v : Vec) (p q : ℝ) :
    (normSq (rotatedReal n v p q) - normSq (rotatedImag n v p q)) ^ 2 +
        4 * (dot (rotatedReal n v p q) (rotatedImag n v p q)) ^ 2 =
      (p ^ 2 + q ^ 2) ^ 2 * ((normSq n - normSq v) ^ 2 + 4 * (dot n v) ^ 2) := by
  rw [phase_rotation_norm_difference, phase_rotation_dot]
  ring

theorem exists_strict_ordered_orthogonal_phase (n v : Vec)
    (hgap : normSq v < normSq n) :
    ∃ p q : ℝ, 0 < p ^ 2 + q ^ 2 ∧
      dot (rotatedReal n v p q) (rotatedImag n v p q) = 0 ∧
      normSq (rotatedImag n v p q) < normSq (rotatedReal n v p q) := by
  obtain ⟨p, q, hpq, horth, hord⟩ := exists_ordered_orthogonal_phase n v
  have hgap' : 0 < normSq n - normSq v := sub_pos.mpr hgap
  have hrad : 0 < (normSq n - normSq v) ^ 2 + 4 * (dot n v) ^ 2 := by
    have hp := sq_pos_of_pos hgap'
    nlinarith [sq_nonneg (dot n v)]
  have hprod := mul_pos (sq_pos_of_pos hpq) hrad
  rw [← phase_gap_identity n v p q, horth] at hprod
  refine ⟨p, q, hpq, horth, ?_⟩
  nlinarith

theorem normalize_pair_strict (A C : Mat) (s mu : ℝ) (n v : Vec)
    (h : IsPair A C s mu n v) (hn : n ≠ 0) (horth : dot n v = 0)
    (hsize : normSq v < normSq n) :
    ∃ n' v' : Vec, IsPair A C s mu n' v' ∧ IsInterior n' v' := by
  have hnp := normSq_pos n hn
  let r := Real.sqrt (normSq n)
  have hrp : 0 < r := Real.sqrt_pos.mpr hnp
  have hrs : r ^ 2 = normSq n := Real.sq_sqrt (le_of_lt hnp)
  have hrn : r ≠ 0 := ne_of_gt hrp
  let t := 1 / r
  let n' : Vec := fun i => t * n i
  let v' : Vec := fun i => t * v i
  have hns : normSq n' = 1 := by
    rw [normSq_scale]
    dsimp only [t]
    rw [← hrs]
    field_simp
  have ht : 0 < t := one_div_pos.mpr hrp
  have hvs : normSq v' < 1 := by
    rw [normSq_scale]
    have hm := mul_lt_mul_of_pos_left hsize (sq_pos_of_pos ht)
    rw [normSq_scale] at hns
    linarith
  have hdot : dot n' v' = 0 := by rw [dot_scale_both, horth, mul_zero]
  exact ⟨n', v', pair_scale A C s mu t n v h, hns, hdot, hvs⟩

theorem strict_eligible_iff_interior_pair (A C : Mat) (s mu : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i) :
    mu ∈ StrictEligibleLevel A C s ↔
      ∃ n v : Vec, IsPair A C s mu n v ∧ IsInterior n v := by
  constructor
  · rintro ⟨n, v, hn, hp, hsize⟩
    by_cases he : mu = s
    · subst mu
      have hreal := exceptional_pair_real A C s n v hp
      obtain ⟨p, q, _, horth, hgap⟩ := exists_strict_ordered_orthogonal_phase n v hsize
      obtain ⟨hr, hi⟩ := phase_rotation_kernel (shift A (-s)) C n v p q hreal hp.2
      have hp' := exceptional_real_pair A C s
        (rotatedReal n v p q) (rotatedImag n v p q) hr hi
      have hn' : rotatedReal n v p q ≠ 0 := by
        intro hz
        have hzero := (normSq_eq_zero_iff _).mpr hz
        have hnonneg := normSq_nonneg (rotatedImag n v p q)
        linarith
      exact normalize_pair_strict A C s s _ _ hp' hn' horth hgap
    · exact normalize_pair_strict A C s mu n v hp hn
        (pair_orthogonality A C s mu n v hsym hskew hp he) hsize
  · rintro ⟨n, v, hp, hn, horth, hv⟩
    have hne : n ≠ 0 := by
      intro hz
      have hzero : normSq n = 0 := (normSq_eq_zero_iff n).mpr hz
      linarith
    exact ⟨n, v, hne, hp, by simpa only [hn] using hv⟩

theorem strict_eligible_candidate_value (A C : Mat) (s mu traceA : ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hmu : mu ∈ StrictEligibleLevel A C s) :
    ∃ n v : Vec, IsInterior n v ∧
      reducedObjective A C s traceA n v = traceA - mu := by
  obtain ⟨n, v, hp, hf⟩ := (strict_eligible_iff_interior_pair A C s mu hsym hskew).mp hmu
  exact ⟨n, v, hf, pair_value A C s mu traceA n v hskew hp hf.1⟩

theorem strict_eligible_subset_eligible (A C : Mat) (s : ℝ) :
    StrictEligibleLevel A C s ⊆ EligibleLevel A C s := by
  rintro mu ⟨n, v, hn, hp, hsize⟩
  exact ⟨n, v, hn, hp, hsize.le⟩

def CommonKernel (A C : Mat) (s : ℝ) (w : Vec) : Prop :=
  matVec (shift A (-s)) w = 0 ∧ matVec C w = 0

def ReducedSecond (A C : Mat) (s : ℝ) (v : Vec) : Prop :=
  ∀ w : Vec, CommonKernel A C s w → dot v w = 0

theorem common_reduced_zero (A C : Mat) (s : ℝ) (v : Vec)
    (hk : CommonKernel A C s v) (hr : ReducedSecond A C s v) : v = 0 := by
  apply (normSq_eq_zero_iff v).mp
  exact hr v hk

theorem pair_zero_projection_common (A C : Mat) (s mu : ℝ) (v : Vec)
    (h : IsPair A C s mu 0 v) : CommonKernel A C s v := by
  constructor
  · simpa only [matVec_zero, add_zero] using h.2
  · have hc := h.1
    simp only [matVec_zero, zero_sub, Pi.zero_apply, mul_zero] at hc
    exact neg_eq_zero.mp hc

theorem reduced_pair_zero_projection (A C : Mat) (s mu : ℝ) (v : Vec)
    (h : IsPair A C s mu 0 v) (hr : ReducedSecond A C s v) : v = 0 :=
  common_reduced_zero A C s v (pair_zero_projection_common A C s mu v h) hr

theorem reduced_pair_nonzero_projection (A C : Mat) (s mu : ℝ) (n v : Vec)
    (h : IsPair A C s mu n v) (hr : ReducedSecond A C s v)
    (hne : n ≠ 0 ∨ v ≠ 0) : n ≠ 0 := by
  intro hz
  subst n
  have hv := reduced_pair_zero_projection A C s mu v h hr
  rcases hne with hne | hne
  · exact hne rfl
  · exact hne hv

theorem complex_pencil_imaginary_product (A C : Mat) (s a b : ℝ)
    (n v m w : Vec)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hreal : matVec A n - matVec C v = fun i => a * n i - b * m i)
    (himag : matVec A m - matVec C w = fun i => b * n i + a * m i)
    (hbottomR : matVec (shift A (-s)) v + matVec C n = 0)
    (hbottomI : matVec (shift A (-s)) w + matVec C m = 0) :
    b * (normSq n + normSq m) = 0 := by
  have he := pair_exchange A C s n v m w hsym hskew
  rw [hreal, himag, hbottomR, hbottomI, dot_zero_right, dot_zero_right] at he
  have hR : dot m (fun i => a * n i - b * m i) =
      a * dot m n - b * normSq m := by simp only [dot, normSq]; ring
  have hI : dot n (fun i => b * n i + a * m i) =
      b * normSq n + a * dot n m := by simp only [dot, normSq]; ring
  rw [hR, hI, dot_symm m n] at he
  nlinarith

theorem reduced_complex_eigenvalue_real (A C : Mat) (s a b : ℝ)
    (n v m w : Vec)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hreal : matVec A n - matVec C v = fun i => a * n i - b * m i)
    (himag : matVec A m - matVec C w = fun i => b * n i + a * m i)
    (hbottomR : matVec (shift A (-s)) v + matVec C n = 0)
    (hbottomI : matVec (shift A (-s)) w + matVec C m = 0)
    (hvred : ReducedSecond A C s v) (hwred : ReducedSecond A C s w)
    (hnonzero : n ≠ 0 ∨ v ≠ 0 ∨ m ≠ 0 ∨ w ≠ 0) : b = 0 := by
  by_contra hb
  have hp := complex_pencil_imaginary_product A C s a b n v m w hsym hskew
    hreal himag hbottomR hbottomI
  have hsum := (mul_eq_zero.mp hp).resolve_left hb
  have hnp := normSq_nonneg n
  have hmp := normSq_nonneg m
  have hn : n = 0 := (normSq_eq_zero_iff n).mp (by linarith)
  have hm : m = 0 := (normSq_eq_zero_iff m).mp (by linarith)
  have hvpair : IsPair A C s 0 0 v := by
    constructor
    · simpa only [hn, hm, Pi.zero_apply, mul_zero, sub_zero] using hreal
    · simpa only [hn] using hbottomR
  have hwpair : IsPair A C s 0 0 w := by
    constructor
    · simpa only [hn, hm, Pi.zero_apply, mul_zero, add_zero] using himag
    · simpa only [hm] using hbottomI
  have hv := reduced_pair_zero_projection A C s 0 v hvpair hvred
  have hw := reduced_pair_zero_projection A C s 0 w hwpair hwred
  rcases hnonzero with h | h | h | h
  · exact h hn
  · exact h hv
  · exact h hm
  · exact h hw

theorem reduced_pencil_at_i_has_trivial_kernel (A C : Mat) (s : ℝ)
    (n v m w : Vec)
    (hsym : ∀ i j, A i j = A j i)
    (hskew : ∀ i j, C i j = -C j i)
    (hreal : matVec A n - matVec C v = fun i => -m i)
    (himag : matVec A m - matVec C w = n)
    (hbottomR : matVec (shift A (-s)) v + matVec C n = 0)
    (hbottomI : matVec (shift A (-s)) w + matVec C m = 0)
    (hvred : ReducedSecond A C s v) (hwred : ReducedSecond A C s w) :
    n = 0 ∧ v = 0 ∧ m = 0 ∧ w = 0 := by
  by_contra hnot
  have hnonzero : n ≠ 0 ∨ v ≠ 0 ∨ m ≠ 0 ∨ w ≠ 0 := by tauto
  have hR : matVec A n - matVec C v = fun i => (0 : ℝ) * n i - 1 * m i := by
    simpa only [zero_mul, one_mul, zero_sub] using hreal
  have hI : matVec A m - matVec C w = fun i => (1 : ℝ) * n i + 0 * m i := by
    simpa only [one_mul, zero_mul, add_zero] using himag
  have hf := reduced_complex_eigenvalue_real A C s 0 1 n v m w hsym hskew
    hR hI hbottomR hbottomI hvred hwred hnonzero
  norm_num at hf


end
end Spectral
end UnilateralCHSH
