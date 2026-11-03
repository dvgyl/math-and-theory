import SameChirality
import Mathlib.Tactic.FieldSimp

/-!
# Exact order theory for an infinite Class D family

This module proves parameterized results over the real numbers, with witness
detection quantified over all complex density matrices. The family is the
Example 2 family from Milne--Jennings--Rudolph, not a newly invented family.
-/

namespace EllipsoidCounterexample

noncomputable section

open Matrix Complex
open scoped ComplexConjugate

/-- A physical state on the boundary of the detector of `W p`.
Its eigenvalues on the `01,10` block are `p/2` and `1-p/2`. -/
def boundaryState (p : ℝ) : M4 :=
  !![0, 0, 0, 0;
     0, 1 / 2, ((p : ℂ) - 1) / 2, 0;
     0, ((p : ℂ) - 1) / 2, 1 / 2, 0;
     0, 0, 0, 0]

lemma boundaryState_hermitian (p : ℝ) : Hermitian (boundaryState p) := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [boundaryState, Complex.div_re, Complex.div_im] <;> ring

lemma boundaryState_quad (p : ℝ) (z : V4) :
    quad (boundaryState p) z =
      p / 4 * Complex.normSq (z 1 + z 2) +
      (2 - p) / 4 * Complex.normSq (z 1 - z 2) := by
  simp [quad, boundaryState, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im]
  ring

theorem boundaryState_state {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    State (boundaryState p) := by
  refine ⟨⟨boundaryState_hermitian p, ?_⟩, ?_⟩
  · intro z
    rw [boundaryState_quad]
    exact add_nonneg
      (mul_nonneg (div_nonneg hp (by norm_num)) (Complex.normSq_nonneg _))
      (mul_nonneg (div_nonneg (sub_nonneg.mpr hp2) (by norm_num))
        (Complex.normSq_nonneg _))
  · norm_num [traceOne, Matrix.trace, boundaryState, Fin.sum_univ_succ]

theorem boundaryState_expectation (p r : ℝ) :
    expect (W r) (boundaryState p) = (p - r) / 2 := by
  rw [expect_W]
  norm_num [boundaryState, Complex.div_re, Complex.div_im,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  ring

/-- A division-free form of the positive-subtraction identity. -/
theorem parametric_subtraction (p q : ℝ) :
    (q : ℂ) • W p = (p : ℂ) • W q + ((q - p : ℝ) : ℂ) • Pplus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [W, Pplus] <;> ring

lemma parametric_expectation (p q : ℝ) (ρ : M4) :
    q * expect (W p) ρ =
      p * expect (W q) ρ + (q - p) * expect Pplus ρ := by
  simp [expect, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    W, Pplus, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

/-- Every increase in the parameter improves detection for every complex state. -/
theorem parametric_finer {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    Finer (W q) (W p) := by
  intro ρ hρ hneg
  have hpos : 0 ≤ expect Pplus ρ := by
    rw [Pplus_expect]
    exact div_nonneg (hρ.1.2 symmetricVector) (by norm_num)
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hmain := parametric_expectation p q ρ
  have hr : 0 ≤ (q - p) * expect Pplus ρ :=
    mul_nonneg (sub_nonneg.mpr hpq) hpos
  have hleft : q * expect (W p) ρ < 0 := mul_neg_of_pos_of_neg hq hneg
  have : p * expect (W q) ρ < 0 := by linarith
  by_contra hnot
  have hnonneg : 0 ≤ expect (W q) ρ := le_of_not_gt hnot
  have hmul := mul_nonneg hp.le hnonneg
  linarith

theorem parametric_strictlyFiner {p q : ℝ}
    (hp : 0 < p) (hp2 : p ≤ 2) (hpq : p < q) :
    StrictlyFiner (W q) (W p) := by
  refine ⟨parametric_finer hp hpq.le, boundaryState p,
    boundaryState_state hp.le hp2, ?_, ?_⟩
  · rw [boundaryState_expectation]
    linarith
  · rw [boundaryState_expectation]
    norm_num

/-- The full detection preorder on this family is exactly the usual real order. -/
theorem parametric_finer_iff {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hq2 : q ≤ 2) :
    Finer (W q) (W p) ↔ p ≤ q := by
  constructor
  · intro h
    by_contra hnot
    have hqp : q < p := lt_of_not_ge hnot
    have hstate := boundaryState_state hq.le hq2
    have hw : expect (W p) (boundaryState q) < 0 := by
      rw [boundaryState_expectation]
      linarith
    have hbad := h (boundaryState q) hstate hw
    rw [boundaryState_expectation] at hbad
    linarith
  · exact parametric_finer hp

theorem parametric_strictlyFiner_iff {p q : ℝ}
    (hp : 0 < p) (hp2 : p ≤ 2) (hq : 0 < q) (hq2 : q ≤ 2) :
    StrictlyFiner (W q) (W p) ↔ p < q := by
  constructor
  · intro h
    have hle := (parametric_finer_iff hp hq hq2).mp h.1
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · rcases h.2 with ⟨ρ, _, hneg, hnonneg⟩
      subst q
      linarith
  · exact parametric_strictlyFiner hp hp2

/-- A separator with strictly positive margin on both sides. -/
theorem midpoint_separator {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ 1) :
    State (boundaryState ((p + q) / 2)) ∧
      expect (W p) (boundaryState ((p + q) / 2)) = (q - p) / 4 ∧
      expect (W q) (boundaryState ((p + q) / 2)) = -(q - p) / 4 := by
  refine ⟨boundaryState_state (by linarith) (by linarith), ?_, ?_⟩ <;>
    rw [boundaryState_expectation] <;> ring

lemma state_diagonal_zero_nonneg {ρ : M4} (hρ : State ρ) : 0 ≤ (ρ 0 0).re := by
  have h := hρ.1.2 (![1, 0, 0, 0] : V4)
  simpa [quad, Fin.sum_univ_succ] using h

lemma state_diagonal_three_nonneg {ρ : M4} (hρ : State ρ) : 0 ≤ (ρ 3 3).re := by
  have h := hρ.1.2 (![0, 0, 0, 1] : V4)
  simpa [quad, Fin.sum_univ_succ] using h

lemma state_diagonal_sum {ρ : M4} (hρ : State ρ) :
    (ρ 0 0).re + (ρ 1 1).re + (ρ 2 2).re + (ρ 3 3).re = 1 := by
  have h := congrArg Complex.re hρ.2
  simpa [traceOne, Matrix.trace, Fin.sum_univ_succ, add_assoc] using h

/-- No state can separate the two witnesses by more than this expectation gap. -/
theorem parametric_expectation_gap_bound {p q : ℝ} (hpq : p ≤ q)
    {ρ : M4} (hρ : State ρ) :
    expect (W p) ρ - expect (W q) ρ ≤ (q - p) / 2 := by
  have h0 := state_diagonal_zero_nonneg hρ
  have h3 := state_diagonal_three_nonneg hρ
  have hsum := state_diagonal_sum hρ
  have hmul := mul_nonneg (sub_nonneg.mpr hpq) (add_nonneg h0 h3)
  have hweighted := congrArg (fun t : ℝ => (q - p) * t) hsum
  rw [expect_W, expect_W]
  nlinarith

/-- The midpoint separator has the largest possible common strict margin.
This bound quantifies over all complex density matrices, not just Bell mixtures. -/
theorem maximal_common_separation_margin {p q m : ℝ} (hpq : p ≤ q)
    {ρ : M4} (hρ : State ρ)
    (hcoarse : m ≤ expect (W p) ρ) (hfine : expect (W q) ρ ≤ -m) :
    m ≤ (q - p) / 4 := by
  have hgap := parametric_expectation_gap_bound hpq hρ
  linarith

def familyRemainder (p q α : ℝ) : M4 := W p - (α : ℂ) • W q

lemma familyRemainder_hermitian (p q α : ℝ) : Hermitian (familyRemainder p q α) := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [familyRemainder, W, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring

lemma familyRemainder_zero (p q α : ℝ) :
    quad (familyRemainder p q α) (![1, 0, 0, 0] : V4) = (p - α * q) / 2 := by
  simp [quad, familyRemainder, W, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

lemma familyRemainder_singlet (p q α : ℝ) :
    quad (familyRemainder p q α) singlet = -p + α * q := by
  simp [quad, familyRemainder, W, singlet, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

lemma familyRemainder_symmetric (p q α : ℝ) :
    quad (familyRemainder p q α) symmetricVector = 2 - p - α * (2 - q) := by
  simp [quad, familyRemainder, W, symmetricVector, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

lemma familyRemainder_quad {p q α : ℝ} (heq : p = α * q) (z : V4) :
    quad (familyRemainder p q α) z =
      (1 - α) / 2 * Complex.normSq (z 1 + z 2) := by
  subst p
  simp [quad, familyRemainder, W, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

/-- Exact feasibility and uniqueness for every scalar PSD subtraction in the family. -/
theorem familyRemainder_psd_iff {p q α : ℝ} (hq : 0 < q) :
    PSD (familyRemainder p q α) ↔ α = p / q ∧ p ≤ q := by
  constructor
  · intro h
    have h0 := h.2 (![1, 0, 0, 0] : V4)
    have hm := h.2 singlet
    have hs := h.2 symmetricVector
    rw [familyRemainder_zero] at h0
    rw [familyRemainder_singlet] at hm
    rw [familyRemainder_symmetric] at hs
    have heq : α * q = p := by linarith
    refine ⟨(eq_div_iff (ne_of_gt hq)).mpr heq, ?_⟩
    have ha : α ≤ 1 := by nlinarith
    nlinarith
  · rintro ⟨ha, hpq⟩
    have heq : p = α * q := ((eq_div_iff (ne_of_gt hq)).mp ha).symm
    have ha1 : α ≤ 1 := by nlinarith
    refine ⟨familyRemainder_hermitian p q α, ?_⟩
    intro z
    rw [familyRemainder_quad heq]
    exact mul_nonneg (div_nonneg (sub_nonneg.mpr ha1) (by norm_num))
      (Complex.normSq_nonneg _)

lemma scaleZ_ball_of_sq_le_one {r : ℝ} (hr : r ^ 2 ≤ 1)
    {u : V3} (hu : u ∈ unitBall) : scaleZ r u ∈ unitBall := by
  change sqNorm (scaleZ r u) ≤ 1
  change sqNorm u ≤ 1 at hu
  have hmul := mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg (u 2))
  simp [scaleZ, sqNorm, Fin.sum_univ_succ] at hu ⊢
  nlinarith

/-- The containment order is determined by the squared third semiaxis. -/
theorem parametric_ellipsoid_subset_iff_sq (p q : ℝ) :
    canonicalEllipsoid (W p) ⊆ canonicalEllipsoid (W q) ↔
      (2 * p - 1) ^ 2 ≤ (2 * q - 1) ^ 2 := by
  constructor
  · intro h
    have hu : (![0, 0, 1] : V3) ∈ unitBall := by
      norm_num [unitBall, sqNorm, Fin.sum_univ_succ,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    have hx := h ⟨![0, 0, 1], hu, rfl⟩
    rcases hx with ⟨v, hv, heq⟩
    have h2 := congrFun heq 2
    simp [W_canonicalMap, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at h2
    change sqNorm v ≤ 1 at hv
    simp [sqNorm, Fin.sum_univ_succ] at hv
    have hv2 : (v 2) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have hmul := mul_nonneg (sq_nonneg (2 * q - 1)) (sub_nonneg.mpr hv2)
    rw [← h2]
    nlinarith
  · intro h x hx
    rcases hx with ⟨u, hu, rfl⟩
    by_cases hq : 2 * q - 1 = 0
    · have hp : 2 * p - 1 = 0 := by nlinarith [sq_nonneg (2 * p - 1)]
      refine ⟨u, hu, ?_⟩
      rw [W_canonicalMap, W_canonicalMap, hp, hq]
    · have hqpos : 0 < (2 * q - 1) ^ 2 := sq_pos_of_ne_zero hq
      have hr : ((2 * p - 1) / (2 * q - 1)) ^ 2 ≤ 1 := by
        rw [div_pow]
        exact (div_le_iff₀ hqpos).2 (by simpa using h)
      refine ⟨scaleZ ((2 * p - 1) / (2 * q - 1)) u,
        scaleZ_ball_of_sq_le_one hr hu, ?_⟩
      rw [W_canonicalMap, W_canonicalMap]
      ext i
      fin_cases i <;> simp [scaleZ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
      field_simp

theorem parametric_ellipsoid_subset_iff (p q : ℝ) :
    canonicalEllipsoid (W p) ⊆ canonicalEllipsoid (W q) ↔
      |2 * p - 1| ≤ |2 * q - 1| := by
  rw [parametric_ellipsoid_subset_iff_sq]
  exact sq_le_sq

theorem parametric_ellipsoid_equal_iff_sq (p q : ℝ) :
    canonicalEllipsoid (W p) = canonicalEllipsoid (W q) ↔
      (2 * p - 1) ^ 2 = (2 * q - 1) ^ 2 := by
  constructor
  · intro h
    exact le_antisymm
      ((parametric_ellipsoid_subset_iff_sq p q).mp h.subset)
      ((parametric_ellipsoid_subset_iff_sq q p).mp h.symm.subset)
  · intro h
    exact Set.Subset.antisymm
      ((parametric_ellipsoid_subset_iff_sq p q).mpr h.le)
      ((parametric_ellipsoid_subset_iff_sq q p).mpr h.symm.le)

theorem parametric_ellipsoid_equal_iff (p q : ℝ) :
    canonicalEllipsoid (W p) = canonicalEllipsoid (W q) ↔
      p = q ∨ p + q = 1 := by
  rw [parametric_ellipsoid_equal_iff_sq]
  constructor
  · intro h
    have hfactor : (p - q) * (p + q - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with hp | hq
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · rw [h]
    · have hp : p = 1 - q := by linarith
      rw [hp]
      ring

theorem parametric_ellipsoid_inside_ball {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : canonicalEllipsoid (W p) ⊆ unitBall := by
  rintro x ⟨u, hu, rfl⟩
  have hr : (2 * p - 1) ^ 2 ≤ 1 := by nlinarith
  have hb := scaleZ_ball_of_sq_le_one hr hu
  simpa [scaleZ, W_canonicalMap] using hb

theorem parametric_admissible {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    Admissible (canonicalEllipsoid (W p)) := by
  exact ⟨parametric_ellipsoid_inside_ball hp.le hp1, W p,
    W_witness hp hp1, W_canonical p, rfl⟩

lemma parametric_det_real (p : ℝ) :
    (Matrix.det (W p)).re = p ^ 3 * (p - 2) / 16 := by
  rw [det_W]
  norm_num [pow_succ, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]

lemma parametric_partialTranspose_det_real (p : ℝ) :
    (Matrix.det (partialTranspose (W p))).re = (p - 1) ^ 3 * (p + 1) / 16 := by
  rw [det_partialTranspose_W]
  norm_num [pow_succ, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]

theorem parametric_classD {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ClassD (W p) := by
  refine ⟨W_witness hp hp1.le, partialTranspose_witness hp hp1, ?_, ?_⟩
  · rw [parametric_det_real]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (pow_pos hp 3) (by linarith)) (by norm_num)
  · rw [parametric_partialTranspose_det_real]
    have hcube : (p - 1) ^ 3 < 0 := by
      have hpos : 0 < (1 - p) ^ 3 := pow_pos (by linarith) 3
      nlinarith
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos hcube (by linarith)) (by norm_num)

theorem family_zero_psd : PSD (W 0) := by
  have h : W 0 = Pplus := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [W, Pplus]
  rw [h]
  exact Pplus_psd

theorem family_one_partialTranspose_psd : PSD (partialTranspose (W 1)) := by
  refine ⟨partialTranspose_hermitian 1, ?_⟩
  intro z
  have hquad : quad (partialTranspose (W 1)) z =
      Complex.normSq (z 0 + z 3) / 2 := by
    rw [partialTranspose_W]
    simp [quad, Fin.sum_univ_succ, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
    ring
  rw [hquad]
  exact div_nonneg (Complex.normSq_nonneg _) (by norm_num)

lemma family_not_witness_of_psd {A : M4} (hpos : PSD A) : ¬ Witness A := by
  rintro ⟨_, _, _, z, hneg⟩
  have hnonneg := hpos.2 z
  linarith

theorem parametric_classD_iff {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ClassD (W p) ↔ 0 < p ∧ p < 1 := by
  constructor
  · intro h
    constructor
    · by_contra hn
      have heq : p = 0 := by linarith
      subst p
      exact family_not_witness_of_psd family_zero_psd h.1
    · by_contra hn
      have heq : p = 1 := by linarith
      subst p
      exact family_not_witness_of_psd family_one_partialTranspose_psd h.2.1
  · rintro ⟨h0, h1⟩
    exact parametric_classD h0 h1

/-- Complete Class C characterization on the closed parameter interval. -/
theorem parametric_classC_iff {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (Witness (W p) ∧ PSD (partialTranspose (W p))) ↔ p = 1 := by
  constructor
  · rintro ⟨hw, hpt⟩
    have hp0 : 0 < p := by
      by_contra hn
      have heq : p = 0 := by linarith
      subst p
      exact family_not_witness_of_psd family_zero_psd hw
    by_contra hne
    have hlt : p < 1 := lt_of_le_of_ne hp1 hne
    exact family_not_witness_of_psd hpt (partialTranspose_witness hp0 hlt)
  · intro heq
    subst p
    exact ⟨W_witness (by norm_num) (by norm_num), family_one_partialTranspose_psd⟩

/-- An infinite family of same-ellipsoid strict improvements. -/
theorem parametric_mirror_strictlyFiner {p : ℝ}
    (hp : 0 < p) (hphalf : p < 1 / 2) :
    StrictlyFiner (W (1 - p)) (W p) ∧
      canonicalEllipsoid (W (1 - p)) = canonicalEllipsoid (W p) := by
  exact ⟨parametric_strictlyFiner hp (by linarith) (by linarith),
    (equal_ellipsoids p).symm⟩

theorem parametric_not_optimal {p : ℝ} (hp : 0 < p) (hphalf : p < 1 / 2) :
    ¬ OptimalIn (canonicalEllipsoid (W p)) (W p) := by
  intro h
  apply h.2
  refine ⟨W (1 - p), ⟨W_witness (by linarith) (by linarith),
    W_canonical _, ?_⟩, (parametric_mirror_strictlyFiner hp hphalf).1⟩
  rw [equal_ellipsoids p]

theorem parametric_not_optimal_in_any_containing_set {p : ℝ}
    (hp : 0 < p) (hphalf : p < 1 / 2) (S : Set M4)
    (hmember : W (1 - p) ∈ S) : ¬ OptimalAmong S (W p) := by
  intro h
  exact h.2 ⟨W (1 - p), hmember, (parametric_mirror_strictlyFiner hp hphalf).1⟩

theorem infinite_ClassD_counterexamples {p : ℝ}
    (hp : 0 < p) (hphalf : p < 1 / 2) :
    Admissible (canonicalEllipsoid (W p)) ∧
      ClassD (W p) ∧ ClassD (W (1 - p)) ∧
      canonicalEllipsoid (W p) = canonicalEllipsoid (W (1 - p)) ∧
      StrictlyFiner (W (1 - p)) (W p) ∧
      ¬ OptimalIn (canonicalEllipsoid (W p)) (W p) := by
  exact ⟨parametric_admissible hp (by linarith),
    parametric_classD hp (by linarith), parametric_classD (by linarith) (by linarith),
    equal_ellipsoids p, (parametric_mirror_strictlyFiner hp hphalf).1,
    parametric_not_optimal hp hphalf⟩

theorem parametric_negative_chirality_iff (p : ℝ) :
    Matrix.det (correlationMatrix (W p)) < 0 ↔ p < 1 / 2 := by
  rw [W_correlation_det]
  constructor <;> intro h <;> linarith

theorem parametric_positive_chirality_iff (p : ℝ) :
    0 < Matrix.det (correlationMatrix (W p)) ↔ 1 / 2 < p := by
  rw [W_correlation_det]
  constructor <;> intro h <;> linarith

/-- Below zero chirality, stronger detectors have strictly smaller ellipsoids. -/
theorem decreasing_geometry_increasing_detection {p q : ℝ}
    (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1 / 2) :
    StrictlyFiner (W q) (W p) ∧
      canonicalEllipsoid (W q) ⊂ canonicalEllipsoid (W p) := by
  refine ⟨parametric_strictlyFiner hp (by linarith) hpq, ?_, ?_⟩
  · apply (parametric_ellipsoid_subset_iff_sq q p).mpr
    nlinarith
  · intro h
    have hle := (parametric_ellipsoid_subset_iff_sq p q).mp h
    nlinarith

/-- Above zero chirality, stronger detectors have strictly larger ellipsoids. -/
theorem increasing_geometry_increasing_detection {p q : ℝ}
    (hp : 1 / 2 ≤ p) (hpq : p < q) (hq : q ≤ 1) :
    StrictlyFiner (W q) (W p) ∧
      canonicalEllipsoid (W p) ⊂ canonicalEllipsoid (W q) := by
  refine ⟨parametric_strictlyFiner (by linarith) (by linarith) hpq, ?_, ?_⟩
  · apply (parametric_ellipsoid_subset_iff_sq p q).mpr
    nlinarith
  · intro h
    have hle := (parametric_ellipsoid_subset_iff_sq q p).mp h
    nlinarith

/-- The subset of the displayed witness family inside an axial target of
third semiaxis `r`. This does not denote all witnesses in the target. -/
def axialFamily (r : ℝ) : Set M4 :=
  {A | ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ |2 * p - 1| ≤ r ∧ A = W p}

theorem axialFamily_parameter_containment (p r : ℝ) (hr : 0 ≤ r) :
    canonicalEllipsoid (W p) ⊆ canonicalEllipsoid (W ((1 + r) / 2)) ↔
      |2 * p - 1| ≤ r := by
  rw [parametric_ellipsoid_subset_iff]
  have h : 2 * ((1 + r) / 2) - 1 = r := by ring
  rw [h, abs_of_nonneg hr]

theorem axialFamily_endpoint_member {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    W ((1 + r) / 2) ∈ axialFamily r := by
  refine ⟨(1 + r) / 2, by linarith, by linarith, ?_, rfl⟩
  have h : 2 * ((1 + r) / 2) - 1 = r := by ring
  rw [h, abs_of_nonneg hr]

/-- Complete relative optimality theorem within the parameterized family.
It is unconditional, but its surrounding set is the explicitly stated family. -/
theorem axialFamily_optimal_parameter_iff {p r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpr : |2 * p - 1| ≤ r) :
    OptimalAmong (axialFamily r) (W p) ↔ p = (1 + r) / 2 := by
  have hmax : p ≤ (1 + r) / 2 := by
    have hupper := (abs_le.mp hpr).2
    linarith
  constructor
  · intro h
    by_contra hne
    have hlt : p < (1 + r) / 2 := lt_of_le_of_ne hmax hne
    exact h.2 ⟨W ((1 + r) / 2), axialFamily_endpoint_member hr hr1,
      parametric_strictlyFiner hp (by linarith) hlt⟩
  · intro heq
    refine ⟨⟨p, hp, hp1, hpr, rfl⟩, ?_⟩
    rintro ⟨V, ⟨q, hq, hq1, hqr, rfl⟩, hstrict⟩
    have hlt := (parametric_strictlyFiner_iff hp (by linarith) hq
      (by linarith)).mp hstrict
    have hupper := (abs_le.mp hqr).2
    linarith

theorem axialFamily_unique_optimal {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (A : M4) :
    OptimalAmong (axialFamily r) A ↔ A = W ((1 + r) / 2) := by
  constructor
  · intro h
    rcases h.1 with ⟨p, hp, hp1, hpr, rfl⟩
    have hparam := (axialFamily_optimal_parameter_iff hr hr1 hp hp1 hpr).mp h
    rw [hparam]
  · intro hA
    subst A
    have hm := axialFamily_endpoint_member hr hr1
    rcases hm with ⟨p, hp, hp1, hpr, heq⟩
    have hpmax : p = (1 + r) / 2 := by
      have hmat := congrFun (congrFun heq 0) 0
      have hreal := congrArg Complex.re hmat
      norm_num [W, Complex.div_re, Complex.div_im] at hreal
      linarith
    subst p
    exact (axialFamily_optimal_parameter_iff hr hr1 hp hp1 hpr).mpr rfl

end
end EllipsoidCounterexample
