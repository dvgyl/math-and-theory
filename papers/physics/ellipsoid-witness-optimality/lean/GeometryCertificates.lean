import EllipsoidCounterexample
import Mathlib.Tactic.FieldSimp

/-!
# Exact semidefinite containment certificates

The main theorems prove the SOUNDNESS of the explicit 4×4 containment LMI,
including the fractional Bloch denominator and the support equations needed
for singular targets.  They do not assume the S-lemma and do not claim its
converse.  The outer set is defined by a support projector and a quadratic
metric.  Identifying these with a Moore--Penrose ellipsoid representation is a
separate linear-algebra fact in the report, not an unmarked Lean axiom here.
-/

namespace GeometryCertificates

noncomputable section

open Matrix

abbrev R3 := Fin 3 → ℝ
abbrev R4 := Fin 4 → ℝ
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

def dot3 (x y : R3) : ℝ := ∑ i, x i * y i
def normSq3 (x : R3) : ℝ := ∑ i, x i ^ 2
def mul3 (A : M3) (x : R3) : R3 := fun i => ∑ j, A i j * x j
def metric3 (H : M3) (x : R3) : ℝ := ∑ i, ∑ j, x i * H i j * x j
def quadratic4 (M : M4) (x : R4) : ℝ := ∑ i, ∑ j, x i * M i j * x j

/-- Real positive semidefiniteness, written without a spectral theorem. -/
def PSD4 (M : M4) : Prop := M.transpose = M ∧ ∀ x, 0 ≤ quadratic4 M x

def ball3 : Set R3 := {u | normSq3 u ≤ 1}
def denominator (b u : R3) : ℝ := 1 + dot3 b u

theorem normSq3_nonnegative (x : R3) : 0 ≤ normSq3 x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

theorem lagrange_identity (b u : R3) :
    normSq3 b * normSq3 u - dot3 b u ^ 2 =
      (b 0 * u 1 - b 1 * u 0) ^ 2 +
      (b 0 * u 2 - b 2 * u 0) ^ 2 +
      (b 1 * u 2 - b 2 * u 1) ^ 2 := by
  simp [normSq3, dot3, Fin.sum_univ_succ]
  ring

/-- The usual physical bound on Bob's Bloch vector makes every conditional
normalizing denominator strictly positive, including on the closed ball. -/
theorem denominator_positive_of_marginal_bound (b u : R3)
    (hb : normSq3 b < 1) (hu : u ∈ ball3) : 0 < denominator b u := by
  have hcs : dot3 b u ^ 2 ≤ normSq3 b * normSq3 u := by
    apply sub_nonneg.mp
    rw [lagrange_identity]
    exact add_nonneg
      (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hprod := mul_nonneg (normSq3_nonnegative b) (sub_nonneg.mpr hu)
  have hdot : dot3 b u ^ 2 < 1 := by nlinarith only [hb, hcs, hprod]
  unfold denominator
  nlinarith only [hdot]

def fractionalMap (a : R3) (T : M3) (b u : R3) : R3 :=
  fun i => (a i + mul3 T u i) / denominator b u

def fractionalEllipsoid (a : R3) (T : M3) (b : R3) : Set R3 :=
  fractionalMap a T b '' ball3

def deviationMatrix (T : M3) (c b : R3) : M3 := fun i j => T i j - c i * b j

/-- This support-and-metric set is the exact representation of a possibly
singular ellipsoid when `P = Q Q⁺` and `H = Q⁺`.  No such identification is
needed for the algebraic certificate theorem itself. -/
def metricEnclosure (c : R3) (H P : M3) : Set R3 :=
  {x | mul3 P (fun i => x i - c i) = (fun i => x i - c i) ∧
    metric3 H (fun i => x i - c i) ≤ 1}

def gram (D H : M3) (k l : Fin 3) : ℝ :=
  ∑ i, ∑ j, D i k * H i j * D j l

def rightCross (D H : M3) (h : R3) (k : Fin 3) : ℝ :=
  ∑ i, ∑ j, D i k * H i j * h j

def leftCross (D H : M3) (h : R3) (l : Fin 3) : ℝ :=
  ∑ i, ∑ j, h i * H i j * D j l

def rawCertificate (h : R3) (D : M3) (b : R3) (H : M3) (lam : ℝ) : M4 :=
  !![lam + b 0 * b 0 - gram D H 0 0,
     b 0 * b 1 - gram D H 0 1,
     b 0 * b 2 - gram D H 0 2,
     b 0 - rightCross D H h 0;
     b 1 * b 0 - gram D H 1 0,
     lam + b 1 * b 1 - gram D H 1 1,
     b 1 * b 2 - gram D H 1 2,
     b 1 - rightCross D H h 1;
     b 2 * b 0 - gram D H 2 0,
     b 2 * b 1 - gram D H 2 1,
     lam + b 2 * b 2 - gram D H 2 2,
     b 2 - rightCross D H h 2;
     b 0 - leftCross D H h 0,
     b 1 - leftCross D H h 1,
     b 2 - leftCross D H h 2,
     1 - metric3 H h - lam]

set_option maxHeartbeats 2000000 in
/-- The certificate matrix is exactly the homogenization of the quadratic
deficit after subtracting `lam * (1 - ‖u‖²)`.  No symmetry assumption on `H`
is needed for this polynomial identity. -/
theorem raw_certificate_identity (h b u : R3) (D H : M3) (lam : ℝ) :
    quadratic4 (rawCertificate h D b H lam) ![u 0, u 1, u 2, 1] =
      denominator b u ^ 2 - metric3 H (fun i => h i + mul3 D u i) -
        lam * (1 - normSq3 u) := by
  simp [quadratic4, rawCertificate, gram, rightCross, leftCross, metric3,
    mul3, denominator, dot3, normSq3, Fin.sum_univ_succ]
  ring

theorem certificate_implies_deficit_nonnegative
    (h b u : R3) (D H : M3) (lam : ℝ)
    (hlam : 0 ≤ lam) (hM : PSD4 (rawCertificate h D b H lam))
    (hu : u ∈ ball3) :
    metric3 H (fun i => h i + mul3 D u i) ≤ denominator b u ^ 2 := by
  have hquad := hM.2 ![u 0, u 1, u 2, 1]
  rw [raw_certificate_identity] at hquad
  have hpenalty : 0 ≤ lam * (1 - normSq3 u) :=
    mul_nonneg hlam (sub_nonneg.mpr hu)
  linarith

theorem metric_divide (H : M3) (x : R3) (d : ℝ) :
    metric3 H (fun i => x i / d) = metric3 H x / d ^ 2 := by
  simp [metric3, Fin.sum_univ_succ]
  ring

theorem mul3_divide (P : M3) (x : R3) (d : ℝ) :
    mul3 P (fun i => x i / d) = fun i => mul3 P x i / d := by
  ext i
  simp [mul3, Fin.sum_univ_succ]
  ring

theorem support_affine (P D : M3) (h u : R3)
    (hh : mul3 P h = h) (hD : P * D = D) :
    mul3 P (fun i => h i + mul3 D u i) = (fun i => h i + mul3 D u i) := by
  have hmul : mul3 P (fun i => h i + mul3 D u i) =
      (fun i => mul3 P h i + mul3 (P * D) u i) := by
    ext i
    simp [mul3, Matrix.mul_apply, Fin.sum_univ_succ]
    ring
  rw [hmul, hD, hh]

theorem fractional_deviation (a b c u : R3) (T : M3)
    (hd : denominator b u ≠ 0) :
    (fun i => fractionalMap a T b u i - c i) =
      (fun i => ((a i - c i) +
        mul3 (fun j k => T j k - c j * b k) u i) / denominator b u) := by
  ext i
  simp only [fractionalMap]
  apply (eq_div_iff hd).mpr
  rw [sub_mul, div_mul_cancel₀ _ hd]
  simp [mul3, denominator, dot3, Fin.sum_univ_succ]
  ring

/-- Exact soundness of the raw containment LMI with BOTH singular support
equations retained.  Denominator positivity is explicit; it is supplied by
the positive definite Bob marginal in the mathematical witness theorem. -/
theorem raw_LMI_implies_containment (a b c : R3) (T H P : M3)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hden : ∀ u ∈ ball3, 0 < denominator b u)
    (hsupport : mul3 P (fun i => a i - c i) = (fun i => a i - c i))
    (hcolumns : P * deviationMatrix T c b = deviationMatrix T c b)
    (hM : PSD4 (rawCertificate (fun i => a i - c i)
      (fun i j => T i j - c i * b j) b H lam)) :
    fractionalEllipsoid a T b ⊆ metricEnclosure c H P := by
  rintro x ⟨u, hu, rfl⟩
  have hd := hden u hu
  change mul3 P (fun i => fractionalMap a T b u i - c i) =
      (fun i => fractionalMap a T b u i - c i) ∧
    metric3 H (fun i => fractionalMap a T b u i - c i) ≤ 1
  rw [fractional_deviation a b c u T (ne_of_gt hd)]
  constructor
  · rw [mul3_divide]
    exact congrArg (fun x : R3 => fun i => x i / denominator b u)
      (support_affine P (deviationMatrix T c b) _ u hsupport hcolumns)
  · rw [metric_divide]
    apply (div_le_one (sq_pos_of_pos hd)).mpr
    exact certificate_implies_deficit_nonnegative _ b u _ H lam hlam hM hu

/-- A version whose denominator hypothesis is the directly checkable strict
quadratic bound `‖b‖² < 1`. -/
theorem raw_LMI_with_marginal_bound (a b c : R3) (T H P : M3)
    (lam : ℝ) (hlam : 0 ≤ lam) (hb : normSq3 b < 1)
    (hsupport : mul3 P (fun i => a i - c i) = (fun i => a i - c i))
    (hcolumns : P * deviationMatrix T c b = deviationMatrix T c b)
    (hM : PSD4 (rawCertificate (fun i => a i - c i)
      (fun i j => T i j - c i * b j) b H lam)) :
    fractionalEllipsoid a T b ⊆ metricEnclosure c H P :=
  raw_LMI_implies_containment a b c T H P lam hlam
    (fun u hu => denominator_positive_of_marginal_bound b u hb hu)
    hsupport hcolumns hM

/-- The canonical containment LMI is the `b = 0` special case. -/
theorem canonical_LMI_implies_containment (a c : R3) (T H P : M3)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hsupport : mul3 P (fun i => a i - c i) = (fun i => a i - c i))
    (hcolumns : P * T = T)
    (hM : PSD4 (rawCertificate (fun i => a i - c i) T 0 H lam)) :
    (fun u => fun i => a i + mul3 T u i) '' ball3 ⊆ metricEnclosure c H P := by
  have hDz : deviationMatrix T c 0 = T := by
    ext i j
    simp [deviationMatrix]
  have h := raw_LMI_implies_containment a 0 c T H P lam hlam
    (by intro u hu; norm_num [denominator, dot3]) hsupport
    (by rw [hDz]; exact hcolumns) (by simpa using hM)
  have hmap : fractionalMap a T (0 : R3) = (fun u => fun i => a i + mul3 T u i) := by
    funext u i
    simp [fractionalMap, denominator, dot3]
  simpa only [fractionalEllipsoid, hmap] using h

def planarMetric : M3 := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
def offPlanePoint : R3 := ![0, 0, 1]

/-- A certificate of the singular-target pitfall: the pseudoinverse quadratic
inequality alone accepts a point one unit off the plane.  The support equation
rejects it. -/
theorem support_condition_is_essential :
    metric3 planarMetric offPlanePoint ≤ 1 ∧
    offPlanePoint ∉ metricEnclosure 0 planarMetric planarMetric := by
  constructor
  · norm_num [metric3, planarMetric, offPlanePoint, Fin.sum_univ_succ]
  · intro h
    have h2 := congrFun h.1 2
    norm_num [mul3, planarMetric, offPlanePoint, Fin.sum_univ_succ,
      Matrix.cons_val_two] at h2

/-- A centered axis-aligned ellipsoid, with zero semiaxes allowed. -/
def axisEllipsoid (r : R3) : Set R3 :=
  (fun u => fun i => r i * u i) '' ball3

def unitAxis (i : Fin 3) : R3 := fun j => if j = i then 1 else 0

theorem unitAxis_mem_ball (i : Fin 3) : unitAxis i ∈ ball3 := by
  fin_cases i <;> norm_num [unitAxis, ball3, normSq3, Fin.sum_univ_succ, Fin.ext_iff]

theorem ball_coordinate_square_le_one (v : R3) (hv : v ∈ ball3) (i : Fin 3) :
    (v i) ^ 2 ≤ 1 := by
  change normSq3 v ≤ 1 at hv
  simp [normSq3, Fin.sum_univ_succ] at hv
  fin_cases i
  · change (v 0) ^ 2 ≤ 1
    nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
  · change (v 1) ^ 2 ≤ 1
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 2)]
  · change (v 2) ^ 2 ≤ 1
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

/-- A complete containment equivalence for diagonal ellipsoids, including
disks, line segments, and points.  Unlike the general LMI theorem above, both
directions are formalized with no external geometric hypothesis. -/
theorem diagonal_containment_iff (r s : R3)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ i, 0 ≤ s i) :
    axisEllipsoid r ⊆ axisEllipsoid s ↔ ∀ i, r i ≤ s i := by
  constructor
  · intro hsub i
    have hx : (fun j => r j * unitAxis i j) ∈ axisEllipsoid r :=
      ⟨unitAxis i, unitAxis_mem_ball i, rfl⟩
    obtain ⟨v, hv, heq⟩ := hsub hx
    have hvi : v i ≤ 1 := by
      have hv2 := ball_coordinate_square_le_one v hv i
      nlinarith
    have hcoord : s i * v i = r i := by
      simpa [unitAxis] using congrFun heq i
    rw [← hcoord]
    simpa using mul_le_mul_of_nonneg_left hvi (hs i)
  · intro hle x hx
    obtain ⟨u, hu, rfl⟩ := hx
    let v : R3 := fun i => (r i / s i) * u i
    have hratio : ∀ i, 0 ≤ r i / s i ∧ r i / s i ≤ 1 := by
      intro i
      refine ⟨div_nonneg (hr i) (hs i), ?_⟩
      by_cases hsi : s i = 0
      · simp [hsi]
      · exact (div_le_one (lt_of_le_of_ne (hs i) (Ne.symm hsi))).mpr (hle i)
    have hsq : ∀ i, (v i) ^ 2 ≤ (u i) ^ 2 := by
      intro i
      obtain ⟨h0, h1⟩ := hratio i
      have hq : (r i / s i) ^ 2 ≤ 1 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hq (sq_nonneg (u i))
      simpa only [v, mul_pow, one_mul] using hm
    have hv : v ∈ ball3 := by
      change normSq3 v ≤ 1
      change normSq3 u ≤ 1 at hu
      have hnorm : normSq3 v ≤ normSq3 u := Finset.sum_le_sum (fun i _ => hsq i)
      exact hnorm.trans hu
    refine ⟨v, hv, ?_⟩
    ext i
    change s i * ((r i / s i) * u i) = r i * u i
    by_cases hsi : s i = 0
    · have hri : r i = 0 := by have h := hle i; have h0 := hr i; linarith
      simp [hsi, hri]
    · field_simp

#print axioms raw_certificate_identity
#print axioms raw_LMI_implies_containment
#print axioms raw_LMI_with_marginal_bound
#print axioms canonical_LMI_implies_containment
#print axioms support_condition_is_essential
#print axioms diagonal_containment_iff

end

end GeometryCertificates
