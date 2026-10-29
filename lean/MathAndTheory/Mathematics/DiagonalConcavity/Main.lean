module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

/-!
# Lachaume's diagonal concavity conjecture: exact counterexample

AI-generated formalization for Dev D. Goyal, October 2026.
The functions below explicitly enumerate all elementary symmetric sums in four variables.
The principal result uses the actual `ConcaveOn` predicate and real fourth roots.
No analytic implication is installed as an axiom or assumed as a hypothesis.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace MathAndTheory.DiagonalConcavity

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

abbrev V4 := Fin 4 → ℝ

@[expose] def sigma1 (x : V4) : ℝ := x 0 + x 1 + x 2 + x 3
@[expose] def sigma2 (x : V4) : ℝ :=
  x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 1 * x 2 + x 1 * x 3 + x 2 * x 3
@[expose] def sigma3 (x : V4) : ℝ :=
  x 0 * x 1 * x 2 + x 0 * x 1 * x 3 + x 0 * x 2 * x 3 + x 1 * x 2 * x 3
@[expose] def sigma4 (x : V4) : ℝ := x 0 * x 1 * x 2 * x 3

@[expose] def family (M : ℝ) (x : V4) : ℝ :=
  1 + M * sigma1 x + sigma2 x + M * sigma3 x + sigma4 x

@[expose] def positiveOrthant : Set V4 := {x | ∀ i, 0 < x i}
@[expose] def fourthRoot (a : ℝ) : ℝ := a ^ (1 / 4 : ℝ)
@[expose] def rootedFamily (M : ℝ) (x : V4) : ℝ := fourthRoot (family M x)

@[expose] def diagonal (M t : ℝ) : ℝ := 1 + 4*M*t + 6*t^2 + 4*M*t^3 + t^4
@[expose] def diagonalD1 (M t : ℝ) : ℝ := 4*M + 12*t + 12*M*t^2 + 4*t^3
@[expose] def diagonalD2 (M t : ℝ) : ℝ := 12 + 24*M*t + 12*t^2

theorem family_diagonal (M t : ℝ) : family M (fun _ => t) = diagonal M t := by
  dsimp [family, sigma1, sigma2, sigma3, sigma4, diagonal]
  ring

theorem diagonal_curvature_identity (M t : ℝ) :
    3*(diagonalD1 M t)^2 - 4*diagonal M t*diagonalD2 M t =
      48*(M^2-1)*(t^2-1)^2 := by
  dsimp [diagonal, diagonalD1, diagonalD2]
  ring

theorem diagonal_positive {M t : ℝ} (hM : 0 < M) (ht : 0 < t) :
    0 < diagonal M t := by
  dsimp [diagonal]
  positivity

theorem diagonal_hasDerivAt (M t : ℝ) :
    HasDerivAt (diagonal M) (diagonalD1 M t) t := by
  convert ((((hasDerivAt_const t (1 : ℝ)).add
    ((hasDerivAt_id t).const_mul (4*M))).add
    (((hasDerivAt_id t).pow 2).const_mul 6)).add
    (((hasDerivAt_id t).pow 3).const_mul (4*M))).add
    ((hasDerivAt_id t).pow 4) using 1
  · ext x
    simp only [diagonal, Pi.add_apply, Pi.pow_apply, id_eq]
  · norm_num [diagonalD1]
    ring

theorem diagonalD1_hasDerivAt (M t : ℝ) :
    HasDerivAt (diagonalD1 M) (diagonalD2 M t) t := by
  convert (((hasDerivAt_const t (4*M)).add
    ((hasDerivAt_id t).const_mul 12)).add
    (((hasDerivAt_id t).pow 2).const_mul (12*M))).add
    (((hasDerivAt_id t).pow 3).const_mul 4) using 1
  · ext x
    simp only [diagonalD1, Pi.add_apply, Pi.pow_apply, id_eq]
  · norm_num [diagonalD2]
    ring

@[expose] def rootD1 (q q1 : ℝ → ℝ) (t : ℝ) : ℝ := q1 t * (1/4) * q t ^ (-3/4 : ℝ)
@[expose] def rootD2 (q q1 q2 : ℝ → ℝ) (t : ℝ) : ℝ :=
  q t ^ (-7/4 : ℝ) / 16 * (4*q t*q2 t - 3*(q1 t)^2)

theorem fourthRoot_hasDerivAt {q q1 : ℝ → ℝ} {t : ℝ}
    (hq : HasDerivAt q (q1 t) t) (hp : 0 < q t) :
    HasDerivAt (fun s => fourthRoot (q s)) (rootD1 q q1 t) t := by
  convert hq.rpow_const (p := (1/4 : ℝ)) (Or.inl (ne_of_gt hp)) using 1
  all_goals norm_num [fourthRoot, rootD1]

theorem rootD1_hasDerivAt {q q1 q2 : ℝ → ℝ} {t : ℝ}
    (hq : HasDerivAt q (q1 t) t) (hq1 : HasDerivAt q1 (q2 t) t)
    (hp : 0 < q t) :
    HasDerivAt (rootD1 q q1) (rootD2 q q1 q2 t) t := by
  have hr : q t ^ (-3/4 : ℝ) = q t ^ (-7/4 : ℝ) * q t := by
    calc
      q t ^ (-3/4 : ℝ) = q t ^ ((-7/4 : ℝ) + 1) := by norm_num
      _ = q t ^ (-7/4 : ℝ) * q t := by rw [Real.rpow_add hp, Real.rpow_one]
  have hd := (hq1.mul_const (1/4 : ℝ)).mul
    (hq.rpow_const (p := (-3/4 : ℝ)) (Or.inl (ne_of_gt hp)))
  convert hd using 1
  · rfl
  · dsimp [rootD2]
    norm_num at *
    rw [hr]
    ring

theorem diagonal_concave_of_one_le {M : ℝ} (hM : 1 ≤ M) :
    ConcaveOn ℝ (Ioi 0) (fun t => fourthRoot (diagonal M t)) := by
  have hMp : 0 < M := lt_of_lt_of_le (by norm_num) hM
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi (0 : ℝ))
    (f' := rootD1 (diagonal M) (diagonalD1 M))
    (f'' := rootD2 (diagonal M) (diagonalD1 M) (diagonalD2 M)) ?_ ?_ ?_ ?_
  · intro t ht
    exact (fourthRoot_hasDerivAt (diagonal_hasDerivAt M t)
      (diagonal_positive hMp ht)).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
    exact (fourthRoot_hasDerivAt (diagonal_hasDerivAt M t)
      (diagonal_positive hMp ht')).hasDerivWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
    exact (rootD1_hasDerivAt (diagonal_hasDerivAt M t)
      (diagonalD1_hasDerivAt M t) (diagonal_positive hMp ht')).hasDerivWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
    have hM2 : 0 ≤ M^2-1 := by nlinarith
    have hprod : 0 ≤ 48*(M^2-1)*(t^2-1)^2 := by positivity
    have hnum : 4*diagonal M t*diagonalD2 M t - 3*(diagonalD1 M t)^2 ≤ 0 := by
      linarith [diagonal_curvature_identity M t]
    exact mul_nonpos_of_nonneg_of_nonpos
      (div_pos (Real.rpow_pos_of_pos (diagonal_positive hMp ht') _) (by norm_num)).le hnum

@[expose] def pointMinus : V4 := ![3/2, 3/2, 1/4, 1/4]
@[expose] def pointPlus : V4 := ![5/2, 5/2, 3/4, 3/4]
@[expose] def pointCenter : V4 := ![2, 2, 1/2, 1/2]

theorem pointMinus_positive : pointMinus ∈ positiveOrthant := by
  intro i
  fin_cases i <;> norm_num [pointMinus]

theorem pointPlus_positive : pointPlus ∈ positiveOrthant := by
  intro i
  fin_cases i <;> norm_num [pointPlus]

theorem points_midpoint : (1/2 : ℝ) • pointMinus + (1/2 : ℝ) • pointPlus = pointCenter := by
  ext i
  fin_cases i <;> norm_num [pointMinus, pointPlus, pointCenter]

theorem family_pointMinus : family 2 pointMinus = 933/64 := by
  norm_num [family, sigma1, sigma2, sigma3, sigma4, pointMinus]

theorem family_pointPlus : family 2 pointPlus = 3597/64 := by
  norm_num [family, sigma1, sigma2, sigma3, sigma4, pointPlus]

theorem family_pointCenter : family 2 pointCenter = 121/4 := by
  norm_num [family, sigma1, sigma2, sigma3, sigma4, pointCenter]

theorem fourthRoot_pow {r : ℝ} (hr : 0 ≤ r) : fourthRoot (r^4) = r := by
  simpa only [fourthRoot, one_div, Nat.cast_ofNat] using
    (Real.pow_rpow_inv_natCast (n := 4) hr (by norm_num : (4 : ℕ) ≠ 0))

theorem fourthRoot_lower {x r : ℝ} (hr : 0 ≤ r) (h : r^4 < x) : r < fourthRoot x := by
  have hh := Real.rpow_lt_rpow (pow_nonneg hr 4) h (by norm_num : (0 : ℝ) < 1/4)
  change fourthRoot (r^4) < fourthRoot x at hh
  rwa [fourthRoot_pow hr] at hh

theorem fourthRoot_upper {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (h : x < r^4) :
    fourthRoot x < r := by
  have hh := Real.rpow_lt_rpow hx h (by norm_num : (0 : ℝ) < 1/4)
  change fourthRoot x < fourthRoot (r^4) at hh
  rwa [fourthRoot_pow hr] at hh

theorem midpoint_strict_violation :
    rootedFamily 2 pointCenter <
      (1/2 : ℝ) * rootedFamily 2 pointMinus + (1/2 : ℝ) * rootedFamily 2 pointPlus := by
  have hm : (977/500 : ℝ) < fourthRoot (933/64) :=
    fourthRoot_lower (by norm_num) (by norm_num)
  have hp : (1369/500 : ℝ) < fourthRoot (3597/64) :=
    fourthRoot_lower (by norm_num) (by norm_num)
  have hc : fourthRoot (121/4) < (4691/2000 : ℝ) :=
    fourthRoot_upper (by norm_num) (by norm_num) (by norm_num)
  simp only [rootedFamily, family_pointMinus, family_pointPlus, family_pointCenter]
  linarith

theorem family_two_not_concave : ¬ ConcaveOn ℝ positiveOrthant (rootedFamily 2) := by
  intro hc
  have h := hc.2 pointMinus_positive pointPlus_positive
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  rw [points_midpoint] at h
  simp only [smul_eq_mul] at h
  exact (not_lt_of_ge h) midpoint_strict_violation

/-- A semantic disproof: diagonal concavity holds, and full concavity fails. -/
theorem diagonal_concavity_counterexample :
    ConcaveOn ℝ (Ioi 0) (fun t => rootedFamily 2 (fun _ => t)) ∧
      ¬ ConcaveOn ℝ positiveOrthant (rootedFamily 2) := by
  constructor
  · simpa only [rootedFamily, family_diagonal] using
      (diagonal_concave_of_one_le (M := 2) (by norm_num))
  · exact family_two_not_concave

/-- Concavity forces a nonpositive second derivative at every interior point. -/
theorem second_nonpos_of_concave {D : Set ℝ} (hD : IsOpen D)
    {f f1 : ℝ → ℝ} {x f2 : ℝ} (hc : ConcaveOn ℝ D f)
    (hf : ∀ t ∈ D, HasDerivAt f (f1 t) t) (hx : x ∈ D)
    (hf2 : HasDerivAt f1 f2 x) : f2 ≤ 0 := by
  have ha : AntitoneOn f1 D := by
    intro u hu v hv huv
    have h := hc.antitoneOn_deriv (fun t ht => (hf t ht).differentiableAt) hu hv huv
    simpa only [(hf u hu).deriv, (hf v hv).deriv] using h
  have ht : Tendsto (fun t : ℝ => x + t) (𝓝[>] 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds.add tendsto_id).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t ∈ D := ht.eventually (hD.mem_nhds hx)
  apply le_of_tendsto hf2.tendsto_slope_zero_right
  filter_upwards [he, self_mem_nhdsWithin] with t hxt htpos
  have ht0 : 0 ≤ t := le_of_lt htpos
  have hle : f1 (x+t) ≤ f1 x := ha hx hxt (by linarith)
  simpa only [smul_eq_mul] using mul_nonpos_of_nonneg_of_nonpos
    (inv_nonneg.mpr ht0) (sub_nonpos.mpr hle)

theorem diagonal_concave_iff {M : ℝ} (hM : 0 < M) :
    ConcaveOn ℝ (Ioi 0) (fun t => fourthRoot (diagonal M t)) ↔ 1 ≤ M := by
  constructor
  · intro hc
    have hn := second_nonpos_of_concave isOpen_Ioi hc
      (fun t ht => fourthRoot_hasDerivAt (diagonal_hasDerivAt M t)
        (diagonal_positive hM ht)) (by norm_num : (2 : ℝ) ∈ Ioi 0)
      (rootD1_hasDerivAt (diagonal_hasDerivAt M 2)
        (diagonalD1_hasDerivAt M 2) (diagonal_positive hM (by norm_num)))
    have hfac : 0 < diagonal M 2 ^ (-7/4 : ℝ) / 16 := by
      exact div_pos (Real.rpow_pos_of_pos (diagonal_positive hM (by norm_num)) _) (by norm_num)
    have hnum : 4*diagonal M 2*diagonalD2 M 2 - 3*(diagonalD1 M 2)^2 ≤ 0 :=
      nonpos_of_mul_nonpos_right hn hfac
    have hid := diagonal_curvature_identity M 2
    norm_num at hid
    nlinarith
  · exact diagonal_concave_of_one_le

@[expose] def witnessLine (s : ℝ) : V4 := ![2+2*s, 2+2*s, 1/2+s, 1/2+s]
@[expose] def linePolynomial (M s : ℝ) : ℝ :=
  4*s^4 + (12*M+12)*s^3 + (28*M+26)*s^2 + 27*(M+1)*s + (40*M+41)/4
@[expose] def lineD1 (M s : ℝ) : ℝ :=
  16*s^3 + (36*M+36)*s^2 + (56*M+52)*s + 27*(M+1)
@[expose] def lineD2 (M s : ℝ) : ℝ := 48*s^2 + (72*M+72)*s + 56*M+52

theorem family_witnessLine (M s : ℝ) : family M (witnessLine s) = linePolynomial M s := by
  norm_num [family, sigma1, sigma2, sigma3, sigma4, witnessLine, linePolynomial]
  ring

theorem witnessLine_positive {s : ℝ} (hs : -1/2 < s) :
    witnessLine s ∈ positiveOrthant := by
  intro i
  fin_cases i <;> norm_num [witnessLine] <;> linarith

theorem family_positive {M : ℝ} {x : V4} (hM : 0 < M) (hx : x ∈ positiveOrthant) :
    0 < family M x := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  dsimp [family, sigma1, sigma2, sigma3, sigma4]
  positivity

theorem linePolynomial_positive {M s : ℝ} (hM : 0 < M) (hs : -1/2 < s) :
    0 < linePolynomial M s := by
  rw [← family_witnessLine]
  exact family_positive hM (witnessLine_positive hs)

theorem linePolynomial_hasDerivAt (M s : ℝ) :
    HasDerivAt (linePolynomial M) (lineD1 M s) s := by
  convert ((((((hasDerivAt_id s).pow 4).const_mul 4).add
    (((hasDerivAt_id s).pow 3).const_mul (12*M+12))).add
    (((hasDerivAt_id s).pow 2).const_mul (28*M+26))).add
    ((hasDerivAt_id s).const_mul (27*(M+1)))).add
    (hasDerivAt_const s ((40*M+41)/4)) using 1
  · ext x
    simp only [linePolynomial, Pi.add_apply, Pi.pow_apply, id_eq]
  · norm_num [lineD1]
    ring

theorem lineD1_hasDerivAt (M s : ℝ) :
    HasDerivAt (lineD1 M) (lineD2 M s) s := by
  convert (((((hasDerivAt_id s).pow 3).const_mul 16).add
    (((hasDerivAt_id s).pow 2).const_mul (36*M+36))).add
    ((hasDerivAt_id s).const_mul (56*M+52))).add
    (hasDerivAt_const s (27*(M+1))) using 1
  · ext x
    simp only [lineD1, Pi.add_apply, Pi.pow_apply, id_eq]
  · norm_num [lineD2]
    ring

theorem line_curvature_identity (M : ℝ) :
    4*linePolynomial M 0*lineD2 M 0 - 3*(lineD1 M 0)^2 = (M-1)*(53*M+55) := by
  dsimp [linePolynomial, lineD1, lineD2]
  ring

theorem positive_line_curvature {M : ℝ} (hM : 1 < M) :
    0 < rootD2 (linePolynomial M) (lineD1 M) (lineD2 M) 0 := by
  dsimp [rootD2]
  rw [line_curvature_identity]
  have hMp : 0 < M := by linarith
  have hp := linePolynomial_positive hMp (by norm_num : (-1/2 : ℝ) < 0)
  exact mul_pos (div_pos (Real.rpow_pos_of_pos hp _) (by norm_num))
    (mul_pos (by linarith) (by linarith))

theorem positive_directional_second_derivative {M : ℝ} (hM : 1 < M) :
    0 < deriv (deriv (fun s => rootedFamily M (witnessLine s))) 0 := by
  have hMp : 0 < M := by linarith
  have he : deriv (fun s => fourthRoot (linePolynomial M s)) =ᶠ[𝓝 (0 : ℝ)]
      rootD1 (linePolynomial M) (lineD1 M) := by
    filter_upwards [Ioi_mem_nhds (show (-1/2 : ℝ) < 0 by norm_num)] with s hs
    exact (fourthRoot_hasDerivAt (linePolynomial_hasDerivAt M s)
      (linePolynomial_positive hMp hs)).deriv
  have heq := he.deriv_eq
  rw [(rootD1_hasDerivAt (linePolynomial_hasDerivAt M 0) (lineD1_hasDerivAt M 0)
    (linePolynomial_positive hMp (by norm_num))).deriv] at heq
  have hp := positive_line_curvature hM
  rw [← heq] at hp
  simpa only [rootedFamily, family_witnessLine] using hp

theorem witnessLine_affine (u v a b : ℝ) (hab : a+b=1) :
    a • witnessLine u + b • witnessLine v = witnessLine (a*u+b*v) := by
  ext i
  fin_cases i <;> norm_num [witnessLine] <;> nlinarith

theorem line_concave_of_family_concave {M : ℝ}
    (hc : ConcaveOn ℝ positiveOrthant (rootedFamily M)) :
    ConcaveOn ℝ (Ioi (-1/2)) (fun s => fourthRoot (linePolynomial M s)) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro u hu v hv a b ha hb hab
  have h := hc.2 (witnessLine_positive hu) (witnessLine_positive hv) ha hb hab
  rw [witnessLine_affine u v a b hab] at h
  simpa only [rootedFamily, family_witnessLine, smul_eq_mul] using h

theorem family_not_concave_of_one_lt {M : ℝ} (hM : 1 < M) :
    ¬ ConcaveOn ℝ positiveOrthant (rootedFamily M) := by
  intro hc
  have hMp : 0 < M := by linarith
  have hn := second_nonpos_of_concave isOpen_Ioi (line_concave_of_family_concave hc)
    (fun s hs => fourthRoot_hasDerivAt (linePolynomial_hasDerivAt M s)
      (linePolynomial_positive hMp hs)) (by norm_num : (0 : ℝ) ∈ Ioi (-1/2))
    (rootD1_hasDerivAt (linePolynomial_hasDerivAt M 0)
      (lineD1_hasDerivAt M 0) (linePolynomial_positive hMp (by norm_num)))
  exact (not_lt_of_ge hn) (positive_line_curvature hM)

theorem positiveOrthant_convex : Convex ℝ positiveOrthant := by
  intro x hx y hy a b ha hb hab i
  change 0 < a*x i+b*y i
  rcases lt_or_eq_of_le ha with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hx i)) (mul_nonneg hb (hy i).le)
  · have hb' : b = 1 := by linarith
    simp only [← ha', hb', zero_mul, one_mul, zero_add]
    exact hy i

@[expose] def geom4 (x : V4) : ℝ := fourthRoot (sigma4 x)

theorem geom4_positive {x : V4} (hx : x ∈ positiveOrthant) : 0 < geom4 x := by
  exact Real.rpow_pos_of_pos (mul_pos (mul_pos (mul_pos (hx 0) (hx 1)) (hx 2)) (hx 3)) _

theorem geom4_product {x : V4} (hx : x ∈ positiveOrthant) :
    geom4 x = fourthRoot (x 0) * fourthRoot (x 1) * fourthRoot (x 2) * fourthRoot (x 3) := by
  dsimp [geom4, sigma4, fourthRoot]
  rw [Real.mul_rpow (mul_nonneg (mul_nonneg (hx 0).le (hx 1).le) (hx 2).le) (hx 3).le,
    Real.mul_rpow (mul_nonneg (hx 0).le (hx 1).le) (hx 2).le,
    Real.mul_rpow (hx 0).le (hx 1).le]

theorem geom4_amgm {x : V4} (hx : x ∈ positiveOrthant) :
    geom4 x ≤ (x 0)/4 + (x 1)/4 + (x 2)/4 + (x 3)/4 := by
  rw [geom4_product hx]
  have h := Real.geom_mean_le_arith_mean4_weighted
    (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num : (0 : ℝ) ≤ 1/4)
    (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num : (0 : ℝ) ≤ 1/4)
    (hx 0).le (hx 1).le (hx 2).le (hx 3).le (by norm_num)
  convert h using 1
  dsimp [fourthRoot]
  ring

theorem geom4_div {x z : V4} (hx : x ∈ positiveOrthant) (hz : z ∈ positiveOrthant) :
    geom4 (fun i => x i / z i) = geom4 x / geom4 z := by
  have hp : sigma4 (fun i => x i / z i) = sigma4 x / sigma4 z := by
    dsimp [sigma4]
    field_simp
  dsimp [geom4, fourthRoot]
  rw [hp]
  exact Real.div_rpow
    (mul_nonneg (mul_nonneg (mul_nonneg (hx 0).le (hx 1).le) (hx 2).le) (hx 3).le)
    (mul_nonneg (mul_nonneg (mul_nonneg (hz 0).le (hz 1).le) (hz 2).le) (hz 3).le) _

/-- Concavity of the four-variable geometric mean, derived from AM--GM. -/
theorem geom4_concave : ConcaveOn ℝ positiveOrthant geom4 := by
  refine ⟨positiveOrthant_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  let z : V4 := a • x + b • y
  have hz : z ∈ positiveOrthant := positiveOrthant_convex hx hy ha hb hab
  have hxr : (fun i => x i / z i) ∈ positiveOrthant := fun i => div_pos (hx i) (hz i)
  have hyr : (fun i => y i / z i) ∈ positiveOrthant := fun i => div_pos (hy i) (hz i)
  have hxa := geom4_amgm hxr
  have hya := geom4_amgm hyr
  rw [geom4_div hx hz] at hxa
  rw [geom4_div hy hz] at hya
  have hzratio (i : Fin 4) : a*(x i/z i)+b*(y i/z i)=1 := by
    calc
      a*(x i/z i)+b*(y i/z i) = (a*x i+b*y i)/z i := by ring
      _ = z i / z i := rfl
      _ = 1 := div_self (ne_of_gt (hz i))
  have hn : a*((x 0/z 0)/4+(x 1/z 1)/4+(x 2/z 2)/4+(x 3/z 3)/4) +
      b*((y 0/z 0)/4+(y 1/z 1)/4+(y 2/z 2)/4+(y 3/z 3)/4) = 1 := by
    calc
      _ = (a*(x 0/z 0)+b*(y 0/z 0))/4 +
          (a*(x 1/z 1)+b*(y 1/z 1))/4 +
          (a*(x 2/z 2)+b*(y 2/z 2))/4 +
          (a*(x 3/z 3)+b*(y 3/z 3))/4 := by ring
      _ = 1 := by rw [hzratio 0, hzratio 1, hzratio 2, hzratio 3]; norm_num
  have hsum : a*(geom4 x/geom4 z)+b*(geom4 y/geom4 z) ≤ 1 := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hxa ha) (mul_le_mul_of_nonneg_left hya hb)
    exact h.trans_eq hn
  have hdiv : (a*geom4 x+b*geom4 y)/geom4 z ≤ 1 := by
    calc
      _ = a*(geom4 x/geom4 z)+b*(geom4 y/geom4 z) := by ring
      _ ≤ 1 := hsum
  simpa only [smul_eq_mul, one_mul] using (div_le_iff₀ (geom4_positive hz)).mp hdiv

theorem family_one_product (x : V4) :
    family 1 x = (1+x 0)*(1+x 1)*(1+x 2)*(1+x 3) := by
  dsimp [family, sigma1, sigma2, sigma3, sigma4]
  ring

theorem rootedFamily_one_geom4 (x : V4) :
    rootedFamily 1 x = geom4 (fun i => 1+x i) := by
  dsimp [rootedFamily, geom4, sigma4]
  rw [family_one_product]

theorem family_one_concave : ConcaveOn ℝ positiveOrthant (rootedFamily 1) := by
  refine ⟨positiveOrthant_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (fun i => 1+x i) ∈ positiveOrthant := fun i => add_pos zero_lt_one (hx i)
  have hy' : (fun i => 1+y i) ∈ positiveOrthant := fun i => add_pos zero_lt_one (hy i)
  have h := geom4_concave.2 hx' hy' ha hb hab
  have he : (fun i => 1+(a • x + b • y) i) =
      a • (fun i => 1+x i) + b • (fun i => 1+y i) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  simp only [rootedFamily_one_geom4]
  rw [he]
  exact h

theorem diagonal_concave_of_family_concave {M : ℝ}
    (hc : ConcaveOn ℝ positiveOrthant (rootedFamily M)) :
    ConcaveOn ℝ (Ioi 0) (fun t => fourthRoot (diagonal M t)) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro u hu v hv a b ha hb hab
  have h := hc.2 (show (fun _ : Fin 4 => u) ∈ positiveOrthant from fun _ => hu)
    (show (fun _ : Fin 4 => v) ∈ positiveOrthant from fun _ => hv) ha hb hab
  simpa only [rootedFamily, family_diagonal, Pi.add_def, Pi.smul_def, smul_eq_mul] using h

/-- The complete one-parameter classification on the positive orthant. -/
theorem family_concave_iff {M : ℝ} (hM : 0 < M) :
    ConcaveOn ℝ positiveOrthant (rootedFamily M) ↔ M = 1 := by
  constructor
  · intro hc
    have hge : 1 ≤ M := (diagonal_concave_iff hM).mp (diagonal_concave_of_family_concave hc)
    have hle : M ≤ 1 := le_of_not_gt (fun h => family_not_concave_of_one_lt h hc)
    exact le_antisymm hle hge
  · rintro rfl
    exact family_one_concave

/-- The library's elementary symmetric function, applied to the coordinate multiset. -/
@[expose] def elementary (k : ℕ) (x : V4) : ℝ :=
  ((Finset.univ : Finset (Fin 4)).val.map x).esymm k

theorem elementary_zero (x : V4) : elementary 0 x = 1 := by
  rw [elementary, Finset.esymm_map_val]
  simp

theorem elementary_one (x : V4) : elementary 1 x = sigma1 x := by
  have hs : (Finset.univ : Finset (Fin 4)).powersetCard 1 = {{0}, {1}, {2}, {3}} := by decide
  rw [elementary, Finset.esymm_map_val, hs]
  simp (disch := decide) [sigma1, Finset.sum_insert, Finset.prod_insert]
  ring

theorem elementary_two (x : V4) : elementary 2 x = sigma2 x := by
  have hs : (Finset.univ : Finset (Fin 4)).powersetCard 2 =
      {{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}} := by decide
  rw [elementary, Finset.esymm_map_val, hs]
  simp (disch := decide) [sigma2, Finset.sum_insert, Finset.prod_insert]
  ring

theorem elementary_three (x : V4) : elementary 3 x = sigma3 x := by
  have hs : (Finset.univ : Finset (Fin 4)).powersetCard 3 =
      {{0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}} := by decide
  rw [elementary, Finset.esymm_map_val, hs]
  simp (disch := decide) [sigma3, Finset.sum_insert, Finset.prod_insert]
  ring

theorem elementary_four (x : V4) : elementary 4 x = sigma4 x := by
  have hs : (Finset.univ : Finset (Fin 4)).powersetCard 4 = {{0,1,2,3}} := by decide
  rw [elementary, Finset.esymm_map_val, hs]
  simp (disch := decide) [sigma4, Finset.sum_insert, Finset.prod_insert]
  ring

theorem family_eq_elementary (M : ℝ) (x : V4) :
    family M x = elementary 0 x + M*elementary 1 x + elementary 2 x +
      M*elementary 3 x + elementary 4 x := by
  rw [elementary_zero, elementary_one, elementary_two, elementary_three, elementary_four]
  rfl

/-- Counterexample expressed using mathlib's elementary symmetric functions. -/
theorem elementary_symmetric_counterexample :
    let f : V4 → ℝ := fun x => fourthRoot
      (elementary 0 x + 2*elementary 1 x + elementary 2 x +
        2*elementary 3 x + elementary 4 x)
    ConcaveOn ℝ (Ioi 0) (fun t => f (fun _ => t)) ∧
      ¬ ConcaveOn ℝ positiveOrthant f := by
  have hf : rootedFamily 2 = fun x : V4 => fourthRoot
      (elementary 0 x + 2*elementary 1 x + elementary 2 x +
        2*elementary 3 x + elementary 4 x) := by
    funext x
    rw [rootedFamily, family_eq_elementary]
  simpa only [hf] using diagonal_concavity_counterexample

/-- Every parameter strictly greater than one disproves diagonal testing. -/
theorem family_of_counterexamples {M : ℝ} (hM : 1 < M) :
    ConcaveOn ℝ (Ioi 0) (fun t => rootedFamily M (fun _ => t)) ∧
      ¬ ConcaveOn ℝ positiveOrthant (rootedFamily M) := by
  constructor
  · simpa only [rootedFamily, family_diagonal] using diagonal_concave_of_one_le hM.le
  · exact family_not_concave_of_one_lt hM

/-- Both complete classifications, with no unproved analytic premise. -/
theorem complete_classification {M : ℝ} (hM : 0 < M) :
    (ConcaveOn ℝ (Ioi 0) (fun t => rootedFamily M (fun _ => t)) ↔ 1 ≤ M) ∧
      (ConcaveOn ℝ positiveOrthant (rootedFamily M) ↔ M = 1) := by
  constructor
  · simpa only [rootedFamily, family_diagonal] using diagonal_concave_iff hM
  · exact family_concave_iff hM

end MathAndTheory.DiagonalConcavity
