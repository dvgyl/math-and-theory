import MilneOrbitSpectral

/-!
# Exact invertible-filter boundary behavior

An explicit algebraic epsilon approximation proves equality of the open-ball
supremum and closed-ball maximum. The spectral equality theorem then gives
an exact criterion for open-ball attainment, including flat nullspaces.
-/

open scoped BigOperators Matrix
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section
namespace Milne

theorem trustDiagPoint_min_norm (d h y : TrustVector) (l : ℝ)
    (hy : ∀ i, d i+l ≠ 0 → y i=trustDiagPoint d h l i) :
    trustSq (trustDiagPoint d h l) ≤ trustSq y := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : d i+l=0
  · simp [trustDiagPoint,hi,sq_nonneg]
  · rw [hy i hi]

/-- An interior maximizing point exists exactly in the zero-shift case
with strict room remaining after the pseudoinverse point. -/
theorem trust_spectral_interior_attainment (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian) (l : ℝ)
    (hl : trustShiftAdmissible (trustEigenvalues K hK) (trustEigenLinear K hK k) l) :
    (∃ x : V3, vSq x<1 ∧ trustQuadratic τ k K x=
      trustDiagValue τ (trustEigenvalues K hK) (trustEigenLinear K hK k) l) ↔
      l=0 ∧ trustSq (trustDiagPoint (trustEigenvalues K hK) (trustEigenLinear K hK k) l)<1 := by
  constructor
  · rintro ⟨x,hx,hv⟩
    obtain ⟨hc,hn⟩ := (trust_spectral_all_maximizers τ k K hK l hl x (le_of_lt hx)).mp hv
    have hl0 : l=0 := (mul_eq_zero.mp hn).resolve_right (ne_of_gt (sub_pos.mpr hx))
    have hmin := trustDiagPoint_min_norm (trustEigenvalues K hK) (trustEigenLinear K hK k)
      (tVec (trustEigenbasis K hK).transpose x) l hc
    change trustSq (trustDiagPoint _ _ l) ≤ vSq (tVec (trustEigenbasis K hK).transpose x) at hmin
    rw [trustEigenbasis_transpose_norm] at hmin
    exact ⟨hl0,lt_of_le_of_lt hmin hx⟩
  · rintro ⟨hl0,hq⟩
    let q := trustDiagPoint (trustEigenvalues K hK) (trustEigenLinear K hK k) l
    let x := tVec (trustEigenbasis K hK) q
    have hx : vSq x<1 := by rw [trustEigenbasis_norm]; exact hq
    refine ⟨x,hx,(trust_spectral_all_maximizers τ k K hK l hl x (le_of_lt hx)).mpr ?_⟩
    refine ⟨?_,by rw [hl0]; simp⟩
    intro i _
    exact congrFun (trustEigenbasis_inverse_left K hK q) i

theorem trust_scale_objective (τ : ℝ) (k p : V3) (K : T3) (t : ℝ) :
    trustQuadratic τ k K (t • p)=
      τ+2*t*vDot k p-t^2*vDot p (tVec K p) := by
  simp [trustQuadratic,vDot,tVec,Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three]
  ring

/-- A constructive epsilon approximation of every closed-ball value by an
open-ball value. No limiting assertion or optimizer existence is assumed. -/
theorem trust_open_ball_approximation (τ : ℝ) (k : V3) (K : T3)
    (p : V3) (hp : vSq p ≤ 1) (ε : ℝ) (hε : 0<ε) :
    ∃ x : V3, vSq x<1 ∧ trustQuadratic τ k K p-ε<trustQuadratic τ k K x := by
  let a := vDot p (tVec K p)
  let A := |trustQuadratic τ k K p-τ|+|a|
  have hA : 0 ≤ A := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hden : 0<A+ε := by linarith
  let δ := ε/(A+ε)
  let t := 1-δ
  have hδ : 0<δ := div_pos hε hden
  have hδ1 : δ ≤ 1 := (div_le_one hden).mpr (by linarith)
  have ht0 : 0 ≤ t := sub_nonneg.mpr hδ1
  have ht1 : t<1 := by dsimp [t]; linarith
  have hδA : δ*A<ε := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith [sq_pos_of_pos hε]
  have hterm : -t*a ≤ |a| := by
    calc
      -t*a = -(t*a) := by ring
      _ ≤ |t*a| := neg_le_abs _
      _ = t*|a| := by rw [abs_mul,abs_of_nonneg ht0]
      _ ≤ |a| := by
        have hh := mul_nonneg (sub_nonneg.mpr (le_of_lt ht1)) (abs_nonneg a)
        nlinarith
  have hinside : trustQuadratic τ k K p-τ-t*a ≤ A := by
    have hh := le_abs_self (trustQuadratic τ k K p-τ)
    dsimp only [A]
    linarith
  have hgap : trustQuadratic τ k K p-trustQuadratic τ k K (t • p)=
      δ*(trustQuadratic τ k K p-τ-t*a) := by
    rw [trust_scale_objective]
    dsimp only [trustQuadratic,t,a]
    ring
  have hgaple := mul_le_mul_of_nonneg_left hinside (le_of_lt hδ)
  have htsq : t^2<1 := by
    have hh := mul_pos (sub_pos.mpr ht1) (show 0<1+t by linarith)
    nlinarith
  refine ⟨t • p,?_,by linarith⟩
  rw [trust_vSq_smul]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hp (sq_nonneg t))
    (by simpa only [mul_one] using htsq)

def trustOpenOrbitSpectrum (τ : ℝ) (k : V3) (K : T3) : Set ℝ :=
  {z | ∃ x : V3, vSq x<1 ∧ trustQuadratic τ k K x=z}

/-- The open ball has the same exact supremum, whether or not it has a
maximizer. The approximation above supplies the sharp lower direction. -/
theorem trust_spectral_open_isLUB (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian) (l : ℝ)
    (hl : trustShiftAdmissible (trustEigenvalues K hK) (trustEigenLinear K hK k) l) :
    IsLUB (trustOpenOrbitSpectrum τ k K)
      (trustDiagValue τ (trustEigenvalues K hK) (trustEigenLinear K hK k) l) := by
  have hmax := trust_spectral_isGreatest τ k K hK l hl
  obtain ⟨p,hp,hv⟩ := hmax.1
  refine ⟨?_,?_⟩
  · rintro z ⟨x,hx,hz⟩
    exact hmax.2 ⟨x,le_of_lt hx,hz⟩
  · intro u hu
    by_contra hn
    have hu' : u<trustDiagValue τ (trustEigenvalues K hK) (trustEigenLinear K hK k) l :=
      lt_of_not_ge hn
    let ε := trustDiagValue τ (trustEigenvalues K hK) (trustEigenLinear K hK k) l-u
    have hε : 0<ε := sub_pos.mpr hu'
    obtain ⟨x,hx,hclose⟩ := trust_open_ball_approximation τ k K p hp ε hε
    have hupper : trustQuadratic τ k K x ≤ u := hu ⟨x,hx,rfl⟩
    rw [hv] at hclose
    dsimp only [ε] at hclose
    linarith

end Milne
