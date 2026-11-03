import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.SimpRw

/-!
# Exact certificates for a diagonal quadratic on the closed unit ball

The next module constructs these certificates for every diagonal quadratic;
they are not extra assumptions in the final optimization theorem. The present
module proves the completed square, the value, every equality case, and the
uniqueness of the shift, including zero coefficients and zero linear terms.
-/

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section
namespace Milne

abbrev TrustVector := Fin 3 → ℝ

def trustSq (x : TrustVector) : ℝ := ∑ i, (x i)^2

def trustDiagObjective (τ : ℝ) (d h x : TrustVector) : ℝ :=
  τ + ∑ i, (2*h i*x i-d i*(x i)^2)

def trustDiagPoint (d h : TrustVector) (l : ℝ) : TrustVector := fun i => h i/(d i+l)

def trustDiagValue (τ : ℝ) (d h : TrustVector) (l : ℝ) : ℝ :=
  τ+l+∑ i, (h i)^2/(d i+l)

def trustDiagCertificate (d h p : TrustVector) (l : ℝ) : Prop :=
  0 ≤ l ∧ (∀ i, 0 ≤ d i+l) ∧ (∀ i, (d i+l)*p i = h i) ∧
    trustSq p ≤ 1 ∧ l*(1-trustSq p)=0

theorem trustDiag_stationary_gap (τ : ℝ) (d h p x : TrustVector) (l : ℝ)
    (hp : ∀ i, (d i+l)*p i=h i) :
    trustDiagObjective τ d h p-trustDiagObjective τ d h x =
      (∑ i, (d i+l)*(x i-p i)^2)+l*(trustSq p-trustSq x) := by
  have hh : h = fun i => (d i+l)*p i := funext fun i => (hp i).symm
  rw [hh]
  simp [trustDiagObjective,trustSq,Fin.sum_univ_three]
  ring

theorem trustDiag_certificate_gap (τ : ℝ) (d h p x : TrustVector) (l : ℝ)
    (hp : trustDiagCertificate d h p l) :
    trustDiagObjective τ d h p-trustDiagObjective τ d h x =
      (∑ i, (d i+l)*(x i-p i)^2)+l*(1-trustSq x) := by
  rcases hp with ⟨_,_,hs,_,hc⟩
  rw [trustDiag_stationary_gap τ d h p x l hs]
  nlinarith

theorem trustDiag_certificate_coordinates (d h p : TrustVector) (l : ℝ)
    (hp : trustDiagCertificate d h p l) (i : Fin 3) (hi : d i+l ≠ 0) :
    p i = trustDiagPoint d h l i := by
  unfold trustDiagPoint
  apply (eq_div_iff hi).mpr
  simpa only [mul_comm] using hp.2.2.1 i

theorem trustDiag_certificate_poles (d h p : TrustVector) (l : ℝ)
    (hp : trustDiagCertificate d h p l) (i : Fin 3) (hi : d i+l=0) : h i=0 := by
  have he := hp.2.2.1 i
  rw [hi,zero_mul] at he
  exact he.symm

theorem trustDiag_certificate_value (τ : ℝ) (d h p : TrustVector) (l : ℝ)
    (hp : trustDiagCertificate d h p l) :
    trustDiagObjective τ d h p = trustDiagValue τ d h l := by
  have he : ∀ i, h i*p i=(h i)^2/(d i+l) := by
    intro i
    by_cases hi : d i+l=0
    · rw [trustDiag_certificate_poles d h p l hp i hi]
      simp
    · rw [trustDiag_certificate_coordinates d h p l hp i hi,trustDiagPoint]
      ring
  have hh : h = fun i => (d i+l)*p i := funext fun i => (hp.2.2.1 i).symm
  have hs : trustDiagObjective τ d h p = τ+(∑ i, h i*p i)+l*trustSq p := by
    rw [hh]
    simp [trustDiagObjective,trustSq,Fin.sum_univ_three]
    ring
  rw [hs]
  simp_rw [he]
  dsimp only [trustDiagValue]
  nlinarith [hp.2.2.2.2]

theorem trustDiag_certificate_upper (τ : ℝ) (d h p x : TrustVector) (l : ℝ)
    (hp : trustDiagCertificate d h p l) (hx : trustSq x ≤ 1) :
    trustDiagObjective τ d h x ≤ trustDiagObjective τ d h p := by
  have hs : 0 ≤ ∑ i, (d i+l)*(x i-p i)^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp.2.1 i) (sq_nonneg _)
  have hc := mul_nonneg hp.1 (sub_nonneg.mpr hx)
  have hg := trustDiag_certificate_gap τ d h p x l hp
  linarith

/-- Complete equality test, retaining all null directions. -/
theorem trustDiag_certificate_equality (τ : ℝ) (d h p x : TrustVector) (l : ℝ)
    (hp : trustDiagCertificate d h p l) (hx : trustSq x ≤ 1) :
    trustDiagObjective τ d h x = trustDiagObjective τ d h p ↔
      (∀ i, d i+l ≠ 0 → x i=p i) ∧ l*(1-trustSq x)=0 := by
  have hs : 0 ≤ ∑ i, (d i+l)*(x i-p i)^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp.2.1 i) (sq_nonneg _)
  have hc := mul_nonneg hp.1 (sub_nonneg.mpr hx)
  have hg := trustDiag_certificate_gap τ d h p x l hp
  constructor
  · intro hv
    have hsum : (∑ i, (d i+l)*(x i-p i)^2)=0 := by linarith
    refine ⟨?_,by linarith⟩
    intro i hi
    have hle := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
        mul_nonneg (hp.2.1 j) (sq_nonneg (x j-p j))) (Finset.mem_univ i)
    have hz : (d i+l)*(x i-p i)^2=0 := by
      have hn := mul_nonneg (hp.2.1 i) (sq_nonneg (x i-p i))
      rw [hsum] at hle
      linarith
    have hz' : (x i-p i)^2=0 := (mul_eq_zero.mp hz).resolve_left hi
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz')
  · rintro ⟨he,hd⟩
    have hsum : (∑ i, (d i+l)*(x i-p i)^2)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : d i+l=0
      · rw [hi,zero_mul]
      · rw [he i hi]
        simp
    rw [hsum,hd] at hg
    linarith

/-- Different optimal points, including entire flat balls or spheres, share
one and the same nonnegative spectral shift. -/
theorem trustDiag_certificate_shift_unique (d h p q : TrustVector) (l u : ℝ)
    (hp : trustDiagCertificate d h p l) (hq : trustDiagCertificate d h q u) : l=u := by
  have hpq := trustDiag_certificate_upper 0 d h p q l hp hq.2.2.2.1
  have hqp := trustDiag_certificate_upper 0 d h q p u hq hp.2.2.2.1
  have he : trustDiagObjective 0 d h q = trustDiagObjective 0 d h p :=
    le_antisymm hpq hqp
  obtain ⟨hcoord,hcomp⟩ := (trustDiag_certificate_equality 0 d h p q l hp
    hq.2.2.2.1).mp he
  have heq : ∀ i, (d i+l)*q i=h i := by
    intro i
    by_cases hi : d i+l=0
    · rw [hi,zero_mul,trustDiag_certificate_poles d h p l hp i hi]
    · rw [hcoord i hi]
      exact hp.2.2.1 i
  by_contra hne
  have hdiff : u-l ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hq0 : q=0 := by
    funext i
    have hz : (u-l)*q i=0 := by nlinarith [heq i,hq.2.2.1 i]
    exact (mul_eq_zero.mp hz).resolve_left hdiff
  have hnorm : trustSq q=0 := by simp [hq0,trustSq]
  rw [hnorm] at hcomp
  have hcomp' := hq.2.2.2.2
  rw [hnorm] at hcomp'
  simp only [sub_zero,mul_one] at hcomp hcomp'
  exact hne (hcomp.trans hcomp'.symm)

def trustDiagSpectrum (τ : ℝ) (d h : TrustVector) : Set ℝ :=
  {z | ∃ x : TrustVector, trustSq x ≤ 1 ∧ trustDiagObjective τ d h x=z}

theorem trustDiag_certificate_isGreatest (τ : ℝ) (d h p : TrustVector) (l : ℝ)
    (hp : trustDiagCertificate d h p l) :
    IsGreatest (trustDiagSpectrum τ d h) (trustDiagValue τ d h l) := by
  have hv := trustDiag_certificate_value τ d h p l hp
  refine ⟨⟨p,hp.2.2.2.1,hv⟩,?_⟩
  rintro z ⟨x,hx,rfl⟩
  rw [← hv]
  exact trustDiag_certificate_upper τ d h p x l hp hx

end Milne
