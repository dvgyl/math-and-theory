import MilneOrbitPolynomial
import MilneOrbitOrthogonal

/-!
# Complete spectral solution and global certificate for every symmetric matrix

All existence statements are unconditional in the real symmetric matrix and
linear term. The secular construction covers singular and indefinite matrices.
-/

open scoped BigOperators Matrix
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section
namespace Milne

def trustOrbitSpectrum (τ : ℝ) (k : V3) (K : T3) : Set ℝ :=
  {z | ∃ x : V3, vSq x ≤ 1 ∧ trustQuadratic τ k K x=z}

theorem trustOrbitSpectrum_eigenbasis (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian) :
    trustOrbitSpectrum τ k K=
      trustDiagSpectrum τ (trustEigenvalues K hK) (trustEigenLinear K hK k) := by
  ext z
  constructor
  · rintro ⟨x,hx,hz⟩
    refine ⟨tVec (trustEigenbasis K hK).transpose x,?_,?_⟩
    · change vSq (tVec (trustEigenbasis K hK).transpose x) ≤ 1
      rwa [trustEigenbasis_transpose_norm]
    · rw [← trust_quadratic_original_coordinates]
      exact hz
  · rintro ⟨y,hy,hz⟩
    refine ⟨tVec (trustEigenbasis K hK) y,?_,?_⟩
    · rw [trustEigenbasis_norm]
      exact hy
    · rw [trust_quadratic_eigenbasis]
      exact hz

/-- The exact global maximum at the unique admissible spectral shift. -/
theorem trust_spectral_isGreatest (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian) (l : ℝ)
    (hl : trustShiftAdmissible (trustEigenvalues K hK) (trustEigenLinear K hK k) l) :
    IsGreatest (trustOrbitSpectrum τ k K)
      (trustDiagValue τ (trustEigenvalues K hK) (trustEigenLinear K hK k) l) := by
  rw [trustOrbitSpectrum_eigenbasis τ k K hK]
  obtain ⟨p,hp⟩ := trust_admissible_certificate _ _ l hl
  exact trustDiag_certificate_isGreatest τ _ _ p l hp

/-- A finite candidate set of cardinal at most seven contains exactly one
admissible shift, and that shift gives the attained global optimum. -/
theorem trust_spectral_finite_solution (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian) :
    ∃! l : ℝ,
      l ∈ trustShiftCandidates (trustEigenvalues K hK) (trustEigenLinear K hK k) ∧
      trustShiftAdmissible (trustEigenvalues K hK) (trustEigenLinear K hK k) l ∧
      IsGreatest (trustOrbitSpectrum τ k K)
        (trustDiagValue τ (trustEigenvalues K hK) (trustEigenLinear K hK k) l) := by
  obtain ⟨l,hl,hu⟩ := trust_finite_algebraic_solution
    (trustEigenvalues K hK) (trustEigenLinear K hK k)
  exact ⟨l,⟨hl.1,hl.2,trust_spectral_isGreatest τ k K hK l hl.2⟩,
    fun u hh => hu u ⟨hh.1,hh.2.1⟩⟩

/-- Every maximizing point: all nonzero shifted eigencoordinates are fixed,
all zero eigencoordinates are free subject only to the displayed ball/sphere
condition. This includes every hard case and every flat family. -/
theorem trust_spectral_all_maximizers (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian) (l : ℝ)
    (hl : trustShiftAdmissible (trustEigenvalues K hK) (trustEigenLinear K hK k) l)
    (x : V3) (hx : vSq x ≤ 1) :
    trustQuadratic τ k K x=
      trustDiagValue τ (trustEigenvalues K hK) (trustEigenLinear K hK k) l ↔
    (∀ i, trustEigenvalues K hK i+l ≠ 0 →
      tVec (trustEigenbasis K hK).transpose x i=
        trustDiagPoint (trustEigenvalues K hK) (trustEigenLinear K hK k) l i) ∧
      l*(1-vSq x)=0 := by
  let d := trustEigenvalues K hK
  let h := trustEigenLinear K hK k
  let y := tVec (trustEigenbasis K hK).transpose x
  obtain ⟨p,hp⟩ := trust_admissible_certificate d h l hl
  have hyn : trustSq y=vSq x := trustEigenbasis_transpose_norm K hK x
  have hy : trustSq y ≤ 1 := by rw [hyn]; exact hx
  have he := trustDiag_certificate_equality τ d h p y l hp hy
  rw [trustDiag_certificate_value τ d h p l hp] at he
  rw [trust_quadratic_original_coordinates]
  change trustDiagObjective τ d h y=trustDiagValue τ d h l ↔ _
  constructor
  · intro hv
    obtain ⟨hc,hn⟩ := he.mp hv
    refine ⟨?_,by rwa [hyn] at hn⟩
    intro i hi
    exact (hc i hi).trans (trustDiag_certificate_coordinates d h p l hp i hi)
  · rintro ⟨hc,hn⟩
    apply he.mpr
    refine ⟨?_,by rwa [hyn]⟩
    intro i hi
    exact (hc i hi).trans (trustDiag_certificate_coordinates d h p l hp i hi).symm

def trustMatrixCertificate (k : V3) (K : T3) (p : V3) (l : ℝ) : Prop :=
  0 ≤ l ∧ (trustShiftMatrix K l).PosSemidef ∧
    tVec (trustShiftMatrix K l) p=k ∧ vSq p ≤ 1 ∧ l*(1-vSq p)=0

/-- Existence of the full global trust-region certificate is proved for
every real symmetric matrix, including singular and indefinite cases. -/
theorem trust_matrix_certificate_exists (k : V3) (K : T3) (hK : K.IsHermitian) :
    ∃ l : ℝ, ∃ p : V3, trustMatrixCertificate k K p l := by
  obtain ⟨l,hl⟩ := trust_admissible_exists
    (trustEigenvalues K hK) (trustEigenLinear K hK k)
  obtain ⟨y,hy⟩ := trust_admissible_certificate _ _ l hl
  refine ⟨l,tVec (trustEigenbasis K hK) y,hy.1,
    trustEigenbasis_shift_psd K hK l hy.2.1,
    trustEigenbasis_shift_equation k K hK y l hy.2.2.1,?_,?_⟩
  · rw [trustEigenbasis_norm]
    exact hy.2.2.2.1
  · rw [trustEigenbasis_norm]
    exact hy.2.2.2.2

theorem trust_matrix_certificate_gap (τ : ℝ) (k : V3) (K : T3)
    (p x : V3) (l : ℝ) (hp : trustMatrixCertificate k K p l) :
    trustQuadratic τ k K p-trustQuadratic τ k K x=
      vDot (x-p) (tVec (trustShiftMatrix K l) (x-p))+l*(1-vSq x) := by
  have hs := trust_completed_square τ k (trustShiftMatrix K l) hp.2.1.1 p hp.2.2.1 x
  rw [trust_shift_objective,trust_shift_objective] at hs
  nlinarith [hp.2.2.2.2]

theorem trust_matrix_certificate_upper (τ : ℝ) (k : V3) (K : T3)
    (p x : V3) (l : ℝ) (hp : trustMatrixCertificate k K p l) (hx : vSq x ≤ 1) :
    trustQuadratic τ k K x ≤ trustQuadratic τ k K p := by
  have hs : 0 ≤ vDot (x-p) (tVec (trustShiftMatrix K l) (x-p)) := by
    simpa [vDot,tVec,Matrix.mulVec,dotProduct] using hp.2.1.2 (x-p)
  have hc := mul_nonneg hp.1 (sub_nonneg.mpr hx)
  have hg := trust_matrix_certificate_gap τ k K p x l hp
  linarith

/-- Coordinate-free equality test: exactly the shifted nullspace and the
complementary sphere constraint remain. -/
theorem trust_matrix_certificate_equality (τ : ℝ) (k : V3) (K : T3)
    (p x : V3) (l : ℝ) (hp : trustMatrixCertificate k K p l) (hx : vSq x ≤ 1) :
    trustQuadratic τ k K x=trustQuadratic τ k K p ↔
      tVec (trustShiftMatrix K l) (x-p)=0 ∧ l*(1-vSq x)=0 := by
  have hs : 0 ≤ vDot (x-p) (tVec (trustShiftMatrix K l) (x-p)) := by
    simpa [vDot,tVec,Matrix.mulVec,dotProduct] using hp.2.1.2 (x-p)
  have hc := mul_nonneg hp.1 (sub_nonneg.mpr hx)
  have hg := trust_matrix_certificate_gap τ k K p x l hp
  have hz : vDot (x-p) (tVec (trustShiftMatrix K l) (x-p))=0 ↔
      tVec (trustShiftMatrix K l) (x-p)=0 := by
    simpa [vDot,tVec,Matrix.mulVec,dotProduct] using
      hp.2.1.dotProduct_mulVec_zero_iff (x-p)
  constructor
  · intro he
    exact ⟨hz.mp (by linarith),by linarith⟩
  · rintro ⟨he,hn⟩
    have hq := hz.mpr he
    linarith

/-- The complete global certificate theorem. The forward direction derives
the certificate from the unconditional spectral construction and equality;
it does not postulate multiplier existence or omit the hard case. -/
theorem trust_global_optimum_iff_certificate (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian) (x : V3) :
    (vSq x ≤ 1 ∧ ∀ y : V3, vSq y ≤ 1 → trustQuadratic τ k K y ≤ trustQuadratic τ k K x) ↔
      ∃ l : ℝ, trustMatrixCertificate k K x l := by
  constructor
  · rintro ⟨hx,hmax⟩
    obtain ⟨l,p,hp⟩ := trust_matrix_certificate_exists k K hK
    have he : trustQuadratic τ k K x=trustQuadratic τ k K p :=
      le_antisymm (trust_matrix_certificate_upper τ k K p x l hp hx)
        (hmax p hp.2.2.2.1)
    obtain ⟨hn,hc⟩ := (trust_matrix_certificate_equality τ k K p x l hp hx).mp he
    have heq : tVec (trustShiftMatrix K l) x=k := by
      change trustShiftMatrix K l *ᵥ (x-p)=0 at hn
      rw [Matrix.mulVec_sub] at hn
      change tVec (trustShiftMatrix K l) x-tVec (trustShiftMatrix K l) p=0 at hn
      rw [hp.2.2.1] at hn
      exact sub_eq_zero.mp hn
    exact ⟨l,hp.1,hp.2.1,heq,hx,hc⟩
  · rintro ⟨l,hx⟩
    exact ⟨hx.2.2.2.1,fun y hy => trust_matrix_certificate_upper τ k K x y l hx hy⟩

end Milne
