import MilneOrbitOpenBall
import MilnePhysicalOrbitFilter

/-!
# Complete physical one-sided F3 orbit optimization

The spectral optimizer is connected to every normalized complex local filter
and every physical Bloch-ball effect. Closed-orbit maxima, all maximizing
effects, invertible-orbit suprema, and exact invertible-attainment conditions
are proved for actual positive two-qubit matrices, with no state-rank premise.
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section
namespace Milne

def canonicalOrbitEigenvalues (c : V3) (S : T3) : V3 :=
  trustEigenvalues (orbitK c S) (orbitK_hermitian c S)

def canonicalOrbitEigenlinear (c : V3) (S : T3) : V3 :=
  trustEigenLinear (orbitK c S) (orbitK_hermitian c S) (ttVec S c)

def canonicalOrbitFrame (c : V3) (S : T3) : T3 :=
  trustEigenbasis (orbitK c S) (orbitK_hermitian c S)

def canonicalOrbitValue (c : V3) (S : T3) (l : ℝ) : ℝ :=
  trustDiagValue (tSq S) (canonicalOrbitEigenvalues c S) (canonicalOrbitEigenlinear c S) l

def canonicalOrbitShiftAdmissible (c : V3) (S : T3) (l : ℝ) : Prop :=
  trustShiftAdmissible (canonicalOrbitEigenvalues c S) (canonicalOrbitEigenlinear c S) l

def canonicalOrbitShiftCandidates (c : V3) (S : T3) : Finset ℝ :=
  trustShiftCandidates (canonicalOrbitEigenvalues c S) (canonicalOrbitEigenlinear c S)

def canonicalFilterSpectrum (c : V3) (S : T3) : Set ℝ :=
  {z | ∃ F : Matrix Q Q ℂ, Matrix.trace (Fᴴ*F)=2 ∧
    correlationSq (complexFiltered (blochState c 0 S) F)=z}

def canonicalInvertibleFilterSpectrum (c : V3) (S : T3) : Set ℝ :=
  {z | ∃ F : Matrix Q Q ℂ, Matrix.trace (Fᴴ*F)=2 ∧ F.det ≠ 0 ∧
    correlationSq (complexFiltered (blochState c 0 S) F)=z}

theorem trustQuadratic_eq_orbitQuadratic (τ : ℝ) (k : V3) (K : T3) (x : V3) :
    trustQuadratic τ k K x=orbitQuadratic τ k K x := rfl

/-- Equality of the complete physical correlation spectrum and the derived
closed-ball quadratic spectrum, in both directions. -/
theorem canonical_filter_spectrum_eq_ball (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) :
    canonicalFilterSpectrum c S=trustOrbitSpectrum (tSq S) (ttVec S c) (orbitK c S) := by
  ext z
  constructor
  · rintro ⟨F,hTr,hz⟩
    obtain ⟨b,hb,hF⟩ := complex_filter_effect_coordinates F hTr
    refine ⟨b,hb,?_⟩
    rw [trustQuadratic_eq_orbitQuadratic,← canonical_complex_filter_correlation c b S hM F hF]
    exact hz
  · rintro ⟨b,hb,hz⟩
    have hw := canonical_filter_realizes_ball c b S hM hb
    dsimp only at hw
    refine ⟨qubitBallFilter b hb,hw.1,?_⟩
    exact hw.2.2.trans hz

/-- The exact full physical orbit is solved by at most seven algebraic
candidates, with exactly one admissible shift and an attained maximum. -/
theorem canonical_filter_finite_spectral_solution (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) :
    ∃! l : ℝ, l ∈ canonicalOrbitShiftCandidates c S ∧
      canonicalOrbitShiftAdmissible c S l ∧
      IsGreatest (canonicalFilterSpectrum c S) (canonicalOrbitValue c S l) := by
  rw [canonical_filter_spectrum_eq_ball c S hM]
  exact trust_spectral_finite_solution (tSq S) (ttVec S c) (orbitK c S) (orbitK_hermitian c S)

theorem canonicalOrbitShiftCandidates_card (c : V3) (S : T3) :
    (canonicalOrbitShiftCandidates c S).card ≤ 7 :=
  trustShiftCandidates_card _ _

theorem canonical_filter_value_isGreatest (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) (l : ℝ)
    (hl : canonicalOrbitShiftAdmissible c S l) :
    IsGreatest (canonicalFilterSpectrum c S) (canonicalOrbitValue c S l) := by
  rw [canonical_filter_spectrum_eq_ball c S hM]
  exact trust_spectral_isGreatest (tSq S) (ttVec S c) (orbitK c S) (orbitK_hermitian c S) l hl

/-- Complete classification of every maximizing complex filter through its
actual positive effect. Null eigencoordinates are retained, not excluded by
an inverse-matrix assumption. -/
theorem canonical_filter_all_maximizers (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) (l : ℝ)
    (hl : canonicalOrbitShiftAdmissible c S l)
    (F : Matrix Q Q ℂ) (hTr : Matrix.trace (Fᴴ*F)=2) :
    correlationSq (complexFiltered (blochState c 0 S) F)=canonicalOrbitValue c S l ↔
    ∃ b : V3, vSq b ≤ 1 ∧ Fᴴ*F=1+spin b ∧
      (∀ i, canonicalOrbitEigenvalues c S i+l ≠ 0 →
        tVec (canonicalOrbitFrame c S).transpose b i=
          trustDiagPoint (canonicalOrbitEigenvalues c S) (canonicalOrbitEigenlinear c S) l i) ∧
        l*(1-vSq b)=0 := by
  constructor
  · intro hv
    obtain ⟨b,hb,hF⟩ := complex_filter_effect_coordinates F hTr
    have hcorr := canonical_complex_filter_correlation c b S hM F hF
    rw [hcorr] at hv
    have hspec := (trust_spectral_all_maximizers (tSq S) (ttVec S c) (orbitK c S)
      (orbitK_hermitian c S) l hl b hb).mp hv
    exact ⟨b,hb,hF,hspec⟩
  · rintro ⟨b,hb,hF,hspec⟩
    rw [canonical_complex_filter_correlation c b S hM F hF]
    exact (trust_spectral_all_maximizers (tSq S) (ttVec S c) (orbitK c S)
      (orbitK_hermitian c S) l hl b hb).mpr hspec

/-- Every effect appearing in the full maximizing classification has a
positive filter realization with the stated exact physical value. -/
theorem canonical_maximizing_effect_realized (c b : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) (l : ℝ)
    (hl : canonicalOrbitShiftAdmissible c S l) (hb : vSq b ≤ 1)
    (hc : ∀ i, canonicalOrbitEigenvalues c S i+l ≠ 0 →
      tVec (canonicalOrbitFrame c S).transpose b i=
        trustDiagPoint (canonicalOrbitEigenvalues c S) (canonicalOrbitEigenlinear c S) l i)
    (hn : l*(1-vSq b)=0) :
    let F := qubitBallFilter b hb
    Matrix.trace (Fᴴ*F)=2 ∧ Density (complexFiltered (blochState c 0 S) F) ∧
      correlationSq (complexFiltered (blochState c 0 S) F)=canonicalOrbitValue c S l := by
  have hw := canonical_filter_realizes_ball c b S hM hb
  dsimp only at hw ⊢
  refine ⟨hw.1,hw.2.1,?_⟩
  rw [hw.2.2]
  exact (trust_spectral_all_maximizers (tSq S) (ttVec S c) (orbitK c S)
    (orbitK_hermitian c S) l hl b hb).mpr ⟨hc,hn⟩

theorem complex_effect_invertible_iff (F : Matrix Q Q ℂ) (b : V3)
    (hF : Fᴴ*F=1+spin b) (hb : vSq b ≤ 1) : F.det ≠ 0 ↔ vSq b<1 := by
  constructor
  · intro hne
    have hdne : (Fᴴ*F).det ≠ 0 := by
      rw [Matrix.det_mul,Matrix.det_conjTranspose]
      exact mul_ne_zero (star_ne_zero.mpr hne) hne
    by_contra hn
    have he : vSq b=1 := le_antisymm hb (le_of_not_gt hn)
    apply hdne
    rw [hF,qubitBall_det,he]
    norm_num
  · intro hb' hz
    have hd := congrArg Matrix.det hF
    rw [Matrix.det_mul,Matrix.det_conjTranspose,hz,star_zero,mul_zero,qubitBall_det] at hd
    have hr := congrArg Complex.re hd
    simp only [Complex.zero_re,Complex.ofReal_re] at hr
    linarith

/-- Every invertible physical filter corresponds to the open ball, and
every open-ball point has an invertible positive realization. -/
theorem canonical_invertible_spectrum_eq_open (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) :
    canonicalInvertibleFilterSpectrum c S=
      trustOpenOrbitSpectrum (tSq S) (ttVec S c) (orbitK c S) := by
  ext z
  constructor
  · rintro ⟨F,hTr,hdet,hz⟩
    obtain ⟨b,hb,hF⟩ := complex_filter_effect_coordinates F hTr
    refine ⟨b,(complex_effect_invertible_iff F b hF hb).mp hdet,?_⟩
    rw [trustQuadratic_eq_orbitQuadratic,← canonical_complex_filter_correlation c b S hM F hF]
    exact hz
  · rintro ⟨b,hb,hz⟩
    have hw := canonical_filter_realizes_ball c b S hM (le_of_lt hb)
    dsimp only at hw
    exact ⟨qubitBallFilter b (le_of_lt hb),hw.1,qubitBallFilter_det_ne_zero b hb,
      hw.2.2.trans hz⟩

/-- Singular-filter maxima are approached by actual invertible filters;
the exact supremum is always the same finite spectral value. -/
theorem canonical_invertible_filter_isLUB (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) (l : ℝ)
    (hl : canonicalOrbitShiftAdmissible c S l) :
    IsLUB (canonicalInvertibleFilterSpectrum c S) (canonicalOrbitValue c S l) := by
  rw [canonical_invertible_spectrum_eq_open c S hM]
  exact trust_spectral_open_isLUB (tSq S) (ttVec S c) (orbitK c S)
    (orbitK_hermitian c S) l hl

/-- Exact invertible-attainment criterion, including all singular positive
semidefinite Hessians and flat families. -/
theorem canonical_invertible_filter_attainment_iff (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) (l : ℝ)
    (hl : canonicalOrbitShiftAdmissible c S l) :
    (∃ F : Matrix Q Q ℂ, Matrix.trace (Fᴴ*F)=2 ∧ F.det ≠ 0 ∧
      correlationSq (complexFiltered (blochState c 0 S) F)=canonicalOrbitValue c S l) ↔
      l=0 ∧ trustSq (trustDiagPoint (canonicalOrbitEigenvalues c S)
        (canonicalOrbitEigenlinear c S) l)<1 := by
  change canonicalOrbitValue c S l ∈ canonicalInvertibleFilterSpectrum c S ↔ _
  rw [canonical_invertible_spectrum_eq_open c S hM]
  exact trust_spectral_interior_attainment (tSq S) (ttVec S c) (orbitK c S)
    (orbitK_hermitian c S) l hl

def canonicalF3FilterSpectrum (c : V3) (S : T3) : Set ℝ :=
  {z | ∃ F : Matrix Q Q ℂ, Matrix.trace (Fᴴ*F)=2 ∧
    steeringValue (complexFiltered (blochState c 0 S) F)=z}

def canonicalInvertibleF3FilterSpectrum (c : V3) (S : T3) : Set ℝ :=
  {z | ∃ F : Matrix Q Q ℂ, Matrix.trace (Fᴴ*F)=2 ∧ F.det ≠ 0 ∧
    steeringValue (complexFiltered (blochState c 0 S) F)=z}

theorem canonicalOrbitValue_nonneg (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) (l : ℝ)
    (hl : canonicalOrbitShiftAdmissible c S l) : 0 ≤ canonicalOrbitValue c S l := by
  obtain ⟨F,_,hF⟩ := (canonical_filter_value_isGreatest c S hM l hl).1
  rw [← hF]
  exact correlationSq_nonneg _

/-- Literal F3 maximum over all normalized complex local filters. -/
theorem canonical_F3_filter_isGreatest (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) (l : ℝ)
    (hl : canonicalOrbitShiftAdmissible c S l) :
    IsGreatest (canonicalF3FilterSpectrum c S) (Real.sqrt (canonicalOrbitValue c S l)) := by
  have hs := canonical_filter_value_isGreatest c S hM l hl
  obtain ⟨F,hTr,hF⟩ := hs.1
  refine ⟨⟨F,hTr,?_⟩,?_⟩
  · rw [steeringValue,hF]
  · rintro z ⟨G,hG,rfl⟩
    exact Real.sqrt_le_sqrt (hs.2 ⟨G,hG,rfl⟩)

/-- Literal F3 supremum over invertible filters, with no attainment
assumption at the singular-filter boundary. -/
theorem canonical_invertible_F3_filter_isLUB (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) (l : ℝ)
    (hl : canonicalOrbitShiftAdmissible c S l) :
    IsLUB (canonicalInvertibleF3FilterSpectrum c S) (Real.sqrt (canonicalOrbitValue c S l)) := by
  have hs := canonical_invertible_filter_isLUB c S hM l hl
  have hmax := canonical_filter_value_isGreatest c S hM l hl
  refine ⟨?_,?_⟩
  · rintro z ⟨F,hF,_,rfl⟩
    exact Real.sqrt_le_sqrt (hmax.2 ⟨F,hF,rfl⟩)
  · intro u hu
    have hI : Matrix.trace ((1 : Matrix Q Q ℂ)ᴴ*1)=2 := by
      norm_num [Matrix.trace,Matrix.diag,Fin.sum_univ_two]
    have hIu : steeringValue (complexFiltered (blochState c 0 S) 1) ≤ u :=
      hu ⟨1,hI,by simp,rfl⟩
    have hu0 : 0 ≤ u := (Real.sqrt_nonneg _).trans hIu
    have hsq : canonicalOrbitValue c S l ≤ u^2 := hs.2 (by
      rintro z ⟨F,hF,hd,rfl⟩
      have hb := hu ⟨F,hF,hd,rfl⟩
      have hn := Real.sqrt_nonneg (correlationSq (complexFiltered (blochState c 0 S) F))
      have he := Real.sq_sqrt (correlationSq_nonneg (complexFiltered (blochState c 0 S) F))
      change Real.sqrt (correlationSq (complexFiltered (blochState c 0 S) F)) ≤ u at hb
      nlinarith)
    have hb := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs,abs_of_nonneg hu0] at hb

/-- Exact attainment criterion stated directly for F3 itself. -/
theorem canonical_invertible_F3_attainment_iff (c : V3) (S : T3)
    (hM : (blochState c 0 S).PosSemidef) (l : ℝ)
    (hl : canonicalOrbitShiftAdmissible c S l) :
    (∃ F : Matrix Q Q ℂ, Matrix.trace (Fᴴ*F)=2 ∧ F.det ≠ 0 ∧
      steeringValue (complexFiltered (blochState c 0 S) F)=
        Real.sqrt (canonicalOrbitValue c S l)) ↔
      l=0 ∧ trustSq (trustDiagPoint (canonicalOrbitEigenvalues c S)
        (canonicalOrbitEigenlinear c S) l)<1 := by
  rw [← canonical_invertible_filter_attainment_iff c S hM l hl]
  constructor
  · rintro ⟨F,hTr,hd,hv⟩
    refine ⟨F,hTr,hd,?_⟩
    have he := congrArg (fun t : ℝ => t^2) hv
    dsimp only at he
    rw [steeringValue,Real.sq_sqrt (correlationSq_nonneg _),
      Real.sq_sqrt (canonicalOrbitValue_nonneg c S hM l hl)] at he
    exact he
  · rintro ⟨F,hTr,hd,hv⟩
    exact ⟨F,hTr,hd,by rw [steeringValue,hv]⟩

end Milne
