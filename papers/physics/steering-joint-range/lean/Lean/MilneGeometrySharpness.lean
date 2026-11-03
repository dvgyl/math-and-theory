import MilneGeometry
import MilneSharpness
import MilneBlochIdentities

/-!
# Exact canonical correlation envelope at prescribed radial skew

For every 0 <= c <= 1 and 0 <= t <= 1-c, an explicit positive state
has canonical centre c e_z, radial squared support t^2, and squared
correlation norm 1-c^2+2t^2. Together with `geometry_radial`, this proves
the exact maximum at each feasible pair, including degenerate endpoints.
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

def geometryEz : V3 := ![0,0,1]

theorem geometryEz_unit : vSq geometryEz = 1 := by
  unfold vSq
  rw [Fin.sum_univ_three]
  change (0:ℝ)^2 + 0^2 + 1^2 = 1
  norm_num

def geometrySkewPlus (c t : ℝ) : QQ → ℂ := fun i =>
  if i.1 = 0 then (if i.2 = 0 then (Real.sqrt (1+c+t) : ℂ) else 0)
  else if i.2 = 1 then (Real.sqrt (1-c+t) : ℂ) else 0

def geometrySkewMinus (c t : ℝ) : QQ → ℂ := fun i =>
  if i.1 = 0 then (if i.2 = 1 then (Real.sqrt (1+c-t) : ℂ) else 0)
  else if i.2 = 0 then (Real.sqrt (1-c-t) : ℂ) else 0

/-- A sum of two rank-one positive operators. -/
def geometrySkewState (c t : ℝ) : CMatrix :=
  (1/4 : ℂ) • (pure (geometrySkewPlus c t) + pure (geometrySkewMinus c t))

def geometrySkewU (c t : ℝ) : ℝ :=
  Real.sqrt (1+c+t) * Real.sqrt (1-c+t)

def geometrySkewV (c t : ℝ) : ℝ :=
  Real.sqrt (1+c-t) * Real.sqrt (1-c-t)

def geometrySkewT (c t : ℝ) : T3 :=
  !![(geometrySkewU c t + geometrySkewV c t)/2, 0, 0;
     0, (geometrySkewV c t - geometrySkewU c t)/2, 0;
     0, 0, t]

theorem geometrySkewState_psd (c t : ℝ) : (geometrySkewState c t).PosSemidef := by
  simpa [geometrySkewState] using psd_real_smul ((pure_psd (geometrySkewPlus c t)).add
    (pure_psd (geometrySkewMinus c t))) (1/4) (by norm_num)

/-- The witness is the claimed actual Bloch matrix, not just scalar data. -/
theorem geometrySkewState_bloch {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) :
    geometrySkewState c t = blochState (c • geometryEz) 0 (geometrySkewT c t) := by
  have h1 := Real.sq_sqrt (show 0 ≤ 1+c+t by linarith)
  have h2 := Real.sq_sqrt (show 0 ≤ 1-c+t by linarith)
  have h3 := Real.sq_sqrt (show 0 ≤ 1+c-t by linarith)
  have h4 := Real.sq_sqrt (show 0 ≤ 1-c-t by linarith)
  ext ⟨i1,i2⟩ ⟨j1,j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    apply Complex.ext <;>
    simp [geometrySkewState, geometrySkewPlus, geometrySkewMinus,
      geometrySkewT, geometrySkewU, geometrySkewV, geometryEz, pure,
      blochState, onAlice, onBob, pauli, pauliZ, Pi.smul_apply, smul_eq_mul,
      Fin.sum_univ_three, Complex.star_def, Complex.mul_re, Complex.mul_im,
      Prod.ext_iff, ← pow_two, ← Complex.ofReal_pow, h1, h2, h3, h4]
  all_goals ring

theorem geometrySkewState_density {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) :
    Density (geometrySkewState c t) := by
  refine ⟨geometrySkewState_psd c t, ?_⟩
  rw [geometrySkewState_bloch hc0 hc1 ht0 ht1]
  exact blochState_trace _ _ _

theorem geometrySkewState_partialB {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) :
    partialB (geometrySkewState c t) = (1/2:ℂ) • (1 : Matrix Q Q ℂ) := by
  rw [geometrySkewState_bloch hc0 hc1 ht0 ht1]
  exact blochState_canonical _ _

theorem geometrySkewState_center {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) :
    center (geometrySkewState c t) = c := by
  rw [geometrySkewState_bloch hc0 hc1 ht0 ht1]
  exact blochState_radial_center c geometryEz _ hc0 geometryEz_unit

theorem geometrySkewT_radial (c t : ℝ) :
    vSq (ttVec (geometrySkewT c t) geometryEz) = t^2 := by
  simp [vSq, ttVec, geometrySkewT, geometryEz, Fin.sum_univ_three]

theorem geometrySkewT_squared {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) :
    tSq (geometrySkewT c t) = 1-c^2+2*t^2 := by
  have h1 := Real.sq_sqrt (show 0 ≤ 1+c+t by linarith)
  have h2 := Real.sq_sqrt (show 0 ≤ 1-c+t by linarith)
  have h3 := Real.sq_sqrt (show 0 ≤ 1+c-t by linarith)
  have h4 := Real.sq_sqrt (show 0 ≤ 1-c-t by linarith)
  have hu : (geometrySkewU c t)^2 = (1+c+t)*(1-c+t) := by
    simp only [geometrySkewU, mul_pow, h1, h2]
  have hv : (geometrySkewV c t)^2 = (1+c-t)*(1-c-t) := by
    simp only [geometrySkewV, mul_pow, h3, h4]
  simp [tSq, geometrySkewT, Fin.sum_univ_three]
  nlinarith [hu, hv]

/-- Feasible physical correlation values at prescribed centre c e_z and
radial squared support t^2. -/
def geometrySkewSpectrum (c t : ℝ) : Set ℝ :=
  {x | ∃ T : T3, (blochState (c • geometryEz) 0 T).PosSemidef ∧
    vSq (ttVec T geometryEz) = t^2 ∧ tSq T = x}

/-- Exact sharp canonical centre/skew envelope, including c=0,c=1,t=0
and t=1-c. The witnesses are actual PSD matrices. -/
theorem geometrySkewEnvelope_isGreatest {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) :
    IsGreatest (geometrySkewSpectrum c t) (1-c^2+2*t^2) := by
  constructor
  · refine ⟨geometrySkewT c t, ?_, geometrySkewT_radial c t,
      geometrySkewT_squared hc0 hc1 ht0 ht1⟩
    rw [← geometrySkewState_bloch hc0 hc1 ht0 ht1]
    exact geometrySkewState_psd c t
  · intro x hx
    obtain ⟨T,hM,hq,rfl⟩ := hx
    have h := geometry_radial c geometryEz T geometryEz_unit hM
    rwa [hq] at h

#print axioms geometrySkewState_density
#print axioms geometrySkewState_center
#print axioms geometrySkewEnvelope_isGreatest

end Milne
