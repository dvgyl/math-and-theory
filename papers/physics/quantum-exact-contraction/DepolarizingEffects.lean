import DepolarizingEffectScalars

/-!
# Arbitrary-dimension binary-effect lift for negative depolarization

The input effect need not commute with the reference algebra.  The only
noncommutative interpolation step is the checked three-sandwich PSD identity.
-/

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey GeneralContraction ReplacerBounds
open NegativeDepolarizingBounds

namespace DepolarizingEffects
noncomputable section

variable {n R A : Type} [Fintype n] [DecidableEq n]
  [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

theorem spectral_harmonic_dominates (U : Matrix n n ℂ)
    (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1) (d : n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (M : Matrix n n ℂ) (hM : M.PosSemidef) (hIM : (1-M).PosSemidef)
    (hSM : (spectral U d-M).PosSemidef)
    (m s : ℝ) (hm : 4 ≤ m) (hs : 0<s) (hb : (m-1)*s<1) :
    (spectral U (fun i => harmonic m s (d i)) - M).PosSemidef := by
  have hw := weight_bounds m s hm hs hb
  apply harmonic_dominates M (spectral U d)
    (spectral U (fun i => reciprocal m s (d i))) _ (weight m s)
    hw.1.le hw.2.le hM hSM hIM (spectral_hermitian U _) (spectral_hermitian U _)
  · rw [← spectral_smul, ← spectral_smul, ← spectral_add]
    have hf : (fun i => weight m s * reciprocal m s (d i) +
        (1-weight m s)*harmonic m s (d i)) = fun _ : n => 1 := by
      funext i
      exact scalar_interpolation_linear m s (d i) hm hs hb (hd i)
    rw [hf, spectral_const U hU' 1, one_smul]
  · simp only [spectral_mul U hU]
    rw [← spectral_smul, ← spectral_smul, ← spectral_add]
    exact congrArg (spectral U) (funext fun i =>
      scalar_interpolation_quad m s (d i) hm hs hb (hd i))

theorem spectral_effect_split (U : Matrix n n ℂ)
    (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1) (d : n → ℝ)
    (m : ℝ) (hm : 4 ≤ m) (hd : ∀ i, 0 ≤ d i) (hdm : ∀ i, d i ≤ m)
    (M : Matrix n n ℂ) (hM : M.PosSemidef) (hIM : (1-M).PosSemidef)
    (hSM : (spectral U d-M).PosSemidef)
    (hcomp : (m • (1:Matrix n n ℂ) - spectral U d - (1-M)).PosSemidef)
    (s : ℝ) (hs : 0<s) (hb : (m-1)*s<1) :
    (spectral U (fun i => reserve m s (d i))).PosSemidef ∧
    ((1-sharpBound m s) • (1:Matrix n n ℂ) -
      spectral U (fun i => reserve m s (d i))).PosSemidef ∧
    (prefactor m s • spectral U d - s • M -
      spectral U (fun i => reserve m s (d i))).PosSemidef ∧
    (sharpBound m s • (1:Matrix n n ℂ) -
      (prefactor m s • spectral U d - s • M -
        spectral U (fun i => reserve m s (d i)))).PosSemidef := by
  have henv := fun i => upperEnvelope_bounds m s (d i) hm hs hb (hd i) (hdm i)
  have hF := spectral_harmonic_dominates U hU hU' d hd M hM hIM hSM m s hm hs hb
  have hcomp' : (spectral U (fun i => m-d i) - (1-M)).PosSemidef := by
    simpa only [spectral_sub, spectral_const U hU' m] using hcomp
  have hG := spectral_harmonic_dominates U hU hU' (fun i => m-d i)
    (fun i => sub_nonneg.mpr (hdm i)) (1-M) hIM
    (by simpa only [sub_sub_cancel] using hM) hcomp' m s hm hs hb
  let Z := spectral U (fun i => upperEnvelope m s (d i))
  have hZM : (Z-M).PosSemidef := by
    have hz := spectral_difference_positive U (fun i => harmonic m s (d i))
      (fun i => upperEnvelope m s (d i)) (fun i => (henv i).1)
    have hh := hz.add hF
    simpa only [sub_add_sub_cancel] using hh
  have hcap : (spread m s • (1:Matrix n n ℂ) - (Z-M)).PosSemidef := by
    have hz := spectral_difference_positive U (fun i => upperEnvelope m s (d i))
      (fun i => 1-harmonic m s (m-d i)+spread m s) (fun i => (henv i).2.1)
    rw [spectral_add, spectral_sub, spectral_const U hU' 1, one_smul,
      spectral_const U hU' (spread m s)] at hz
    have hh := hz.add hG
    convert hh using 1
    dsimp [Z]
    abel
  have heq : spectral U (fun i => reserve m s (d i)) =
      prefactor m s • spectral U d - s • Z := by
    unfold reserve
    rw [spectral_sub, spectral_smul, spectral_smul]
  have hres : prefactor m s • spectral U d - s • M -
      spectral U (fun i => reserve m s (d i)) = s • (Z-M) := by
    rw [heq, smul_sub]
    abel
  refine ⟨spectral_positive U _ (fun i => (henv i).2.2.1), ?_, ?_, ?_⟩
  · rw [← spectral_const U hU' (1-sharpBound m s)]
    exact spectral_difference_positive U _ _ (fun i => (henv i).2.2.2)
  · rw [hres]
    exact posSemidef_real_smul _ hZM s hs.le
  · rw [hres, sharpBound_eq]
    have hh := posSemidef_real_smul _ hcap s hs.le
    simpa only [smul_sub, smul_smul] using hh

/-- The reserve lies in the reference algebra, while the residual effect is
bounded by the sharp all-dimensional factor. -/
theorem reference_effect_split (D : Matrix R R ℂ) (hD : D.PosSemidef)
    (m : ℝ) (hm : 4 ≤ m) (hDm : (m • (1:Matrix R R ℂ)-D).PosSemidef)
    (M : Matrix (R×A) (R×A) ℂ) (hM : M.PosSemidef) (hIM : (1-M).PosSemidef)
    (hDM : (referenceLift D-M).PosSemidef)
    (hcomp : (m • (1:Matrix (R×A) (R×A) ℂ)-referenceLift D-(1-M)).PosSemidef)
    (s : ℝ) (hs : 0<s) (hb : (m-1)*s<1) :
    ∃ H : Matrix R R ℂ, H.PosSemidef ∧
      ((1-sharpBound m s) • (1:Matrix R R ℂ)-H).PosSemidef ∧
      (prefactor m s • referenceLift D-s • M-referenceLift H).PosSemidef ∧
      (sharpBound m s • (1:Matrix (R×A) (R×A) ℂ)-
        (prefactor m s • referenceLift D-s • M-referenceLift H)).PosSemidef := by
  let U := hD.1.eigenvectorUnitary.1
  let d := hD.1.eigenvalues
  have hU : Uᴴ*U=1 := unitary.coe_star_mul_self hD.1.eigenvectorUnitary
  have hU' : U*Uᴴ=1 := unitary.coe_mul_star_self hD.1.eigenvectorUnitary
  have hspec : spectral U d = D := hD.1.spectral_theorem.symm
  have hd : ∀ i, 0 ≤ d i := hD.eigenvalues_nonneg
  have hdm : ∀ i, d i ≤ m := by
    have hp : (spectral U (fun i => m-d i)).PosSemidef := by
      simpa only [spectral_sub, spectral_const U hU' m, hspec] using hDm
    have hh := nonneg_of_spectral_positive U hU _ hp
    intro i
    exact sub_nonneg.mp (hh i)
  have hV : (referenceLift (A:=A) U)ᴴ * referenceLift U = 1 := by
    rw [referenceLift_star, referenceLift_mul, hU, referenceLift_one]
  have hV' : referenceLift (A:=A) U * (referenceLift U)ᴴ = 1 := by
    rw [referenceLift_star, referenceLift_mul, hU', referenceLift_one]
  have hvd : spectral (referenceLift (A:=A) U) (fun i => d i.1) = referenceLift D := by
    rw [referenceLift_spectral, hspec]
  have hh := spectral_effect_split (referenceLift (A:=A) U) hV hV' (fun i => d i.1)
    m hm (fun i => hd i.1) (fun i => hdm i.1) M hM hIM
    (by simpa only [hvd] using hDM) (by simpa only [hvd] using hcomp) s hs hb
  have hreserve : spectral (referenceLift (A:=A) U) (fun i => reserve m s (d i.1)) =
      referenceLift (spectral U (fun i => reserve m s (d i))) :=
    referenceLift_spectral U (fun i => reserve m s (d i))
  refine ⟨spectral U (fun i => reserve m s (d i)), ?_, ?_, ?_, ?_⟩
  · exact spectral_positive U _
      (fun i => (upperEnvelope_bounds m s (d i) hm hs hb (hd i) (hdm i)).2.2.1)
  · rw [← spectral_const U hU' (1-sharpBound m s)]
    exact spectral_difference_positive U _ _
      (fun i => (upperEnvelope_bounds m s (d i) hm hs hb (hd i) (hdm i)).2.2.2)
  · simpa only [hreserve, referenceLift_spectral, hspec] using hh.2.2.1
  · simpa only [hreserve, referenceLift_spectral, hspec] using hh.2.2.2

end
end DepolarizingEffects
