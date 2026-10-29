import AdjugateJets
import CyclicResidualJets
import RateTiltedAction
import ResidualCumulants
import HermitianShift

/-!
First and second characteristic coefficients obtained from actual finite
Poisson equations. The determinant jet transfer is proved by the adjugate
identity; no eigenvalue or uncertainty conclusion is assumed.
-/
namespace UnicyclicRateJets
noncomputable section
open scoped BigOperators
open Equiv UnicyclicDeterminant UnicyclicPoisson UnicyclicResidualJets
open UnicyclicJets UnicyclicImplicit
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 2000000

def countedIncrement (a : ι) (i : ι) : ℝ := if i=a then 1 else 0

theorem countedIncrement_sum (a : ι) : (∑ i, countedIncrement a i)=1 := by
  simp [countedIncrement]

def jetMatrix (σ : Perm ι) (u v : ι → ℝ) (a : ι) (J C2 t : ℝ) : Matrix ι ι ℝ :=
  (edgeTilt (rateMatrix σ u v (lambdaJet J C2 t)) a (σ a) (Real.exp t)).transpose

theorem contDiff_polyJet (h k : ℝ) : ContDiff ℝ 2 (polyJet h k) := by
  exact (contDiff_const.add (contDiff_id.mul contDiff_const)).add
    (((contDiff_id.pow 2).mul contDiff_const).div_const 2)

theorem contDiff_lambdaJet (J C2 : ℝ) : ContDiff ℝ 2 (lambdaJet J C2) := by
  exact ((contDiff_const.mul contDiff_id).add
    ((contDiff_const.mul (contDiff_id.pow 2)).div_const 2))

omit [Fintype ι] [DecidableEq ι] in
theorem contDiff_rateMatrix [Fintype ι] [DecidableEq ι] (σ : Perm ι) (u v : ι → ℝ) (J C2 : ℝ) (i j : ι) :
    ContDiff ℝ 2 (fun t => rateMatrix σ u v (lambdaJet J C2 t) i j) := by
  have hDiag : ContDiff ℝ 2 (fun t => lambdaJet J C2 t+u j+v (σ⁻¹ j)) :=
    ((contDiff_lambdaJet J C2).add contDiff_const).add contDiff_const
  dsimp only [rateMatrix, ringMatrix]
  split_ifs <;>
    first | exact (hDiag.add contDiff_const).add contDiff_const | exact contDiff_const

theorem contDiff_jetMatrix (σ : Perm ι) (u v : ι → ℝ) (a : ι)
    (J C2 : ℝ) (i j : ι) :
    ContDiff ℝ 2 (fun t => jetMatrix σ u v a J C2 t i j) := by
  have hA := contDiff_rateMatrix σ u v J C2 j i
  have he : ContDiff ℝ 2 Real.exp := Real.contDiff_exp
  have hn : ContDiff ℝ 2 (fun t : ℝ => Real.exp (-t)) :=
    Real.contDiff_exp.comp contDiff_id.neg
  dsimp only [jetMatrix, Matrix.transpose_apply, edgeTilt]
  simp_rw [← Real.exp_neg]
  split_ifs <;>
    first | exact (he.mul hn).mul hA
          | exact (he.mul contDiff_const).mul hA
          | exact (contDiff_const.mul hn).mul hA
          | exact (contDiff_const.mul contDiff_const).mul hA

theorem jetMatrix_mulVec (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (hn : 3≤Fintype.card ι)
    (u v h k : ι → ℝ) (a : ι) (J C2 t : ℝ) (i : ι) :
    (jetMatrix σ u v a J C2 t).mulVec (fun j => polyJet (h j) (k j) t) i =
      UnicyclicResidualJets.residual σ u v (countedIncrement a) h k J C2 t i := by
  rw [jetMatrix, tilted_rate_residual σ hc hn]
  dsimp only [UnicyclicResidualJets.residual, countedIncrement, expPoly]
  rw [mul_neg, neg_mul]
  ring

theorem jetMatrix_det (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (hn : 3≤Fintype.card ι)
    (u v : ι → ℝ) (a : ι) (J C2 t : ℝ) :
    (jetMatrix σ u v a J C2 t).det =
      characteristicResidual (-(rateMatrix σ u v 0)).charpoly
        (∏ i, u i) (∏ i, v i) (quadraticBranch J C2) t := by
  rw [jetMatrix, Matrix.det_transpose,
    rateMatrix_determinant_tilt σ hc hn u v a (lambdaJet J C2 t)
      (Real.exp t) (Real.exp_ne_zero t)]
  dsimp only [characteristicResidual, quadraticBranch, lambdaJet]
  rw [UnicyclicSpectral.charpoly_neg_eval, rateMatrix_add_scalar, Real.exp_neg]
  ring

theorem coefficient_equations_from_poisson (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (hn : 3≤Fintype.card ι)
    (u v h k : ι → ℝ) (a : ι) (J C2 : ℝ)
    (hfirst : ∀ i, generator σ u v h i+drift σ u v (countedIncrement a) i=J)
    (hsecond : ∀ i, generator σ u v k i+
      2*tiltFirst σ u v (countedIncrement a) h i+
      tiltSecondOne σ u v (countedIncrement a) i=C2+2*J*h i) :
    (-(rateMatrix σ u v 0)).charpoly.coeff 1*J=(∏ i, u i)-(∏ i, v i) ∧
      (-(rateMatrix σ u v 0)).charpoly.coeff 1*C2+
        2*(-(rateMatrix σ u v 0)).charpoly.coeff 2*J^2=(∏ i, u i)+(∏ i, v i) := by
  have hz : ∀ i, ZeroJet2 (fun t =>
      (jetMatrix σ u v a J C2 t).mulVec (fun j => polyJet (h j) (k j) t) i) := by
    intro i
    have hid : (fun t => (jetMatrix σ u v a J C2 t).mulVec
        (fun j => polyJet (h j) (k j) t) i) =
        (fun t => UnicyclicResidualJets.residual σ u v (countedIncrement a) h k J C2 t i) := by
      funext t
      exact jetMatrix_mulVec σ hc hn u v h k a J C2 t i
    rw [hid]
    obtain ⟨h0,h1,h2⟩ := residual_jets_zero σ u v (countedIncrement a) h k J C2
      hfirst hsecond i
    exact ⟨h0,h1.deriv,h2.deriv⟩
  have hdet := determinant_zero_jet_of_residual
    (jetMatrix σ u v a J C2) (fun t i => polyJet (h i) (k i) t) a
    (contDiff_jetMatrix σ u v a J C2) (fun i => contDiff_polyJet (h i) (k i))
    (by simp [polyJet]) hz
  have hid : (fun t => (jetMatrix σ u v a J C2 t).det) =
      characteristicResidual (-(rateMatrix σ u v 0)).charpoly
        (∏ i, u i) (∏ i, v i) (quadraticBranch J C2) := by
    funext t
    exact jetMatrix_det σ hc hn u v a J C2 t
  rw [hid] at hdet
  exact quadratic_coefficient_equations_of_zero_residual_jet _ _ _ J C2
    hdet.2.1 hdet.2.2

#print axioms coefficient_equations_from_poisson
end
end UnicyclicRateJets
