import CyclicPoisson
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Componentwise residual jets for the actual tilted row generator. -/
namespace UnicyclicResidualJets
noncomputable section
open scoped BigOperators
open Equiv UnicyclicPoisson
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 2000000

def polyJet (h k s : ℝ) : ℝ := 1+s*h+s^2*k/2
def polyJetD (h k s : ℝ) : ℝ := h+s*k
def lambdaJet (J C2 s : ℝ) : ℝ := J*s+C2*s^2/2
def lambdaJetD (J C2 s : ℝ) : ℝ := J+C2*s
def expPoly (d h k s : ℝ) : ℝ := Real.exp (s*d)*polyJet h k s
def expPolyD (d h k s : ℝ) : ℝ :=
  Real.exp (s*d)*(d*polyJet h k s+polyJetD h k s)
def expPolyDD (d h k s : ℝ) : ℝ :=
  Real.exp (s*d)*(d^2*polyJet h k s+2*d*polyJetD h k s+k)

theorem hasDerivAt_polyJet (h k s : ℝ) :
    HasDerivAt (polyJet h k) (polyJetD h k s) s := by
  convert (((hasDerivAt_const s (1 : ℝ)).add ((hasDerivAt_id s).mul_const h)).add
    ((((hasDerivAt_id s).pow 2).mul_const k).div_const 2)) using 1 ;
    dsimp [polyJet, polyJetD] ; ring

theorem hasDerivAt_polyJetD (h k s : ℝ) :
    HasDerivAt (polyJetD h k) k s := by
  simpa only [polyJetD, one_mul] using ((hasDerivAt_id s).mul_const k).const_add h

theorem hasDerivAt_lambdaJet (J C2 s : ℝ) :
    HasDerivAt (lambdaJet J C2) (lambdaJetD J C2 s) s := by
  convert (((hasDerivAt_id s).const_mul J).add
    ((((hasDerivAt_id s).pow 2).const_mul C2).div_const 2)) using 1 ;
    dsimp [lambdaJet, lambdaJetD] ; ring

theorem hasDerivAt_lambdaJetD (J C2 s : ℝ) :
    HasDerivAt (lambdaJetD J C2) C2 s := by
  simpa only [lambdaJetD, mul_one] using ((hasDerivAt_id s).const_mul C2).const_add J

theorem hasDerivAt_exp_scaled (d s : ℝ) :
    HasDerivAt (fun t => Real.exp (t*d)) (d*Real.exp (s*d)) s := by
  simpa [mul_comm] using ((hasDerivAt_id s).mul_const d).exp

theorem hasDerivAt_expPoly (d h k s : ℝ) :
    HasDerivAt (expPoly d h k) (expPolyD d h k s) s := by
  convert (hasDerivAt_exp_scaled d s).mul (hasDerivAt_polyJet h k s) using 1 ;
    dsimp [expPoly, expPolyD] ; ring

theorem hasDerivAt_expPolyD (d h k s : ℝ) :
    HasDerivAt (expPolyD d h k) (expPolyDD d h k s) s := by
  convert (hasDerivAt_exp_scaled d s).mul
    (((hasDerivAt_polyJet h k s).const_mul d).add (hasDerivAt_polyJetD h k s)) using 1 ;
    dsimp [expPolyD, expPolyDD] ; ring

def residual (σ : Perm ι) (u v d h k : ι → ℝ) (J C2 s : ℝ) (i : ι) : ℝ :=
  lambdaJet J C2 s*polyJet (h i) (k i) s-
    u i*expPoly (d i) (h (σ i)) (k (σ i)) s-
    v (σ⁻¹ i)*expPoly (-d (σ⁻¹ i)) (h (σ⁻¹ i)) (k (σ⁻¹ i)) s+
    (u i+v (σ⁻¹ i))*polyJet (h i) (k i) s

def residualD (σ : Perm ι) (u v d h k : ι → ℝ) (J C2 s : ℝ) (i : ι) : ℝ :=
  (lambdaJetD J C2 s*polyJet (h i) (k i) s+
    lambdaJet J C2 s*polyJetD (h i) (k i) s)-
    u i*expPolyD (d i) (h (σ i)) (k (σ i)) s-
    v (σ⁻¹ i)*expPolyD (-d (σ⁻¹ i)) (h (σ⁻¹ i)) (k (σ⁻¹ i)) s+
    (u i+v (σ⁻¹ i))*polyJetD (h i) (k i) s

def residualDD (σ : Perm ι) (u v d h k : ι → ℝ) (J C2 s : ℝ) (i : ι) : ℝ :=
  (C2*polyJet (h i) (k i) s+2*lambdaJetD J C2 s*polyJetD (h i) (k i) s+
    lambdaJet J C2 s*k i)-
    u i*expPolyDD (d i) (h (σ i)) (k (σ i)) s-
    v (σ⁻¹ i)*expPolyDD (-d (σ⁻¹ i)) (h (σ⁻¹ i)) (k (σ⁻¹ i)) s+
    (u i+v (σ⁻¹ i))*k i

omit [Fintype ι] [DecidableEq ι] in
theorem hasDerivAt_residual [Fintype ι] [DecidableEq ι] (σ : Perm ι) (u v d h k : ι → ℝ)
    (J C2 s : ℝ) (i : ι) :
    HasDerivAt (fun t => residual σ u v d h k J C2 t i)
      (residualD σ u v d h k J C2 s i) s := by
  convert ((((hasDerivAt_lambdaJet J C2 s).mul (hasDerivAt_polyJet (h i) (k i) s)).sub
    ((hasDerivAt_expPoly (d i) (h (σ i)) (k (σ i)) s).const_mul (u i))).sub
    ((hasDerivAt_expPoly (-d (σ⁻¹ i)) (h (σ⁻¹ i)) (k (σ⁻¹ i)) s).const_mul (v (σ⁻¹ i)))).add
    ((hasDerivAt_polyJet (h i) (k i) s).const_mul (u i+v (σ⁻¹ i))) using 1

omit [Fintype ι] [DecidableEq ι] in
theorem hasDerivAt_residualD [Fintype ι] [DecidableEq ι] (σ : Perm ι) (u v d h k : ι → ℝ)
    (J C2 s : ℝ) (i : ι) :
    HasDerivAt (fun t => residualD σ u v d h k J C2 t i)
      (residualDD σ u v d h k J C2 s i) s := by
  have hfirst := ((hasDerivAt_lambdaJetD J C2 s).mul
    (hasDerivAt_polyJet (h i) (k i) s)).add
    ((hasDerivAt_lambdaJet J C2 s).mul (hasDerivAt_polyJetD (h i) (k i) s))
  have hfwd := hfirst.sub
    ((hasDerivAt_expPolyD (d i) (h (σ i)) (k (σ i)) s).const_mul (u i))
  have hback := hfwd.sub
    ((hasDerivAt_expPolyD (-d (σ⁻¹ i)) (h (σ⁻¹ i)) (k (σ⁻¹ i)) s).const_mul (v (σ⁻¹ i)))
  have hall := hback.add
    ((hasDerivAt_polyJetD (h i) (k i) s).const_mul (u i+v (σ⁻¹ i)))
  convert hall using 1 ;
    dsimp [residualD, residualDD] ; ring

omit [Fintype ι] [DecidableEq ι] in
theorem residual_zero [Fintype ι] [DecidableEq ι] (σ : Perm ι) (u v d h k : ι → ℝ) (J C2 : ℝ) (i : ι) :
    residual σ u v d h k J C2 0 i=0 := by
  simp [residual, lambdaJet, polyJet, expPoly]

omit [Fintype ι] [DecidableEq ι] in
theorem residualD_zero [Fintype ι] [DecidableEq ι] (σ : Perm ι) (u v d h k : ι → ℝ) (J C2 : ℝ)
    (hfirst : ∀ i, generator σ u v h i+drift σ u v d i=J) (i : ι) :
    residualD σ u v d h k J C2 0 i=0 := by
  have hh := hfirst i
  dsimp [generator, drift] at hh
  simp only [residualD, lambdaJet, lambdaJetD, polyJet, polyJetD, expPolyD,
    zero_mul, mul_zero, zero_pow (by decide : 2≠0), zero_div, add_zero,
    zero_add, Real.exp_zero, one_mul]
  nlinarith only [hh]

omit [Fintype ι] [DecidableEq ι] in
theorem residualDD_zero [Fintype ι] [DecidableEq ι] (σ : Perm ι) (u v d h k : ι → ℝ) (J C2 : ℝ)
    (hsecond : ∀ i, generator σ u v k i+2*tiltFirst σ u v d h i+
      tiltSecondOne σ u v d i=C2+2*J*h i) (i : ι) :
    residualDD σ u v d h k J C2 0 i=0 := by
  have hh := hsecond i
  dsimp [generator, tiltFirst, tiltSecondOne] at hh
  simp only [residualDD, lambdaJet, lambdaJetD, polyJet, polyJetD, expPolyDD,
    zero_mul, mul_zero, zero_pow (by decide : 2≠0), zero_div, add_zero,
    zero_add, Real.exp_zero, one_mul]
  nlinarith only [hh]

theorem residual_jets_zero (σ : Perm ι) (u v d h k : ι → ℝ) (J C2 : ℝ)
    (hfirst : ∀ i, generator σ u v h i+drift σ u v d i=J)
    (hsecond : ∀ i, generator σ u v k i+2*tiltFirst σ u v d h i+
      tiltSecondOne σ u v d i=C2+2*J*h i) (i : ι) :
    residual σ u v d h k J C2 0 i=0 ∧
      HasDerivAt (fun t => residual σ u v d h k J C2 t i) 0 0 ∧
      HasDerivAt (deriv (fun t => residual σ u v d h k J C2 t i)) 0 0 := by
  refine ⟨residual_zero σ u v d h k J C2 i, ?_, ?_⟩
  · have hh := hasDerivAt_residual σ u v d h k J C2 0 i
    rwa [residualD_zero σ u v d h k J C2 hfirst i] at hh
  · have hd : deriv (fun t => residual σ u v d h k J C2 t i) =
        fun t => residualD σ u v d h k J C2 t i := by
      funext t
      exact (hasDerivAt_residual σ u v d h k J C2 t i).deriv
    rw [hd]
    have hh := hasDerivAt_residualD σ u v d h k J C2 0 i
    rwa [residualDD_zero σ u v d h k J C2 hsecond i] at hh

theorem residual_derivatives_zero (σ : Perm ι) (u v d h k : ι → ℝ) (J C2 : ℝ)
    (hfirst : ∀ i, generator σ u v h i+drift σ u v d i=J)
    (hsecond : ∀ i, generator σ u v k i+2*tiltFirst σ u v d h i+
      tiltSecondOne σ u v d i=C2+2*J*h i) (i : ι) :
    residual σ u v d h k J C2 0 i=0 ∧
      deriv (fun t => residual σ u v d h k J C2 t i) 0=0 ∧
      deriv (deriv (fun t => residual σ u v d h k J C2 t i)) 0=0 := by
  obtain ⟨h0,h1,h2⟩ := residual_jets_zero σ u v d h k J C2 hfirst hsecond i
  exact ⟨h0,h1.deriv,h2.deriv⟩

end
end UnicyclicResidualJets

#print axioms UnicyclicResidualJets.residual_jets_zero
#print axioms UnicyclicResidualJets.residual_derivatives_zero
