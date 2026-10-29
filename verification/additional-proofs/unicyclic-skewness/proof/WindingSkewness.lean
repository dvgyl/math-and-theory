import ActualCycleBound
import RateReversal

/-!
Orientation-independent winding skewness theorem for arbitrary positive
nearest-neighbour rates on a finite cycle of at least three states.

The final theorem concerns actual derivatives of a local C³ zero-eigenvalue
branch of the actual counted-edge tilted generator. Existence of such a
branch is also proved. No spectral, stationary, variance, or uncertainty
conclusion appears among the hypotheses. The standard probabilistic
identification of this eigenvalue germ with long-time current cumulants is
explained in the research report, not implemented as a path-space theorem.
-/
namespace UnicyclicWinding
noncomputable section
open scoped BigOperators Topology
open Filter Equiv Polynomial
open UnicyclicDeterminant UnicyclicActual UnicyclicReversal UnicyclicCumulant
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 2000000

theorem rateSkewness_reversal (σ : Perm ι) (u v : ι → ℝ) :
    rateSkewness σ⁻¹ (fun j => v (σ⁻¹ j)) (fun j => u (σ⁻¹ j)) =
      rateSkewness σ u v := by
  exact rate_coefficient_skewness_reversal σ u v

theorem rate_coefficient_pos [Nonempty ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (hn : 3≤Fintype.card ι)
    (u v : ι → ℝ) (hu : ∀ i, 0<u i) (hv : ∀ i, 0<v i)
    (hUV : (∏ i, u i)≠∏ i, v i) (a : ι) :
    0<(ratePolynomial σ u v).coeff 1 := by
  rcases lt_or_gt_of_ne hUV with huv | hvu
  · have hrev : (∏ i, u (σ⁻¹ i))<(∏ i, v (σ⁻¹ i)) := by
      simpa only [Equiv.prod_comp] using huv
    have h := (positive_current_coefficient_data σ⁻¹ hc.inv hn
      (fun i => v (σ⁻¹ i)) (fun i => u (σ⁻¹ i))
      (fun i => hv _) (fun i => hu _) hrev a).1
    simpa only [ratePolynomial,rateMatrix_reversal] using h
  · exact (positive_current_coefficient_data σ hc hn u v hu hv hvu a).1

theorem rate_skewness_bounds [Nonempty ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (hn : 3≤Fintype.card ι)
    (u v : ι → ℝ) (hu : ∀ i, 0<u i) (hv : ∀ i, 0<v i)
    (hUV : (∏ i, u i)≠∏ i, v i) (a : ι) :
    -(1/16 : ℝ)≤rateSkewness σ u v ∧ rateSkewness σ u v≤1 := by
  rcases lt_or_gt_of_ne hUV with huv | hvu
  · have hrev : (∏ i, u (σ⁻¹ i))<(∏ i, v (σ⁻¹ i)) := by
      simpa only [Equiv.prod_comp] using huv
    have h := positive_current_skewness_bounds σ⁻¹ hc.inv hn
      (fun i => v (σ⁻¹ i)) (fun i => u (σ⁻¹ i))
      (fun i => hv _) (fun i => hu _) hrev a
    simpa only [rateSkewness_reversal] using h
  · exact positive_current_skewness_bounds σ hc hn u v hu hv hvu a

def tiltedCharacteristic (σ : Perm ι) (u v : ι → ℝ) (a : ι) (s z : ℝ) : ℝ :=
  (edgeTilt (rateMatrix σ u v z) a (σ a) (Real.exp s)).det

theorem tiltedCharacteristic_formula (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (hn : 3≤Fintype.card ι)
    (u v : ι → ℝ) (a : ι) (s z : ℝ) :
    tiltedCharacteristic σ u v a s z =
      (ratePolynomial σ u v).eval z-
        ((∏ i, u i)*(Real.exp s-1)+(∏ i, v i)*(Real.exp (-s)-1)) := by
  rw [tiltedCharacteristic,rateMatrix_determinant_tilt σ hc hn u v a z
    (Real.exp s) (Real.exp_ne_zero s)]
  dsimp only [ratePolynomial]
  rw [UnicyclicSpectral.charpoly_neg_eval,rateMatrix_add_scalar,Real.exp_neg]
  ring

/-- The current skewness interval for every smooth root germ of the actual
counted-edge tilted characteristic equation. -/
theorem winding_skewness_interval [Nonempty ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (hn : 3≤Fintype.card ι)
    (u v : ι → ℝ) (hu : ∀ i, 0<u i) (hv : ∀ i, 0<v i)
    (hUV : (∏ i, u i)≠∏ i, v i) (a : ι) (f : ℝ → ℝ)
    (hf : ContDiffAt ℝ 3 f 0) (hf0 : f 0=0)
    (hroot : ∀ᶠ s in 𝓝 (0 : ℝ), tiltedCharacteristic σ u v a s (f s)=0) :
    deriv f 0≠0 ∧
      -(1/16 : ℝ)≤deriv (deriv (deriv f)) 0/deriv f 0 ∧
      deriv (deriv (deriv f)) 0/deriv f 0≤1 := by
  have hp1 := rate_coefficient_pos σ hc hn u v hu hv hUV a
  have heq : ∀ᶠ s in 𝓝 (0 : ℝ),
      (ratePolynomial σ u v).eval (f s)=
        (∏ i, u i)*(Real.exp s-1)+(∏ i, v i)*(Real.exp (-s)-1) := by
    filter_upwards [hroot] with s hs
    rw [tiltedCharacteristic_formula σ hc hn] at hs
    exact sub_eq_zero.mp hs
  obtain ⟨h1,h2,h3⟩ := local_branch_derivatives (ratePolynomial σ u v)
    (∏ i, u i) (∏ i, v i) f (ne_of_gt hp1) hf hf0 heq
  have hnz : first ((ratePolynomial σ u v).coeff 1) (∏ i, u i) (∏ i, v i)≠0 :=
    div_ne_zero (sub_ne_zero.mpr hUV) (ne_of_gt hp1)
  rw [h1,h3]
  exact ⟨hnz,rate_skewness_bounds σ hc hn u v hu hv hUV a⟩

/-- Existence and the bound, obtained from the rates alone. -/
theorem exists_winding_branch_and_interval [Nonempty ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (hn : 3≤Fintype.card ι)
    (u v : ι → ℝ) (hu : ∀ i, 0<u i) (hv : ∀ i, 0<v i)
    (hUV : (∏ i, u i)≠∏ i, v i) (a : ι) :
    ∃ f : ℝ → ℝ, ContDiffAt ℝ 3 f 0 ∧ f 0=0 ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), tiltedCharacteristic σ u v a s (f s)=0) ∧
      deriv f 0≠0 ∧
      -(1/16 : ℝ)≤deriv (deriv (deriv f)) 0/deriv f 0 ∧
      deriv (deriv (deriv f)) 0/deriv f 0≤1 := by
  have hp0 : (ratePolynomial σ u v).eval 0=0 := by
    rw [ratePolynomial,UnicyclicSpectral.charpoly_neg_eval]
    simp only [zero_smul,zero_add]
    exact rateMatrix_det_zero σ u v (fun i => (hu i).le) (fun i => (hv i).le) a
  have hp1 := rate_coefficient_pos σ hc hn u v hu hv hUV a
  obtain ⟨f,hf,hf0,hroot⟩ := UnicyclicImplicit.exists_local_winding_branch
    (ratePolynomial σ u v) (∏ i, u i) (∏ i, v i) hp0 (ne_of_gt hp1)
  have hz : ∀ᶠ s in 𝓝 (0 : ℝ), tiltedCharacteristic σ u v a s (f s)=0 := by
    filter_upwards [hroot] with s hs
    rw [tiltedCharacteristic_formula σ hc hn,hs,sub_self]
  exact ⟨f,hf,hf0,hz,winding_skewness_interval σ hc hn u v hu hv hUV a f hf hf0 hz⟩

#print axioms rate_skewness_bounds
#print axioms winding_skewness_interval
#print axioms exists_winding_branch_and_interval
end
end UnicyclicWinding
