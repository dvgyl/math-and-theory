import SpectralPolynomialBound
import PositiveRateSpectrum
import RateJets

/-!
The winding-current characteristic-coefficient inequality for arbitrary
strictly positive nearest-neighbour rates on a finite cycle with positive
affinity. All stationary, variance, spectral, and uncertainty ingredients
are constructed or proved from the rates.
-/
namespace UnicyclicActual
noncomputable section
open scoped BigOperators
open Equiv Polynomial UnicyclicDeterminant UnicyclicPoisson UnicyclicRateJets
open UnicyclicCumulant
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 2000000

def ratePolynomial (σ : Perm ι) (u v : ι → ℝ) : Polynomial ℝ :=
  (-(rateMatrix σ u v 0)).charpoly

def rateSkewness (σ : Perm ι) (u v : ι → ℝ) : ℝ :=
  third ((ratePolynomial σ u v).coeff 1) ((ratePolynomial σ u v).coeff 2)
    ((ratePolynomial σ u v).coeff 3) (∏ i, u i) (∏ i, v i) /
      first ((ratePolynomial σ u v).coeff 1) (∏ i, u i) (∏ i, v i)

theorem positive_current_coefficient_data [Nonempty ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (hn : 3≤Fintype.card ι)
    (u v : ι → ℝ) (hu : ∀ i, 0<u i) (hv : ∀ i, 0<v i)
    (hUV : (∏ i, v i)<∏ i, u i) (a : ι) :
    0<(ratePolynomial σ u v).coeff 1 ∧
      2/Real.log ((∏ i, u i)/(∏ i, v i)) ≤
        second ((ratePolynomial σ u v).coeff 1) ((ratePolynomial σ u v).coeff 2)
          (∏ i, u i) (∏ i, v i) /
        first ((ratePolynomial σ u v).coeff 1) (∏ i, u i) (∏ i, v i) := by
  obtain ⟨π,h,k,J,C2,hπ,hnorm,hJ,hflux,hcenter,hkcenter,hfirst,hsecond,hC2⟩ :=
    exists_two_coefficients σ hc u v (countedIncrement a) hu hv hUV
      (countedIncrement_sum a)
  obtain ⟨hc1,hc2⟩ := coefficient_equations_from_poisson σ hc hn u v h k a J C2
    hfirst hsecond
  change (ratePolynomial σ u v).coeff 1*J=(∏ i, u i)-(∏ i, v i) at hc1
  change (ratePolynomial σ u v).coeff 1*C2+
      2*(ratePolynomial σ u v).coeff 2*J^2=(∏ i, u i)+(∏ i, v i) at hc2
  have ha1 : 0<(ratePolynomial σ u v).coeff 1 := by
    have hp : 0<(ratePolynomial σ u v).coeff 1*J := by rw [hc1]; linarith
    exact (mul_pos_iff_of_pos_right hJ).mp hp
  have hJdef : first ((ratePolynomial σ u v).coeff 1) (∏ i, u i) (∏ i, v i)=J := by
    apply (div_eq_iff (ne_of_gt ha1)).mpr
    nlinarith only [hc1]
  have hC2def : second ((ratePolynomial σ u v).coeff 1) ((ratePolynomial σ u v).coeff 2)
      (∏ i, u i) (∏ i, v i)=C2 := by
    dsimp only [second]
    rw [hJdef]
    apply (div_eq_iff (ne_of_gt ha1)).mpr
    nlinarith only [hc2]
  refine ⟨ha1, ?_⟩
  rw [hJdef,hC2def,hC2]
  exact edgeQuadratic_tur σ u v (countedIncrement a) π h J hu hv hπ hJ hflux
    (countedIncrement_sum a)

theorem positive_current_skewness_bounds [Nonempty ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (hn : 3≤Fintype.card ι)
    (u v : ι → ℝ) (hu : ∀ i, 0<u i) (hv : ∀ i, 0<v i)
    (hUV : (∏ i, v i)<∏ i, u i) (i0 : ι) :
    -(1/16 : ℝ) ≤ rateSkewness σ u v ∧ rateSkewness σ u v ≤ 1 := by
  let a := ∏ i, Real.sqrt (u i)
  let b := ∏ i, Real.sqrt (v i)
  have ha : 0<a := Finset.prod_pos (fun i _ => Real.sqrt_pos.mpr (hu i))
  have hb : 0<b := Finset.prod_pos (fun i _ => Real.sqrt_pos.mpr (hv i))
  have hau : a^2=∏ i, u i := sqrt_product_square u (fun i => (hu i).le)
  have hbv : b^2=∏ i, v i := sqrt_product_square v (fun i => (hv i).le)
  have hba : b<a := by nlinarith only [hau,hbv,hUV,ha,hb]
  obtain ⟨theta,htheta,hfactor,hd,hp0⟩ := positive_rate_spectral_factorization
    σ hc hn u v hu hv (ne_of_gt hUV) i0
  obtain ⟨ha1,htur⟩ := positive_current_coefficient_data σ hc hn u v hu hv hUV i0
  have hlog : Real.log ((∏ i, u i)/(∏ i, v i))=2*Real.log (a/b) := by
    rw [← hau,← hbv,← div_pow,Real.log_pow]
    norm_num
  have hlogpos : 0<Real.log (a/b) := Real.log_pos ((one_lt_div hb).mpr hba)
  have hfrac : 2/(2*Real.log (a/b))=1/Real.log (a/b) := by
    field_simp [ne_of_gt hlogpos]
  rw [hlog,hfrac,← hau,← hbv] at htur
  have hbound := UnicyclicPolynomial.bound_from_spectral_shift_and_uncertainty
    (Finset.univ : Finset ι) Finset.univ_nonempty theta (ratePolynomial σ u v)
    a b ha hb hba (fun i _ => htheta i) hd hfactor htur
  simpa only [rateSkewness,hau,hbv] using hbound

theorem fin_ring_positive_current_skewness_bounds (n : ℕ) (hn : 3≤n)
    (u v : Fin n → ℝ) (hu : ∀ i, 0<u i) (hv : ∀ i, 0<v i)
    (hUV : (∏ i, v i)<∏ i, u i) :
    -(1/16 : ℝ) ≤ rateSkewness (finRotate n) u v ∧
      rateSkewness (finRotate n) u v ≤ 1 := by
  let i0 : Fin n := ⟨0, by omega⟩
  letI : Nonempty (Fin n) := ⟨i0⟩
  exact positive_current_skewness_bounds (finRotate n)
    (finRotate_isCycleOn n (by omega)) (by simpa using hn) u v hu hv hUV i0

#print axioms positive_current_coefficient_data
#print axioms positive_current_skewness_bounds
#print axioms fin_ring_positive_current_skewness_bounds
end
end UnicyclicActual
