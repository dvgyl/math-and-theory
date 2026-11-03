import QuantumConsequences
import QuantumFilters
import FilterReduction
import Shortcut

/-!
Assembly of actual complex density-matrix identities and the checked global
real optimization.  The observables here are the explicitly defined Pauli
correlation-plane function.  The additional equivalence to four-observable
CHSH and the polar-decomposition/whitening reduction for arbitrary GL filters
are not asserted by this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
open scoped Matrix ComplexOrder
open Matrix

namespace UnilateralCHSH.Quantum

def correlationColumn (ρ : State) (j : Fin 3) : Vec := fun i => correlation ρ i j

def physicalPlane (ρ : State) (n : Vec) : ℝ :=
  planeColumnValue n (correlationColumn ρ 0) +
  planeColumnValue n (correlationColumn ρ 1) +
  planeColumnValue n (correlationColumn ρ 2)

theorem covariance_symmetric (D : Mat3) : ∀ i j, covariance D i j = covariance D j i := by
  intro i j
  simp only [covariance, matProduct, Matrix.transpose_apply]
  ring

theorem positive_filter_plane (c u n : Vec) (D : Mat3) (hu : normSq u ≤ 1) :
    physicalPlane (filtered (canonical c D) (positiveFilter u)) n =
      filteredPlaneValue D c u n (Real.sqrt (1-normSq u)) := by
  have hc (j : Fin 3) : correlationColumn (filtered (canonical c D) (positiveFilter u)) j =
      filteredColumn u (column D j) (filterRadius u) (c j) := by
    funext i
    exact positive_filter_correlation c u D hu i j
  unfold physicalPlane filteredPlaneValue
  rw [hc 0,hc 1,hc 2]
  rfl

def physicalPlaneValues (c : Vec) (D : Mat3) : Set ℝ :=
  {b | ∃ u n : Vec, normSq u ≤ 1 ∧ normSq n = 1 ∧
    physicalPlane (filtered (canonical c D) (positiveFilter u)) n = b}

theorem physicalPlaneValues_eq_real (c : Vec) (D : Mat3) :
    physicalPlaneValues c D = Reduction.filterPlaneValues D c := by
  ext b
  constructor <;> rintro ⟨u,n,hu,hn,h⟩ <;> refine ⟨u,n,hu,hn,?_⟩
  · rwa [positive_filter_plane c u n D hu] at h
  · rwa [positive_filter_plane c u n D hu]

/-- An exact global theorem for the explicitly defined physical positive
filter family and its Pauli correlation planes.  No KKT or optimizer
existence assumptions occur in this statement. -/
theorem exact_physical_positive_filter_maximum (c : Vec) (D : Mat3) :
    IsGreatest (physicalPlaneValues c D) (Reduction.canonicalMaximum D c) := by
  rw [physicalPlaneValues_eq_real]
  exact Reduction.exact_real_filter_maximum D c

theorem canonical_reduced_shortcut (c : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef)
    (hguard : 1 < traceThree (covariance D)-normSq c) :
    let K := shift (covariance D) (-normSq c)
    let C := crossMatrix (matVec D c)
    let alpha := traceThree (covariance D)-normSq c
    K.det ≠ 0 ∧ ∃ (r : ℝ) (n v : Vec),
      0 < r ∧ normSq n = 1 ∧ dot n v = 0 ∧ normSq v < 1 ∧
      v = Shortcut.liftV K⁻¹ C n ∧
      matVec (schurMatrix K C K⁻¹) n = (fun i => r*n i) ∧
      (∀ x : Vec, r*normSq x ≤ quad (schurMatrix K C K⁻¹) x) ∧
      reducedObjective (covariance D) C (normSq c) (traceThree (covariance D)) n v = alpha-r ∧
      Reduction.canonicalMaximum D c = alpha-r := by
  dsimp only
  let K := shift (covariance D) (-normSq c)
  let C := crossMatrix (matVec D c)
  let alpha := traceThree (covariance D)-normSq c
  have hm : 0 < purityMargin c D := by unfold purityMargin; linarith
  obtain ⟨hd,r,n,v,hr,hn,hnv,hv,hvdef,heigen,hmin,hvalue,hupper⟩ :=
    Shortcut.strict_block_schur_maximum K C alpha (purityMargin c D)
      (shift_symmetric (covariance D) (-normSq c) (covariance_symmetric D))
      (crossMatrix_skew (matVec D c)) hm
      (fun x y => physical_spinflip_gram_bound c x y D hρ)
  have heq : reducedObjective (covariance D) C (normSq c)
      (traceThree (covariance D)) n v = alpha-r := by
    rw [Shortcut.reduced_equals_energy _ _ _ _ _ _ hn]
    exact hvalue
  refine ⟨hd,r,n,v,hr,hn,hnv,hv,hvdef,heigen,hmin,heq,?_⟩
  apply le_antisymm
  · let p := Global.maximizer (covariance D) C (normSq c) (traceThree (covariance D))
    have hp := (Global.maximizer_spec (covariance D) C (normSq c) (traceThree (covariance D))).1
    change reducedObjective (covariance D) C (normSq c)
      (traceThree (covariance D)) p.1 p.2 ≤ alpha-r
    rw [Shortcut.reduced_equals_energy _ _ _ _ _ _ hp.1]
    exact hupper p.1 p.2 hp.1
  · have hb := Global.feasible_value_le_maximum (covariance D) C (normSq c)
      (traceThree (covariance D)) (n,v) ⟨hn,hnv,le_of_lt hv⟩
    change reducedObjective (covariance D) C (normSq c)
      (traceThree (covariance D)) n v ≤ _ at hb
    rwa [heq] at hb

/-- A physical state alone supplies the Gram hypothesis, the actual inverse,
the least eigenpair, an invertible Kraus witness, and a bound for every
positive-filter correlation plane in the closed effect ball. -/
theorem canonical_physical_shortcut (c : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef)
    (hguard : 1 < traceThree (covariance D)-normSq c) :
    ∃ (r : ℝ) (u n : Vec), 0 < r ∧ normSq u < 1 ∧ normSq n = 1 ∧
      (positiveFilter u).det ≠ 0 ∧
      (filtered (canonical c D) (positiveFilter u)).PosSemidef ∧
      Matrix.trace (filtered (canonical c D) (positiveFilter u)) = 1 ∧
      physicalPlane (filtered (canonical c D) (positiveFilter u)) n =
        traceThree (covariance D)-normSq c-r ∧
      (∀ w z : Vec, normSq w ≤ 1 → normSq z = 1 →
        physicalPlane (filtered (canonical c D) (positiveFilter w)) z ≤
          traceThree (covariance D)-normSq c-r) := by
  obtain ⟨_,r,n,v,hr,hn,hnv,hv,_,_,_,hvalue,hmaximum⟩ :=
    canonical_reduced_shortcut c D hρ hguard
  let u : Vec := fun i => -cross n v i
  have hu : normSq u < 1 := by
    rw [tangent_cross_norm n v hn hnv]
    exact hv
  have hdensity := positive_filter_density c u D hρ (le_of_lt hu)
  refine ⟨r,u,n,hr,hu,hn,positive_filter_invertible u hu,
    hdensity.1,hdensity.2,?_,?_⟩
  · rw [positive_filter_plane c u n D (le_of_lt hu)]
    rw [exact_bivector_filter_construction D c n v hn hnv (le_of_lt hv)]
    exact hvalue
  · intro w z hw hz
    rw [positive_filter_plane c w z D hw]
    rw [← hmaximum]
    exact Reduction.every_filter_plane_le_canonicalMaximum D c w z hz hw

theorem canonical_maximum_violation_requires_guard (c : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef)
    (hviol : 1 < Reduction.canonicalMaximum D c) :
    1 < traceThree (covariance D)-normSq c := by
  let p := Global.maximizer (covariance D) (crossMatrix (matVec D c))
    (normSq c) (traceThree (covariance D))
  have hp := (Global.maximizer_spec (covariance D) (crossMatrix (matVec D c))
    (normSq c) (traceThree (covariance D))).1
  exact physical_violation_requires_guard c p.1 p.2 D hρ hp.1 hp.2.2 hviol

/-- Necessary and sufficient physical activation criterion for the full
positive-filter/Pauli-plane model.  The right side is a strict Rayleigh
inequality for a single explicit actual-inverse Schur matrix. -/
theorem canonical_activation_iff (c : Vec) (D : Mat3)
    (hρ : (canonical c D).PosSemidef) :
    (∃ u n : Vec, normSq u ≤ 1 ∧ normSq n = 1 ∧
      1 < physicalPlane (filtered (canonical c D) (positiveFilter u)) n) ↔
    (1 < traceThree (covariance D)-normSq c ∧
      ∃ n : Vec, normSq n = 1 ∧
        quad (schurMatrix (shift (covariance D) (-normSq c))
          (crossMatrix (matVec D c)) (shift (covariance D) (-normSq c))⁻¹) n <
            traceThree (covariance D)-normSq c-1) := by
  constructor
  · rintro ⟨u,n,hu,hn,hviol⟩
    have hub := (exact_physical_positive_filter_maximum c D).2
      ⟨u,n,hu,hn,rfl⟩
    have hmax : 1 < Reduction.canonicalMaximum D c := lt_of_lt_of_le hviol hub
    have hg := canonical_maximum_violation_requires_guard c D hρ hmax
    obtain ⟨_,r,x,v,_,hx,_,_,_,he,_,_,hvalue⟩ :=
      canonical_reduced_shortcut c D hρ hg
    have hq : quad (schurMatrix (shift (covariance D) (-normSq c))
        (crossMatrix (matVec D c)) (shift (covariance D) (-normSq c))⁻¹) x = r := by
      unfold quad
      rw [he, dot_scale_right]
      change r * normSq x = r
      rw [hx,mul_one]
    refine ⟨hg,x,hx,?_⟩
    rw [hq]
    rw [hvalue] at hmax
    linarith
  · rintro ⟨hg,n,hn,hq⟩
    obtain ⟨_,r,x,v,_,_,_,_,_,_,hmin,_,hvalue⟩ :=
      canonical_reduced_shortcut c D hρ hg
    have hr := hmin n
    rw [hn,mul_one] at hr
    have hmax : 1 < Reduction.canonicalMaximum D c := by rw [hvalue]; linarith
    obtain ⟨u,z,hu,hz,heq⟩ := (exact_physical_positive_filter_maximum c D).1
    exact ⟨u,z,hu,hz,by rwa [heq]⟩

end UnilateralCHSH.Quantum
