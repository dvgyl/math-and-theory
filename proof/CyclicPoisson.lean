module
public import CyclicConstruction
public import FiniteTUR

@[expose] public section

/-! Finite Poisson solvability and perturbation coefficients for actual cyclic
rates. These definitions use the generator acting on functions (the transpose
of the column generator used in the determinant development). -/
namespace UnicyclicPoisson
noncomputable section
open scoped BigOperators
open Equiv UnicyclicConstruction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 2000000

def generator (σ : Perm ι) (u v f : ι → ℝ) (i : ι) : ℝ :=
  u i*(f (σ i)-f i)+v (σ⁻¹ i)*(f (σ⁻¹ i)-f i)

def drift (σ : Perm ι) (u v d : ι → ℝ) (i : ι) : ℝ :=
  u i*d i-v (σ⁻¹ i)*d (σ⁻¹ i)

def tiltFirst (σ : Perm ι) (u v d f : ι → ℝ) (i : ι) : ℝ :=
  u i*d i*f (σ i)-v (σ⁻¹ i)*d (σ⁻¹ i)*f (σ⁻¹ i)

def tiltSecondOne (σ : Perm ι) (u v d : ι → ℝ) (i : ι) : ℝ :=
  u i*d i^2+v (σ⁻¹ i)*d (σ⁻¹ i)^2

omit [Fintype ι] [DecidableEq ι] in
theorem weighted_gradient_sum [Fintype ι] [DecidableEq ι] (σ : Perm ι) (u v π g : ι → ℝ) (J : ℝ)
    (hflux : ∀ i, π i*u i-π (σ i)*v i=J) :
    (∑ i, π i*(u i*g i-v (σ⁻¹ i)*g (σ⁻¹ i))) = J*(∑ i, g i) := by
  have hreindex :
      (∑ i, π i*(v (σ⁻¹ i)*g (σ⁻¹ i))) =
        ∑ i, π (σ i)*(v i*g i) := by
    simpa only [Perm.inv_apply_self] using
      (Equiv.sum_comp σ (fun i => π i*(v (σ⁻¹ i)*g (σ⁻¹ i)))).symm
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hreindex, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ i, (π i*u i-π (σ i)*v i)*g i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i, J*g i := by simp_rw [hflux]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem stationary_generator_zero (σ : Perm ι) (u v π f : ι → ℝ) (J : ℝ)
    (hflux : ∀ i, π i*u i-π (σ i)*v i=J) :
    (∑ i, π i*generator σ u v f i)=0 := by
  have hh := weighted_gradient_sum σ u v π (fun i => f (σ i)-f i) J hflux
  have he (i : ι) :
      u i*(f (σ i)-f i)-v (σ⁻¹ i)*(f (σ (σ⁻¹ i))-f (σ⁻¹ i)) =
        generator σ u v f i := by
    simp only [Perm.apply_inv_self, generator]
    ring
  simp_rw [he] at hh
  simpa only [Finset.sum_sub_distrib, Equiv.sum_comp σ f, sub_self, mul_zero] using hh

theorem exists_signed_cyclic_solution (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (ρ f : ι → ℝ)
    (hprod : (∏ i, ρ i)<1) :
    ∃ x : ι → ℝ, ∀ i, x i-ρ i*x (σ i)=f i := by
  let Z : ℝ := 1-∏ i, ρ i
  have hZ : 0<Z := sub_pos.mpr hprod
  refine ⟨fun i => green σ ρ f (Fintype.card ι) i/Z, ?_⟩
  intro i
  have hh := green_recurrence σ hc ρ f i
  calc
    _ = (green σ ρ f (Fintype.card ι) i-
          ρ i*green σ ρ f (Fintype.card ι) (σ i))/Z := by ring
    _ = f i := by
      rw [hh]
      change Z*f i/Z=f i
      field_simp [ne_of_gt hZ]

/-- Every zero-stationary-mean forcing has a centered Poisson solution,
constructed through a finite cyclic Green sum. -/
theorem exists_centered_poisson [Nonempty ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (u v π f : ι → ℝ) (J : ℝ)
    (hu : ∀ i, 0<u i) (_hv : ∀ i, 0<v i)
    (hUV : (∏ i, v i)<∏ i, u i)
    (hnorm : (∑ i, π i)=1) (hJ : J≠0)
    (hflux : ∀ i, π i*u i-π (σ i)*v i=J)
    (hf : (∑ i, π i*f i)=0) :
    ∃ h : ι → ℝ, (∑ i, π i*h i)=0 ∧ ∀ i, generator σ u v h i=f i := by
  have hup : 0<∏ i, u i := Finset.prod_pos (fun i hi => hu i)
  have hp : (∏ i, v (σ⁻¹ i)/u i)<1 := by
    rw [Finset.prod_div_distrib, Equiv.prod_comp σ⁻¹ v]
    exact (div_lt_one hup).mpr hUV
  obtain ⟨g,he⟩ := exists_signed_cyclic_solution σ⁻¹ hc.inv
    (fun i => v (σ⁻¹ i)/u i) (fun i => f i/u i) hp
  have hrec : ∀ i, u i*g i-v (σ⁻¹ i)*g (σ⁻¹ i)=f i := by
    intro i
    have hh := congrArg (fun z : ℝ => u i*z) (he i)
    field_simp [ne_of_gt (hu i)] at hh
    simp only [one_div] at hh
    nlinarith only [hh]
  have hgsum : (∑ i, g i)=0 := by
    have hh := weighted_gradient_sum σ u v π g J hflux
    simp_rw [hrec] at hh
    rw [hf] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hJ
  obtain ⟨h,hdiff⟩ := exists_cyclic_coboundary σ hc g hgsum
  let μ : ℝ := ∑ i, π i*h i
  refine ⟨fun i => h i-μ, ?_, ?_⟩
  · simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hnorm]
    dsimp [μ]
    ring
  · intro i
    have hfwd : (h (σ i)-μ)-(h i-μ)=g i := by
      have hh := hdiff i
      linarith only [hh]
    have hback : (h (σ⁻¹ i)-μ)-(h i-μ)= -g (σ⁻¹ i) := by
      have hh := hdiff (σ⁻¹ i)
      simp only [Perm.apply_inv_self] at hh
      linarith only [hh]
    simp only [generator, hfwd, hback]
    nlinarith only [hrec i]

def secondCoefficient (σ : Perm ι) (u v d π h : ι → ℝ) : ℝ :=
  ∑ i, π i*(tiltSecondOne σ u v d i+2*tiltFirst σ u v d h i)

def edgeQuadratic (σ : Perm ι) (u v d π h : ι → ℝ) : ℝ :=
  ∑ i, (π i*u i+π (σ i)*v i)*(d i+h (σ i)-h i)^2

theorem secondCoefficient_eq_edgeQuadratic (σ : Perm ι)
    (u v d π h : ι → ℝ) (J : ℝ)
    (hflux : ∀ i, π i*u i-π (σ i)*v i=J)
    (hcenter : (∑ i, π i*h i)=0)
    (hcorr : ∀ i, generator σ u v h i+drift σ u v d i=J) :
    secondCoefficient σ u v d π h = edgeQuadratic σ u v d π h := by
  let K : ι → ℝ := fun i =>
    u i*(d i+h (σ i)-h i)^2+
      v (σ⁻¹ i)*(d (σ⁻¹ i)+h i-h (σ⁻¹ i))^2
  have hpoint (i : ι) :
      K i+2*h i*J =
        (tiltSecondOne σ u v d i+2*tiltFirst σ u v d h i)+
          generator σ u v (fun i => h i^2) i := by
    rw [← hcorr i]
    dsimp [K, generator, drift, tiltSecondOne, tiltFirst]
    ring
  have hs :
      (∑ i, (π i*K i+2*J*(π i*h i))) =
        ∑ i, (π i*(tiltSecondOne σ u v d i+2*tiltFirst σ u v d h i)+
          π i*generator σ u v (fun i => h i^2) i) := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = π i*(K i+2*h i*J) := by ring
      _ = π i*((tiltSecondOne σ u v d i+2*tiltFirst σ u v d h i)+
            generator σ u v (fun i => h i^2) i) := by rw [hpoint i]
      _ = _ := by ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [hcenter, stationary_generator_zero σ u v π (fun i => h i^2) J hflux] at hs
  have hK : (∑ i, π i*K i)=secondCoefficient σ u v d π h := by
    dsimp only [secondCoefficient]
    linarith only [hs]
  have hreindex :
      (∑ i, π i*v (σ⁻¹ i)*(d (σ⁻¹ i)+h i-h (σ⁻¹ i))^2) =
        ∑ i, π (σ i)*v i*(d i+h (σ i)-h i)^2 := by
    simpa only [Perm.inv_apply_self] using
      (Equiv.sum_comp σ (fun i =>
        π i*v (σ⁻¹ i)*(d (σ⁻¹ i)+h i-h (σ⁻¹ i))^2)).symm
  have hKedge : (∑ i, π i*K i)=edgeQuadratic σ u v d π h := by
    dsimp only [K, edgeQuadratic]
    simp only [mul_add, add_mul, Finset.sum_add_distrib, ← mul_assoc]
    rw [hreindex]
  exact hK.symm.trans hKedge

/-- Construct genuine first and second perturbation coefficients from the
rates, including the centered first and second vector coefficients. -/
theorem exists_two_coefficients [Nonempty ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (u v d : ι → ℝ)
    (hu : ∀ i, 0<u i) (hv : ∀ i, 0<v i)
    (hUV : (∏ i, v i)<∏ i, u i) (hd : (∑ i, d i)=1) :
    ∃ (π h k : ι → ℝ) (J C2 : ℝ),
      (∀ i, 0<π i) ∧ (∑ i, π i)=1 ∧ 0<J ∧
      (∀ i, π i*u i-π (σ i)*v i=J) ∧
      (∑ i, π i*h i)=0 ∧ (∑ i, π i*k i)=0 ∧
      (∀ i, generator σ u v h i+drift σ u v d i=J) ∧
      (∀ i, generator σ u v k i+2*tiltFirst σ u v d h i+
        tiltSecondOne σ u v d i=C2+2*J*h i) ∧
      C2=edgeQuadratic σ u v d π h := by
  obtain ⟨π,J,h,hπ,hnorm,hJ,hflux,hcenter,hcor⟩ :=
    exists_stationary_corrector σ hc u v d hu hv hUV hd
  have hfirst : ∀ i, generator σ u v h i+drift σ u v d i=J := by
    intro i
    have hh := hcor i
    dsimp [generator, drift]
    nlinarith only [hh]
  let C2 := secondCoefficient σ u v d π h
  let f : ι → ℝ := fun i => C2+2*J*h i-
    (tiltSecondOne σ u v d i+2*tiltFirst σ u v d h i)
  have hf : (∑ i, π i*f i)=0 := by
    have hs : (∑ i, π i*f i) =
        C2*(∑ i, π i)+2*J*(∑ i, π i*h i)-
          secondCoefficient σ u v d π h := by
      dsimp only [f, secondCoefficient]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hs, hnorm, hcenter]
    dsimp [C2]
    ring
  obtain ⟨k,hkcenter,hk⟩ := exists_centered_poisson σ hc u v π f J
    hu hv hUV hnorm (ne_of_gt hJ) hflux hf
  refine ⟨π,h,k,J,C2,hπ,hnorm,hJ,hflux,hcenter,hkcenter,hfirst,?_,?_⟩
  · intro i
    have hh := hk i
    dsimp only [f] at hh
    linarith only [hh]
  · exact secondCoefficient_eq_edgeQuadratic σ u v d π h J hflux hcenter hfirst

omit [Fintype ι] [DecidableEq ι] in
theorem stationary_flow_affinity [Fintype ι] [DecidableEq ι] (σ : Perm ι) (u v π : ι → ℝ)
    (hu : ∀ i, 0<u i) (hv : ∀ i, 0<v i) (hπ : ∀ i, 0<π i) :
    (∑ i, Real.log ((π i*u i)/(π (σ i)*v i))) =
      Real.log ((∏ i, u i)/(∏ i, v i)) := by
  have hterm (i : ι) :
      Real.log ((π i*u i)/(π (σ i)*v i)) =
        Real.log (u i/v i)+Real.log (π i)-Real.log (π (σ i)) := by
    rw [Real.log_div (mul_ne_zero (ne_of_gt (hπ i)) (ne_of_gt (hu i)))
      (mul_ne_zero (ne_of_gt (hπ _)) (ne_of_gt (hv i))),
      Real.log_mul (ne_of_gt (hπ i)) (ne_of_gt (hu i)),
      Real.log_mul (ne_of_gt (hπ _)) (ne_of_gt (hv i)),
      Real.log_div (ne_of_gt (hu i)) (ne_of_gt (hv i))]
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Equiv.sum_comp σ (fun i => Real.log (π i))]
  have hup : (∏ i, u i)≠0 := ne_of_gt (Finset.prod_pos (fun i hi => hu i))
  have hvp : (∏ i, v i)≠0 := ne_of_gt (Finset.prod_pos (fun i hi => hv i))
  rw [Real.log_div hup hvp,
    Real.log_prod Finset.univ u (fun i hi => ne_of_gt (hu i)),
    Real.log_prod Finset.univ v (fun i hi => ne_of_gt (hv i))]
  simp_rw [Real.log_div (ne_of_gt (hu _)) (ne_of_gt (hv _))]
  rw [Finset.sum_sub_distrib]
  ring

/-- The finite-flow TUR expressed using the actual rate-product affinity and
the corrected quadratic form. No uncertainty bound is a hypothesis. -/
theorem edgeQuadratic_tur (σ : Perm ι) (u v d π h : ι → ℝ) (J : ℝ)
    (hu : ∀ i, 0<u i) (hv : ∀ i, 0<v i) (hπ : ∀ i, 0<π i)
    (hJ : 0<J) (hflux : ∀ i, π i*u i-π (σ i)*v i=J)
    (hd : (∑ i, d i)=1) :
    2/Real.log ((∏ i, u i)/(∏ i, v i)) ≤ edgeQuadratic σ u v d π h/J := by
  have hg : (∑ i, (d i+h (σ i)-h i))=1 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Equiv.sum_comp σ h, hd]
    ring
  have hh := UnicyclicFiniteTUR.finite_flow_tur
    (fun i => π i*u i) (fun i => π (σ i)*v i) (fun i => d i+h (σ i)-h i) J
    (fun i => mul_pos (hπ i) (hu i)) (fun i => mul_pos (hπ _) (hv i))
    hJ hflux hg
  rw [stationary_flow_affinity σ u v π hu hv hπ] at hh
  exact hh

end
end UnicyclicPoisson

#print axioms UnicyclicPoisson.exists_centered_poisson
#print axioms UnicyclicPoisson.exists_two_coefficients
#print axioms UnicyclicPoisson.edgeQuadratic_tur
