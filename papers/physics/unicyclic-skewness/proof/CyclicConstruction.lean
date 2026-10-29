import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
Constructive finite cyclic recurrences.  These are actual constructions from
positive rates and a single-cycle permutation, not definitions that assume the
stationary or corrector conclusions.  This file is under active checking.
-/
namespace UnicyclicConstruction
noncomputable section
open scoped BigOperators
open Equiv
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 2000000

def transferTerm (σ : Perm ι) (ρ f : ι → ℝ) (k : ℕ) (i : ι) : ℝ :=
  (∏ j ∈ Finset.range k, ρ ((σ^j) i)) * f ((σ^k) i)

def green (σ : Perm ι) (ρ f : ι → ℝ) (n : ℕ) (i : ι) : ℝ :=
  ∑ k ∈ Finset.range n, transferTerm σ ρ f k i

omit [Fintype ι] [DecidableEq ι] in
theorem transfer_step [Fintype ι] [DecidableEq ι] (σ : Perm ι) (ρ f : ι → ℝ) (k : ℕ) (i : ι) :
    ρ i * transferTerm σ ρ f k (σ i) = transferTerm σ ρ f (k+1) i := by
  have hshift (j : ℕ) : (σ^j) (σ i) = (σ^(j+1)) i := by
    rw [pow_succ, Perm.mul_apply]
  simp only [transferTerm, Finset.prod_range_succ', pow_zero, Perm.one_apply]
  simp_rw [hshift]
  ring

theorem green_recurrence_raw (σ : Perm ι) (ρ f : ι → ℝ) (n : ℕ) (i : ι) :
    green σ ρ f n i - ρ i * green σ ρ f n (σ i) =
      f i-transferTerm σ ρ f n i := by
  have hm : ρ i * green σ ρ f n (σ i) =
      ∑ k ∈ Finset.range n, transferTerm σ ρ f (k+1) i := by
    rw [green, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact transfer_step σ ρ f k i
  have hs := Finset.sum_range_succ (fun k => transferTerm σ ρ f k i) n
  have hs' := Finset.sum_range_succ' (fun k => transferTerm σ ρ f k i) n
  have hzero : transferTerm σ ρ f 0 i = f i := by simp [transferTerm]
  dsimp only [green]
  dsimp only [green] at hm
  linarith only [hm, hs, hs', hzero]

omit [Fintype ι] [DecidableEq ι] in
theorem orbit_product [Fintype ι] [DecidableEq ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (ρ : ι → ℝ) (i : ι) :
    (∏ k ∈ Finset.range (Fintype.card ι), ρ ((σ^k) i)) = ∏ j, ρ j := by
  apply Finset.prod_bij (fun k hk => (σ^k) i)
  · intro k hk
    exact Finset.mem_univ _
  · intro k hk l hl hkl
    have he := (hc.pow_apply_eq_pow_apply (Finset.mem_univ i)).mp hkl
    have hk' := Finset.mem_range.mp hk
    have hl' := Finset.mem_range.mp hl
    simpa only [Finset.card_univ, Nat.ModEq, Nat.mod_eq_of_lt hk', Nat.mod_eq_of_lt hl'] using he
  · intro j hj
    obtain ⟨k, hk, he⟩ := hc.exists_pow_eq (Finset.mem_univ i) (Finset.mem_univ j)
    exact ⟨k, Finset.mem_range.mpr (by simpa using hk), he⟩
  · intro k hk
    rfl

omit [Fintype ι] [DecidableEq ι] in
theorem orbit_sum [Fintype ι] [DecidableEq ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (f : ι → ℝ) (i : ι) :
    (∑ k ∈ Finset.range (Fintype.card ι), f ((σ^k) i)) = ∑ j, f j := by
  apply Finset.sum_bij (fun k hk => (σ^k) i)
  · intro k hk
    exact Finset.mem_univ _
  · intro k hk l hl hkl
    have he := (hc.pow_apply_eq_pow_apply (Finset.mem_univ i)).mp hkl
    have hk' := Finset.mem_range.mp hk
    have hl' := Finset.mem_range.mp hl
    simpa only [Finset.card_univ, Nat.ModEq, Nat.mod_eq_of_lt hk', Nat.mod_eq_of_lt hl'] using he
  · intro j hj
    obtain ⟨k, hk, he⟩ := hc.exists_pow_eq (Finset.mem_univ i) (Finset.mem_univ j)
    exact ⟨k, Finset.mem_range.mpr (by simpa using hk), he⟩
  · intro k hk
    rfl

theorem green_recurrence (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (ρ f : ι → ℝ) (i : ι) :
    green σ ρ f (Fintype.card ι) i -
      ρ i * green σ ρ f (Fintype.card ι) (σ i) =
      (1-∏ j, ρ j)*f i := by
  rw [green_recurrence_raw]
  have hp : (σ^(Fintype.card ι)) i = i := by
    simpa using hc.pow_card_apply (Finset.mem_univ i)
  rw [transferTerm, orbit_product σ hc ρ i, hp]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem green_positive [Fintype ι] [DecidableEq ι] (σ : Perm ι) (ρ f : ι → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hf : ∀ i, 0 < f i) (i : ι) :
    0 < green σ ρ f (Fintype.card ι) i := by
  apply Finset.sum_pos
  · intro k hk
    exact mul_pos (Finset.prod_pos (fun j hj => hρ _)) (hf _)
  · exact ⟨0, Finset.mem_range.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)⟩

theorem exists_positive_cyclic_solution (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (ρ f : ι → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hf : ∀ i, 0 < f i)
    (hprod : (∏ i, ρ i) < 1) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ ∀ i, x i-ρ i*x (σ i)=f i := by
  let Z : ℝ := 1-∏ i, ρ i
  have hZ : 0 < Z := sub_pos.mpr hprod
  refine ⟨fun i => green σ ρ f (Fintype.card ι) i/Z, ?_, ?_⟩
  · intro i
    exact div_pos (green_positive σ ρ f hρ hf i) hZ
  · intro i
    have hh := green_recurrence σ hc ρ f i
    change green σ ρ f (Fintype.card ι) i/Z -
      ρ i*(green σ ρ f (Fintype.card ι) (σ i)/Z) = f i
    calc
      _ = (green σ ρ f (Fintype.card ι) i-
            ρ i*green σ ρ f (Fintype.card ι) (σ i))/Z := by ring
      _ = f i := by
        rw [hh]
        change Z*f i/Z=f i
        field_simp [ne_of_gt hZ]

/-- A normalized positive stationary flow is constructed from the rates. -/
theorem exists_stationary_cycle [Nonempty ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (u v : ι → ℝ)
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hUV : (∏ i, v i) < ∏ i, u i) :
    ∃ (π : ι → ℝ) (J : ℝ), (∀ i, 0 < π i) ∧
      (∑ i, π i)=1 ∧ 0<J ∧ ∀ i, π i*u i-π (σ i)*v i=J := by
  have hup : 0 < ∏ i, u i := Finset.prod_pos (fun i hi => hu i)
  have hp : (∏ i, v i/u i) < 1 := by
    rw [Finset.prod_div_distrib]
    exact (div_lt_one hup).mpr hUV
  obtain ⟨x, hx, he⟩ := exists_positive_cyclic_solution σ hc
    (fun i => v i/u i) (fun i => 1/u i)
    (fun i => div_pos (hv i) (hu i)) (fun i => one_div_pos.mpr (hu i)) hp
  let Z := ∑ i, x i
  have hZ : 0 < Z := Finset.sum_pos (fun i hi => hx i) Finset.univ_nonempty
  have he' : ∀ i, u i*x i-v i*x (σ i)=1 := by
    intro i
    have hh := congrArg (fun z : ℝ => u i*z) (he i)
    field_simp [ne_of_gt (hu i)] at hh
    nlinarith only [hh]
  refine ⟨fun i => x i/Z, 1/Z, ?_, ?_, one_div_pos.mpr hZ, ?_⟩
  · intro i
    exact div_pos (hx i) hZ
  · simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ (ne_of_gt hZ)
  · intro i
    calc
      _ = (u i*x i-v i*x (σ i))/Z := by ring
      _ = 1/Z := by rw [he' i]

theorem exists_positive_gradient (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (u v : ι → ℝ)
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hUV : (∏ i, v i) < ∏ i, u i) (J : ℝ) (hJ : 0<J) :
    ∃ g : ι → ℝ, (∀ i, 0<g i) ∧
      ∀ i, u i*g i-v (σ⁻¹ i)*g (σ⁻¹ i)=J := by
  have hup : 0 < ∏ i, u i := Finset.prod_pos (fun i hi => hu i)
  have hp : (∏ i, v (σ⁻¹ i)/u i) < 1 := by
    rw [Finset.prod_div_distrib, Equiv.prod_comp σ⁻¹ v]
    exact (div_lt_one hup).mpr hUV
  obtain ⟨g, hg, he⟩ := exists_positive_cyclic_solution σ⁻¹ hc.inv
    (fun i => v (σ⁻¹ i)/u i) (fun i => J/u i)
    (fun i => div_pos (hv _) (hu i)) (fun i => div_pos hJ (hu i)) hp
  refine ⟨g, hg, ?_⟩
  intro i
  have hh := congrArg (fun z : ℝ => u i*z) (he i)
  field_simp [ne_of_gt (hu i)] at hh
  simp only [one_div] at hh
  nlinarith only [hh]

omit [Fintype ι] [DecidableEq ι] in
theorem gradient_sum_one [Fintype ι] [DecidableEq ι] (σ : Perm ι) (u v π g : ι → ℝ) (J : ℝ)
    (hJ : J ≠ 0) (hnorm : (∑ i, π i)=1)
    (hflux : ∀ i, π i*u i-π (σ i)*v i=J)
    (hrec : ∀ i, u i*g i-v (σ⁻¹ i)*g (σ⁻¹ i)=J) :
    (∑ i, g i)=1 := by
  have hleft : (∑ i, π i*(u i*g i-v (σ⁻¹ i)*g (σ⁻¹ i)))=J := by
    simp_rw [hrec]
    rw [← Finset.sum_mul, hnorm, one_mul]
  have hreindex :
      (∑ i, π i*(v (σ⁻¹ i)*g (σ⁻¹ i))) =
        ∑ i, π (σ i)*(v i*g i) := by
    simpa only [Perm.inv_apply_self] using
      (Equiv.sum_comp σ (fun i => π i*(v (σ⁻¹ i)*g (σ⁻¹ i)))).symm
  have hright : (∑ i, π i*(u i*g i-v (σ⁻¹ i)*g (σ⁻¹ i))) =
      J*(∑ i, g i) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hreindex, ← Finset.sum_sub_distrib]
    calc
      _ = ∑ i, (π i*u i-π (σ i)*v i)*g i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, J*g i := by simp_rw [hflux]
      _ = _ := (Finset.mul_sum _ _ _).symm
  apply mul_left_cancel₀ hJ
  simpa using hright.symm.trans hleft

/-- Explicitly integrate every zero-sum edge function around a finite cycle. -/
theorem exists_cyclic_coboundary [Nonempty ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (r : ι → ℝ)
    (hr : (∑ i, r i)=0) :
    ∃ h : ι → ℝ, ∀ i, h (σ i)-h i=r i := by
  let N : ℕ := Fintype.card ι
  let H : ι → ℝ := fun i => ∑ k ∈ Finset.range N, green σ (fun _ => 1) r k i
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card ι))
  have hstep (k : ℕ) (i : ι) :
      green σ (fun _ => 1) r k (σ i)-green σ (fun _ => 1) r k i =
        r ((σ^k) i)-r i := by
    have hh := green_recurrence_raw σ (fun _ => 1) r k i
    simp only [transferTerm, Finset.prod_const_one, one_mul] at hh
    linarith only [hh]
  have hdiff (i : ι) : H (σ i)-H i = -(N : ℝ)*r i := by
    dsimp only [H]
    rw [← Finset.sum_sub_distrib]
    simp_rw [hstep]
    rw [Finset.sum_sub_distrib, orbit_sum σ hc r i, hr]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, zero_sub, neg_mul]
  refine ⟨fun i => -H i/(N : ℝ), ?_⟩
  intro i
  calc
    _ = -(H (σ i)-H i)/(N : ℝ) := by ring
    _ = r i := by rw [hdiff i]; field_simp [hN]

/-- Positive rates on a genuine finite cycle supply a centered Poisson
corrector for every winding increment of total one. -/
theorem exists_stationary_corrector [Nonempty ι] (σ : Perm ι)
    (hc : σ.IsCycleOn (Finset.univ : Finset ι)) (u v d : ι → ℝ)
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hUV : (∏ i, v i) < ∏ i, u i) (hd : (∑ i, d i)=1) :
    ∃ (π : ι → ℝ) (J : ℝ) (h : ι → ℝ),
      (∀ i, 0<π i) ∧ (∑ i, π i)=1 ∧ 0<J ∧
      (∀ i, π i*u i-π (σ i)*v i=J) ∧ (∑ i, π i*h i)=0 ∧
      ∀ i, u i*(d i+h (σ i)-h i)-
        v (σ⁻¹ i)*(d (σ⁻¹ i)+h i-h (σ⁻¹ i))=J := by
  obtain ⟨π,J,hπ,hnorm,hJ,hflux⟩ := exists_stationary_cycle σ hc u v hu hv hUV
  obtain ⟨g,hg,hrec⟩ := exists_positive_gradient σ hc u v hu hv hUV J hJ
  have hgsum := gradient_sum_one σ u v π g J (ne_of_gt hJ) hnorm hflux hrec
  have hrsum : (∑ i, (g i-d i))=0 := by
    rw [Finset.sum_sub_distrib, hgsum, hd]
    ring
  obtain ⟨h,hdiff⟩ := exists_cyclic_coboundary σ hc (fun i => g i-d i) hrsum
  let μ : ℝ := ∑ i, π i*h i
  refine ⟨π,J,(fun i => h i-μ),hπ,hnorm,hJ,hflux,?_,?_⟩
  · simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hnorm]
    dsimp [μ]
    ring
  · intro i
    have hf : d i+(h (σ i)-μ)-(h i-μ)=g i := by
      have hh := hdiff i
      linarith only [hh]
    have hb : d (σ⁻¹ i)+(h i-μ)-(h (σ⁻¹ i)-μ)=g (σ⁻¹ i) := by
      have hh := hdiff (σ⁻¹ i)
      simp only [Perm.apply_inv_self] at hh
      linarith only [hh]
    rw [hf,hb]
    exact hrec i

end
end UnicyclicConstruction

#print axioms UnicyclicConstruction.exists_stationary_cycle
#print axioms UnicyclicConstruction.exists_stationary_corrector
