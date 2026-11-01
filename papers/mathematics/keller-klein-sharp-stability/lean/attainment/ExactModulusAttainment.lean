import ExactSaturatedModulus

/-!
Actual finite-vector attainment of the complete local saturated modulus.
Every odd core size and every feasible residual/deficit pair are included.
The support gap, normalization, cap, core size, and coefficient distance
are proved for the explicit two-residual family, not assumed.
-/

noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.ExactModulusAttainment
open Breakthrough.ExactSupportGap Breakthrough.GapCore Breakthrough.GapFibers
open Breakthrough.SharpTail Breakthrough.ExactSaturatedModulus

set_option maxHeartbeats 5000000

def twoResidualCoefficients (n : ℕ) (a u v : ℝ) : Fin (n+1+1) → ℝ :=
  Fin.cons u (Fin.cons v (fun _ : Fin n => a))

lemma twoResidual_sum {n : ℕ} (a u v : ℝ) (ω : BoolCube (n+1+1)) :
    rademacherSum (twoResidualCoefficients n a u v) ω =
      u*rademacherSign (ω 0)+v*rademacherSign (ω (Fin.succ 0))+
        rademacherSum (fun _ : Fin n => a) (fun i => ω i.succ.succ) := by
  simp [rademacherSum, twoResidualCoefficients, Fin.sum_univ_succ]
  ring

lemma twoResidual_variance (n : ℕ) (a u v : ℝ) :
    (∑ i, twoResidualCoefficients n a u v i ^ 2) =
      (n:ℝ)*a^2+u^2+v^2 := by
  simp [twoResidualCoefficients, Fin.sum_univ_succ]
  ring

lemma twoResidual_gap {n : ℕ} (hn : Odd n) {a u v : ℝ}
    (ha : 0 < a) (hu : 0 ≤ u) (hv : 0 ≤ v) (hsmall : u+v ≤ a) :
    supportGap (twoResidualCoefficients n a u v) = a-u-v := by
  apply supportGap_eq_of_gap_and_outcome
  · intro ω
    rw [twoResidual_sum]
    let S := rademacherSum (fun _ : Fin n => a) (fun i => ω i.succ.succ)
    have hflat : a ≤ |S| := flat_gap_lower hn ha _
    have hresu : |u*rademacherSign (ω 0)|=u := by
      cases hω : ω 0 <;> simp [rademacherSign, hω, abs_of_nonneg hu]
    have hresv : |v*rademacherSign (ω (Fin.succ 0))|=v := by
      cases hω : ω (Fin.succ 0) <;> simp [rademacherSign, hω, abs_of_nonneg hv]
    have hres := abs_add (u*rademacherSign (ω 0))
      (v*rademacherSign (ω (Fin.succ 0)))
    rw [hresu, hresv] at hres
    have ht := abs_sub
      (u*rademacherSign (ω 0)+v*rademacherSign (ω (Fin.succ 0))+S)
      (u*rademacherSign (ω 0)+v*rademacherSign (ω (Fin.succ 0)))
    have hid : u*rademacherSign (ω 0)+v*rademacherSign (ω (Fin.succ 0))+S-
      (u*rademacherSign (ω 0)+v*rademacherSign (ω (Fin.succ 0)))=S := by ring
    rw [hid] at ht
    linarith only [hflat,hres,ht]
  · obtain ⟨η,hη⟩ := flat_gap_outcome hn ha
    rcases le_total 0 (rademacherSum (fun _ : Fin n => a) η) with hp | hm
    · rw [abs_of_nonneg hp] at hη
      refine ⟨Fin.cons false (Fin.cons false η), ?_⟩
      rw [twoResidual_sum]
      simp only [Fin.cons_zero, Fin.cons_succ, rademacherSign,
        Bool.false_eq_true, if_false, mul_neg_one]
      rw [hη, abs_of_nonneg (by linarith : 0 ≤ -u+-v+a)]
      ring
    · rw [abs_of_nonpos hm] at hη
      refine ⟨Fin.cons true (Fin.cons true η), ?_⟩
      rw [twoResidual_sum]
      simp only [Fin.cons_zero, Fin.cons_succ, rademacherSign, if_true, mul_one]
      rw [abs_of_nonpos (by linarith :
        u+v+rademacherSum (fun _ : Fin n => a) η ≤ 0)]
      linarith

lemma twoResidual_core_card {n : ℕ} {a u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hhigh : 2*(u+v)<a) :
    (gapCore (twoResidualCoefficients n a u v) (a-u-v)).card=n := by
  classical
  have hu' : u<a-u-v := by linarith
  have hv' : v<a-u-v := by linarith
  have ha' : a-u-v≤a := by linarith
  rw [gapCore, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [twoResidualCoefficients, Fin.cons_zero, Fin.cons_succ,
    if_neg (not_le.mpr hu'), if_neg (not_le.mpr hv'), if_pos ha']
  simp

lemma split_root_data {r e : ℝ} (hr : 0 < r) (he : 0 ≤ e)
    (hlocal : e ≤ (Real.sqrt 2-1)*r) :
    let d := Real.sqrt (r^2-2*r*e-e^2)
    let u := (r+e+d)/2
    let v := (r+e-d)/2
    0≤v ∧ v≤u ∧ u≤r+e ∧ u+v=r+e ∧ u^2+v^2=r^2 ∧
      Real.sqrt ((u-r)^2+v^2)=gapModulus r e := by
  dsimp only
  have hF := gapModulus_square hr he hlocal
  have hd0 := Real.sqrt_nonneg (r^2-2*r*e-e^2)
  have hd2 := Real.sq_sqrt hF.1
  have hre := mul_nonneg hr.le he
  have hd : Real.sqrt (r^2-2*r*e-e^2)≤r+e := by
    nlinarith only [hd2,hd0,hr,he,hre]
  refine ⟨by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
  · nlinarith only [hd2]
  · unfold gapModulus
    congr 1
    nlinarith only [hd2]

/-- The complete two-residual equality family is realized by actual finite
signed sums for every odd core size. No support-gap hypothesis is supplied. -/
theorem actual_exact_modulus_family {n : ℕ} (hn : Odd n) {a r e : ℝ}
    (ha : 0<a) (hr : 0<r) (he : 0≤e)
    (hlocal : e≤(Real.sqrt 2-1)*r)
    (hvar : (n:ℝ)*a^2+r^2=1) (hhigh : a/2<a-r-e) :
    let d := Real.sqrt (r^2-2*r*e-e^2)
    let u := (r+e+d)/2
    let v := (r+e-d)/2
    let b := twoResidualCoefficients n a u v
    let w := twoResidualCoefficients n a r 0
    (∑ i, b i^2)=1 ∧ (∀ i, 0≤b i ∧ b i≤a) ∧
      supportGap b=a-r-e ∧
      (gapCore b (supportGap b)).card=n ∧
      (∑ i, w i^2)=1 ∧ (∀ i, 0≤w i ∧ w i≤a) ∧
      supportGap w=a-r ∧
      supportGap w-supportGap b=e ∧
      Real.sqrt (∑ i, (b i-w i)^2)=gapModulus r e := by
  classical
  let d := Real.sqrt (r^2-2*r*e-e^2)
  let u := (r+e+d)/2
  let v := (r+e-d)/2
  change (∑ i, twoResidualCoefficients n a u v i^2)=1 ∧
    (∀ i, 0≤twoResidualCoefficients n a u v i ∧ twoResidualCoefficients n a u v i≤a) ∧
    supportGap (twoResidualCoefficients n a u v)=a-r-e ∧
    (gapCore (twoResidualCoefficients n a u v)
      (supportGap (twoResidualCoefficients n a u v))).card=n ∧
    (∑ i, twoResidualCoefficients n a r 0 i^2)=1 ∧
    (∀ i, 0≤twoResidualCoefficients n a r 0 i ∧ twoResidualCoefficients n a r 0 i≤a) ∧
    supportGap (twoResidualCoefficients n a r 0)=a-r ∧
    supportGap (twoResidualCoefficients n a r 0)-
      supportGap (twoResidualCoefficients n a u v)=e ∧
    Real.sqrt (∑ i, (twoResidualCoefficients n a u v i-
      twoResidualCoefficients n a r 0 i)^2)=gapModulus r e
  have hd := split_root_data hr he hlocal
  change 0≤v ∧ v≤u ∧ u≤r+e ∧ u+v=r+e ∧ u^2+v^2=r^2 ∧
    Real.sqrt ((u-r)^2+v^2)=gapModulus r e at hd
  have hu : 0≤u := hd.1.trans hd.2.1
  have hv := hd.1
  have hsum := hd.2.2.2.1
  have hva := hd.2.2.2.2.1
  have hdist := hd.2.2.2.2.2
  have huva : u+v≤a := by linarith
  have hsmall : 2*(u+v)<a := by linarith
  have hra : r≤a := by linarith
  have hgap : supportGap (twoResidualCoefficients n a u v)=a-r-e := by
    rw [twoResidual_gap hn ha hu hv huva]
    linarith only [hsum]
  have hwgap : supportGap (twoResidualCoefficients n a r 0)=a-r := by
    simpa using twoResidual_gap hn ha hr.le (le_refl (0:ℝ)) (by simpa using hra)
  refine ⟨?_, ?_, hgap, ?_, ?_, ?_, hwgap, ?_, ?_⟩
  · rw [twoResidual_variance]
    nlinarith only [hvar,hva]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0≤u ∧ u≤a
      exact ⟨hu, by linarith⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · change 0≤v ∧ v≤a
        exact ⟨hv, by linarith⟩
      · exact ⟨ha.le, le_rfl⟩
  · rw [hgap]
    have hx : a-r-e=a-u-v := by linarith only [hsum]
    rw [hx]
    exact twoResidual_core_card hu hv hsmall
  · rw [twoResidual_variance]
    nlinarith only [hvar]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨hr.le,hra⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨le_rfl,ha.le⟩
      · exact ⟨ha.le,le_rfl⟩
  · rw [hwgap,hgap]
    ring
  · simpa [twoResidualCoefficients, Fin.sum_univ_succ] using hdist

#print axioms twoResidual_gap
#print axioms actual_exact_modulus_family

end Breakthrough.ExactModulusAttainment
