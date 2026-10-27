module

public import IntervalEvaluation
public import CertificateCoverage
public import ProfileCoverage
public import ProfileReduction

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.Gyires.RankTwo.Certificate

open Bernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem profile_deficit_nonpos_of_all_checks (hn : 2 ≤ Fintype.card ι)
    (hcheck : allProfileChecks (Fintype.card ι) = true) (t : ℝ)
    (ht : 0 < t ∧ t < Fintype.card ι) (p q : ι → ℝ)
    (hp : p ∈ parameters t) (hq : q ∈ parameters t)
    (heqp : EqualInterior p) (heqq : EqualInterior q) :
    lawDeficit (Fintype.card ι) (t/Fintype.card ι)
      (t*((Fintype.card ι : ℝ)-t)/(Fintype.card ι : ℝ)^2) (law p) (law q) ≤ 0 := by
  let n := Fintype.card ι
  have hnpos : 0 < n := by dsimp [n]; omega
  have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  obtain ⟨a, m, hm, ham, hpt, hpg, _hpm⟩ := exists_centered_profile hp ht heqp
  obtain ⟨c, l, hl, hcl, hqt, hqg, hqm⟩ := exists_centered_profile hq ht heqq
  obtain ⟨hLR, hLt, htR⟩ := profile_intervals_overlap a m c l t hm hl hpt hqt
  let L := max a c
  let R := min (a+m) (c+l)
  let U := (R : ℝ)-t
  let V := t-L
  let f := intervalEvaluation U V
  have hU : 0 ≤ U := sub_nonneg.mpr htR
  have hV : 0 ≤ V := sub_nonneg.mpr hLt
  have hLR' : (L : ℝ) < R := by exact_mod_cast hLR
  have hs : f 2+f 3 ≠ 0 := by
    change intervalEvaluation U V 2+intervalEvaluation U V 3 ≠ 0
    rw [intervalEvaluation_two, intervalEvaluation_three]
    dsimp [U, V]
    linarith
  have hratio : ((L : ℝ)*f 2+R*f 3)/(f 2+f 3) = t := by
    change ((L : ℝ)*intervalEvaluation U V 2+R*intervalEvaluation U V 3)/
      (intervalEvaluation U V 2+intervalEvaluation U V 3) = t
    rw [intervalEvaluation_two, intervalEvaluation_three]
    exact interval_mean L R t hLR'
  have hD := interval_D_pos n L R t ht hLR
  change 0 < SparsePolynomial.eval f (Dpoly n L R) at hD
  have hmeanq : ∑ i, (q i-t/n) = 0 := by
    have hmean : ∑ i, q i = (n : ℝ)*(t/n) := by
      rw [hq.2]
      field_simp [ne_of_gt hn']
    exact sum_centerVector q (t/n) hmean
  have hvariance := eval_Kpoly_actual f n c l L R q rfl hn0 (Nat.ne_of_gt hl) hs
    (ne_of_gt hD) (by rw [hratio]; exact hq.2) (by rw [hratio]; exact hqm)
  rw [hratio] at hvariance
  have hbound := profile_contraction_of_check f (intervalEvaluation_nonneg U V hU hV)
    n a m c l L R (fun i => p i-t/n) (fun i => q i-t/n) rfl hnpos hm hl hs hD hmeanq
    (by rw [hratio]; exact hpg) (by rw [hratio]; exact hqg) hvariance
    (profile_check_of_all n a m c l hm ham hl hcl hLR hcheck)
  have hσ : SparsePolynomial.eval f (Dpoly n L R)/((n : ℝ)^2*(f 2+f 3)^2) =
      t*((n : ℝ)-t)/(n : ℝ)^2 := by
    have h := interval_scale_identity (n : ℝ) L R (f 2) (f 3) (ne_of_gt hn') hs
    rw [hratio] at h
    rw [eval_Dpoly]
    exact h.symm
  dsimp only at hbound
  rw [hσ] at hbound
  have hσpos : 0 < t*((n : ℝ)-t)/(n : ℝ)^2 :=
    div_pos (mul_pos ht.1 (sub_pos.mpr ht.2)) (pow_pos hn' 2)
  have hc : 0 < (n.factorial : ℝ)/(n : ℝ)^n :=
    div_pos (by exact_mod_cast Nat.factorial_pos n) (pow_pos hn' n)
  rw [lawDeficit_eq_actual hn _ _ (ne_of_gt hσpos) p q hmeanq]
  exact sub_nonpos.mpr ((div_le_div_iff_of_pos_right hc).mpr hbound)

theorem all_parameters_deficit_nonpos_of_all_checks (hn : 2 ≤ Fintype.card ι)
    (hcheck : allProfileChecks (Fintype.card ι) = true) (t : ℝ)
    (ht : 0 < t ∧ t < Fintype.card ι) (p q : ι → ℝ)
    (hp : p ∈ parameters t) (hq : q ∈ parameters t) :
    lawDeficit (Fintype.card ι) (t/Fintype.card ι)
      (t*((Fintype.card ι : ℝ)-t)/(Fintype.card ι : ℝ)^2) (law p) (law q) ≤ 0 := by
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (show 0 < Fintype.card ι by omega)
  have hmean : t = (Fintype.card ι : ℝ)*(t/Fintype.card ι) := by
    field_simp [ne_of_gt hn']
  apply lawDeficit_nonpos_of_profiles hn t (t/Fintype.card ι)
    (t*((Fintype.card ι : ℝ)-t)/(Fintype.card ι : ℝ)^2) hmean
    (div_nonneg (mul_nonneg ht.1.le (sub_pos.mpr ht.2).le) (sq_nonneg _))
    (fun x hx y hy heqx heqy => profile_deficit_nonpos_of_all_checks hn hcheck t ht x y hx hy heqx heqy)
    p q hp hq

end MathAndTheory.Gyires.RankTwo.Certificate
