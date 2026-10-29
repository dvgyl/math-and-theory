import BookInnerCalculus

noncomputable section
namespace BookCompletion
open Set

def innerH (n : ℕ) (t : ℝ) : ℝ := 2/(2-t)^n
def innerHprime (n : ℕ) (t : ℝ) : ℝ := innerH n t*(n:ℝ)/(2-t)
def innerHsecond (n : ℕ) (t : ℝ) : ℝ := innerH n t*(n:ℝ)*((n:ℝ)+1)/(2-t)^2
def innerF (n : ℕ) (t : ℝ) : ℝ := innerQ n t+1-2*t-innerH n t
def innerG (n : ℕ) (t : ℝ) : ℝ := innerQ n t+innerH n t+2*t-1
def innerFprime (n : ℕ) (t : ℝ) : ℝ := innerQprime n t-2-innerHprime n t
def innerGprime (n : ℕ) (t : ℝ) : ℝ := innerQprime n t+innerHprime n t+2
def innerGsecond (n : ℕ) (t : ℝ) : ℝ := innerQsecond n t+innerHsecond n t

theorem innerH_eq_inv_pow (n : ℕ) (t : ℝ) : innerH n t = 2*((2-t)⁻¹)^n := by
  simp [innerH,div_eq_mul_inv,inv_pow]

theorem continuousAt_innerQ (n : ℕ) {t : ℝ} (ht0 : t ≠ 0) (ht2 : 2-t ≠ 0) :
    ContinuousAt (innerQ n) t := by
  have ha : ContinuousAt innerA t :=
    ((continuousAt_const.sub continuousAt_id).pow 2).div
      (continuousAt_id.mul (continuousAt_const.sub continuousAt_id)) (mul_ne_zero ht0 ht2)
  exact (continuousAt_id.pow 2).mul (ha.pow n)

theorem continuousAt_innerH (n : ℕ) {t : ℝ} (ht2 : 2-t ≠ 0) :
    ContinuousAt (innerH n) t :=
  continuousAt_const.div ((continuousAt_const.sub continuousAt_id).pow n) (pow_ne_zero n ht2)

theorem continuousAt_innerF (n : ℕ) {t : ℝ} (ht0 : t ≠ 0) (ht2 : 2-t ≠ 0) :
    ContinuousAt (innerF n) t :=
  ((((continuousAt_innerQ n ht0 ht2).add continuousAt_const).sub
    (continuousAt_const.mul continuousAt_id)).sub (continuousAt_innerH n ht2))

theorem continuousAt_innerG (n : ℕ) {t : ℝ} (ht0 : t ≠ 0) (ht2 : 2-t ≠ 0) :
    ContinuousAt (innerG n) t :=
  ((((continuousAt_innerQ n ht0 ht2).add (continuousAt_innerH n ht2)).add
    (continuousAt_const.mul continuousAt_id)).sub continuousAt_const)

theorem hasDerivAt_innerH {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    HasDerivAt (innerH n) (innerHprime n t) t := by
  have ht2 : 2-t ≠ 0 := (inner_domain ht).2.1.ne'
  have hpow : (2-t)^n = (2-t)^(n-1)*(2-t) := by rw [← pow_succ,Nat.sub_add_cancel hn]
  have h := (hasDerivAt_const t (2:ℝ)).div (((hasDerivAt_id t).const_sub 2).pow n)
    (pow_ne_zero n ht2)
  convert h using 1
  dsimp [innerHprime,innerH]
  simp only [hpow,id_eq]
  field_simp [ht2,pow_ne_zero (n-1) ht2]
  ring

theorem hasDerivAt_innerHprime {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    HasDerivAt (innerHprime n) (innerHsecond n t) t := by
  have ht2 : 2-t ≠ 0 := (inner_domain ht).2.1.ne'
  have h := ((hasDerivAt_innerH hn ht).mul_const (n:ℝ)).div
    ((hasDerivAt_id t).const_sub 2) ht2
  convert h using 1
  dsimp [innerHsecond,innerHprime]
  field_simp [ht2]
  ring

theorem hasDerivAt_innerF {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    HasDerivAt (innerF n) (innerFprime n t) t := by
  convert (((hasDerivAt_innerQ hn ht).add_const 1).sub
    ((hasDerivAt_id t).const_mul 2)).sub (hasDerivAt_innerH hn ht) using 1
  dsimp [innerFprime]
  ring

theorem hasDerivAt_innerG {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    HasDerivAt (innerG n) (innerGprime n t) t := by
  convert (((hasDerivAt_innerQ hn ht).add (hasDerivAt_innerH hn ht)).add
    ((hasDerivAt_id t).const_mul 2)).sub_const 1 using 1
  dsimp [innerGprime]
  ring

theorem hasDerivAt_innerGprime {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    HasDerivAt (innerGprime n) (innerGsecond n t) t := by
  exact ((hasDerivAt_innerQprime hn ht).add (hasDerivAt_innerHprime hn ht)).add_const 2

theorem innerH_pos (n : ℕ) {t : ℝ} (ht : t < 2) : 0 < innerH n t :=
  div_pos (by norm_num) (pow_pos (sub_pos.mpr ht) n)

theorem innerHprime_pos {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    0 < innerHprime n t := by
  have hN : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact div_pos (mul_pos (innerH_pos n (by linarith [ht.2])) hN) (inner_domain ht).2.1

theorem innerHsecond_pos {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    0 < innerHsecond n t := by
  have hN : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact div_pos (mul_pos (mul_pos (innerH_pos n (by linarith [ht.2])) hN) (by linarith))
    (sq_pos_of_pos (inner_domain ht).2.1)

theorem innerFprime_neg {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    innerFprime n t < 0 := by
  have hq := innerQprime_neg hn ht
  have hh := innerHprime_pos (n:=n) (by omega) ht
  dsimp [innerFprime]
  linarith

theorem innerGsecond_pos {n : ℕ} (hn : 3 ≤ n) {t : ℝ} (ht : t ∈ Ioo 0 (1/2)) :
    0 < innerGsecond n t :=
  add_pos (innerQsecond_pos hn ht) (innerHsecond_pos (by omega) ht)

theorem innerF_strictAnti {n : ℕ} (hn : 2 ≤ n) : StrictAntiOn (innerF n) (Ioo 0 (1/2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (fun t ht => (continuousAt_innerF n ht.1.ne' (inner_domain ht).2.1.ne').continuousWithinAt)
  intro t ht
  have ht' := interior_subset ht
  rw [(hasDerivAt_innerF (by omega) ht').deriv]
  exact innerFprime_neg hn ht'

theorem innerGprime_strictMono {n : ℕ} (hn : 3 ≤ n) :
    StrictMonoOn (innerGprime n) (Ioo 0 (1/2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (fun t ht => (hasDerivAt_innerGprime (by omega) ht).continuousAt.continuousWithinAt)
  intro t ht
  have ht' := interior_subset ht
  rw [(hasDerivAt_innerGprime (by omega) ht').deriv]
  exact innerGsecond_pos hn ht'

theorem innerA_eq_u_div {t : ℝ} (ht0 : t ≠ 0) (ht2 : 2-t ≠ 0) :
    innerA t = u t/(2-t) := by
  dsimp [innerA,u]
  field_simp [ht0,ht2]

theorem normalized_even_inner_factor (n : ℕ) (he : Even n) {t : ℝ}
    (ht0 : t ≠ 0) (ht2 : 2-t ≠ 0) : normalized n t = (2-t)^n*innerF n t := by
  rw [normalized_even n he]
  dsimp [innerF,innerQ,innerH]
  rw [innerA_eq_u_div ht0 ht2,div_pow]
  field_simp [ht2,pow_ne_zero n ht2]
  ring

theorem normalized_odd_inner_factor (n : ℕ) (ho : Odd n) {t : ℝ}
    (ht0 : t ≠ 0) (ht2 : 2-t ≠ 0) : normalized n t = (2-t)^n*innerG n t := by
  rw [normalized_odd n ho]
  dsimp [innerG,innerQ,innerH]
  rw [innerA_eq_u_div ht0 ht2,div_pow]
  field_simp [ht2,pow_ne_zero n ht2]
  ring

theorem inner_even_root_iff (n : ℕ) (hn : 1 ≤ n) (he : Even n) {t : ℝ}
    (ht : t ∈ Ioo 0 (1/2)) : (realPolynomial n).IsRoot (-t) ↔ innerF n t = 0 := by
  rw [real_root_iff_normalized n hn ht.1,normalized_even_inner_factor n he ht.1.ne'
    (inner_domain ht).2.1.ne',mul_eq_zero]
  simp [pow_ne_zero n (inner_domain ht).2.1.ne']

theorem inner_odd_root_iff (n : ℕ) (hn : 1 ≤ n) (ho : Odd n) {t : ℝ}
    (ht : t ∈ Ioo 0 (1/2)) : (realPolynomial n).IsRoot (-t) ↔ innerG n t = 0 := by
  rw [real_root_iff_normalized n hn ht.1,normalized_odd_inner_factor n ho ht.1.ne'
    (inner_domain ht).2.1.ne',mul_eq_zero]
  simp [pow_ne_zero n (inner_domain ht).2.1.ne']

#print axioms innerH_eq_inv_pow
#print axioms continuousAt_innerQ
#print axioms continuousAt_innerH
#print axioms continuousAt_innerF
#print axioms continuousAt_innerG
#print axioms hasDerivAt_innerH
#print axioms hasDerivAt_innerHprime
#print axioms hasDerivAt_innerF
#print axioms hasDerivAt_innerG
#print axioms hasDerivAt_innerGprime
#print axioms innerH_pos
#print axioms innerHprime_pos
#print axioms innerHsecond_pos
#print axioms innerFprime_neg
#print axioms innerGsecond_pos
#print axioms innerF_strictAnti
#print axioms innerGprime_strictMono
#print axioms innerA_eq_u_div
#print axioms normalized_even_inner_factor
#print axioms normalized_odd_inner_factor
#print axioms inner_even_root_iff
#print axioms inner_odd_root_iff
end BookCompletion
