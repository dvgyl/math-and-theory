import BookInnerShape

set_option maxHeartbeats 1000000
noncomputable section
open Set
namespace BookCompletion

theorem innerF_tenth_pos (n : ℕ) (hn : 2≤n) : 0 < innerF n (1/10) := by
  have hpowQ : (innerA (1/10))^2 ≤ (innerA (1/10))^n :=
    pow_le_pow_right₀ (by norm_num [innerA]) hn
  have hQ : innerQ 2 (1/10) ≤ innerQ n (1/10) :=
    mul_le_mul_of_nonneg_left hpowQ (sq_nonneg _)
  have hpowH : ((2-(1/10:ℝ))⁻¹)^n ≤ ((2-(1/10:ℝ))⁻¹)^2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hH : innerH n (1/10) ≤ innerH 2 (1/10) := by
    rw [innerH_eq_inv_pow n (1/10),innerH_eq_inv_pow 2 (1/10)]
    exact mul_le_mul_of_nonneg_left hpowH (by norm_num)
  have hbase : 0 < innerF 2 (1/10) := by norm_num [innerF,innerQ,innerA,innerH]
  unfold innerF at *
  linarith

theorem innerF_half_neg (n : ℕ) : innerF n (1/2)<0 := by
  have hpow : (innerA (1/2))^n ≤ ((2-(1/2:ℝ))⁻¹)^n :=
    pow_le_pow_left₀ (by norm_num [innerA]) (by norm_num [innerA]) n
  have hQ : innerQ n (1/2) ≤ (1/2:ℝ)^2*((2-(1/2:ℝ))⁻¹)^n :=
    mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
  have hp : 0 < (2/3:ℝ)^n := pow_pos (by norm_num) n
  unfold innerF
  rw [innerH_eq_inv_pow]
  norm_num at hQ ⊢
  linarith

theorem innerG_hundredth_pos (n : ℕ) (hn : 3≤n) : 0 < innerG n (1/100) := by
  have hpow : (innerA (1/100))^3 ≤ (innerA (1/100))^n :=
    pow_le_pow_right₀ (by norm_num [innerA]) hn
  have hQ : innerQ 3 (1/100) ≤ innerQ n (1/100) :=
    mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
  have hQbase : 1 < innerQ 3 (1/100) := by norm_num [innerQ,innerA]
  have hH := innerH_pos n (t:=1/100) (by norm_num)
  unfold innerG
  linarith

theorem innerG_order3_fifth_neg : innerG 3 (1/5)<0 := by
  norm_num [innerG,innerQ,innerA,innerH]

theorem innerG_third_neg (n : ℕ) (hn : 5≤n) : innerG n (1/3)<0 := by
  have hpowQ : (innerA (1/3))^n ≤ (innerA (1/3))^5 :=
    pow_le_pow_of_le_one (by norm_num [innerA]) (by norm_num [innerA]) hn
  have hQ : innerQ n (1/3) ≤ innerQ 5 (1/3) :=
    mul_le_mul_of_nonneg_left hpowQ (sq_nonneg _)
  have hpowH : ((2-(1/3:ℝ))⁻¹)^n ≤ ((2-(1/3:ℝ))⁻¹)^5 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hH : innerH n (1/3) ≤ innerH 5 (1/3) := by
    rw [innerH_eq_inv_pow n (1/3),innerH_eq_inv_pow 5 (1/3)]
    exact mul_le_mul_of_nonneg_left hpowH (by norm_num)
  have hbase : innerG 5 (1/3)<0 := by norm_num [innerG,innerQ,innerA,innerH]
  unfold innerG at *
  linarith

theorem innerG_half_pos (n : ℕ) : 0 < innerG n (1/2) := by
  have hQ : 0 ≤ innerQ n (1/2) := by
    unfold innerQ
    exact mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num [innerA]) n)
  have hH := innerH_pos n (t:=1/2) (by norm_num)
  unfold innerG
  linarith

theorem innerG_negative_witness (n : ℕ) (hn : 3≤n) (ho : Odd n) :
    ∃ t ∈ Ioo (1/100:ℝ) (1/2), innerG n t<0 := by
  by_cases hn3 : n=3
  · subst n
    exact ⟨1/5,by norm_num,innerG_order3_fifth_neg⟩
  · have h5 : 5≤n := by rcases ho with ⟨k,hk⟩; omega
    exact ⟨1/3,by norm_num,innerG_third_neg n h5⟩

#print axioms innerF_tenth_pos
#print axioms innerF_half_neg
#print axioms innerG_hundredth_pos
#print axioms innerG_order3_fifth_neg
#print axioms innerG_third_neg
#print axioms innerG_half_pos
#print axioms innerG_negative_witness
end BookCompletion
