import EvenRoots
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace SquareFlowerCompletion.RealCompanion
open Set Filter Topology

def leftCoordinate (n : ℕ) : ℝ :=
  if hn : 4 ≤ n then Classical.choose (F_left_zero hn) else 1
def rightCoordinate (n : ℕ) : ℝ :=
  if hn : 4 ≤ n then Classical.choose (F_right_zero hn) else 2

theorem leftCoordinate_spec {n : ℕ} (hn : 4 ≤ n) :
    leftCoordinate n ∈ Ioo 1 (5/4) ∧ F n (leftCoordinate n) = 0 := by
  unfold leftCoordinate
  rw [dif_pos hn]
  exact Classical.choose_spec (F_left_zero hn)

theorem rightCoordinate_spec {n : ℕ} (hn : 4 ≤ n) :
    rightCoordinate n ∈ Ioo (3/2) 2 ∧ F n (rightCoordinate n) = 0 := by
  unfold rightCoordinate
  rw [dif_pos hn]
  exact Classical.choose_spec (F_right_zero hn)

theorem a_lt_one {t : ℝ} (ht : t ∈ Ioo 1 2) : a t < 1 := by
  have hp := mul_pos (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)
  dsimp [a]
  nlinarith

theorem F_increases_order (n : ℕ) {t : ℝ} (ht : t ∈ Ioo 1 2) :
    F n t < F (n+2) t := by
  have ha0 := (a_pos t).le
  have ha1 := a_lt_one ht
  have hp := pow_lt_pow_right₀ (by linarith : (1:ℝ) < 2-a t)
    (show n < n+2 by omega)
  have hq : (a t)^(n+2) ≤ (a t)^n := pow_le_pow_of_le_one ha0 ha1.le (by omega)
  have hr := mul_le_mul_of_nonneg_left hq (by linarith [ht.1] : 0 ≤ t)
  dsimp [F]
  linarith

theorem F_eventually_positive {t : ℝ} (ht : t ∈ Ioo 1 2) :
    ∀ᶠ n : ℕ in atTop, 0 < F n t := by
  have ha0 := (a_pos t).le
  have ha1 := a_lt_one ht
  have hlim := tendsto_pow_atTop_atTop_of_one_lt (by linarith : (1:ℝ) < 2-a t)
  have he : ∀ᶠ n : ℕ in atTop, (4:ℝ) < (2-a t)^n :=
    hlim.eventually (eventually_gt_atTop 4)
  filter_upwards [he] with n hn
  have hq : (a t)^n ≤ 1 := pow_le_one₀ ha0 ha1.le
  have hr := mul_le_mul_of_nonneg_left hq (by linarith [ht.1] : 0 ≤ t)
  dsimp [F]
  nlinarith [ht.2]

theorem leftCoordinate_strict_motion {n : ℕ} (hn : 4 ≤ n) :
    leftCoordinate (n+2) < leftCoordinate n := by
  have hs := leftCoordinate_spec hn
  have hs' := leftCoordinate_spec (n:=n+2) (by omega)
  have hg := F_increases_order n (t:=leftCoordinate n) ⟨hs.1.1,by linarith [hs.1.2]⟩
  rw [hs.2] at hg
  by_contra h
  have hm := (F_strictMono_left (n:=n+2) (by omega)).monotoneOn
    ⟨hs.1.1.le,hs.1.2.le⟩ ⟨hs'.1.1.le,hs'.1.2.le⟩ (le_of_not_gt h)
  rw [hs'.2] at hm
  linarith

theorem rightCoordinate_strict_motion {n : ℕ} (hn : 4 ≤ n) :
    rightCoordinate n < rightCoordinate (n+2) := by
  have hs := rightCoordinate_spec hn
  have hs' := rightCoordinate_spec (n:=n+2) (by omega)
  have hg := F_increases_order n (t:=rightCoordinate n) ⟨by linarith [hs.1.1],hs.1.2⟩
  rw [hs.2] at hg
  by_contra h
  have hm := (F_strictAnti_right (n:=n+2) (by omega)).antitoneOn
    ⟨hs'.1.1.le,hs'.1.2.le⟩ ⟨hs.1.1.le,hs.1.2.le⟩ (le_of_not_gt h)
  rw [hs'.2] at hm
  linarith

theorem leftCoordinate_tendsto : Tendsto leftCoordinate atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [eventually_ge_atTop 4] with n hn
    exact hb.trans (leftCoordinate_spec hn).1.1
  · intro b hb
    obtain ⟨t,ht1,htm⟩ := exists_between (lt_min hb (by norm_num : (1:ℝ) < 5/4))
    have ht5 : t < 5/4 := htm.trans_le (min_le_right _ _)
    have htb : t < b := htm.trans_le (min_le_left _ _)
    have ht : t ∈ Ioo 1 2 := ⟨ht1,by linarith⟩
    filter_upwards [eventually_ge_atTop 4,F_eventually_positive ht] with n hn hp
    have hs := leftCoordinate_spec hn
    have hlt : leftCoordinate n < t := by
      by_contra h
      have hm := (F_strictMono_left hn).monotoneOn
        ⟨ht1.le,ht5.le⟩ ⟨hs.1.1.le,hs.1.2.le⟩ (le_of_not_gt h)
      rw [hs.2] at hm
      linarith
    exact hlt.trans htb

theorem rightCoordinate_tendsto : Tendsto rightCoordinate atTop (𝓝 2) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨t,hmt,ht2⟩ := exists_between (max_lt hb (by norm_num : (3/2:ℝ) < 2))
    have ht3 : 3/2 < t := (le_max_right _ _).trans_lt hmt
    have hbt : b < t := (le_max_left _ _).trans_lt hmt
    have ht : t ∈ Ioo 1 2 := ⟨by linarith,ht2⟩
    filter_upwards [eventually_ge_atTop 4,F_eventually_positive ht] with n hn hp
    have hs := rightCoordinate_spec hn
    have hlt : t < rightCoordinate n := by
      by_contra h
      have hm := (F_strictAnti_right hn).antitoneOn
        ⟨hs.1.1.le,hs.1.2.le⟩ ⟨ht3.le,ht2.le⟩ (le_of_not_gt h)
      rw [hs.2] at hm
      linarith
    exact hbt.trans hlt
  · intro b hb
    filter_upwards [eventually_ge_atTop 4] with n hn
    exact (rightCoordinate_spec hn).1.2.trans hb

theorem selected_even_real_root_classification {n : ℕ} (he : Even n) (hn : 4 ≤ n)
    (x : ℝ) : (Counting.complexDominationPolynomial n).eval (x:ℂ) = 0 ↔
      x = 0 ∨ x = -leftCoordinate n ∨ x = -rightCoordinate n := by
  obtain ⟨l,hl,r,hr,hFl,hFr,hclass,_,_⟩ := even_order_real_root_classification he hn
  have hls := leftCoordinate_spec hn
  have hrs := rightCoordinate_spec hn
  have hll : leftCoordinate n = l := (F_strictMono_left hn).injOn
    ⟨hls.1.1.le,hls.1.2.le⟩ ⟨hl.1.le,hl.2.le⟩ (hls.2.trans hFl.symm)
  have hrr : rightCoordinate n = r := (F_strictAnti_right hn).injOn
    ⟨hrs.1.1.le,hrs.1.2.le⟩ ⟨hr.1.le,hr.2.le⟩ (hrs.2.trans hFr.symm)
  simpa only [hll,hrr] using hclass x

theorem even_index_tendsto : Tendsto (fun k : ℕ => 2*k+4) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with k hk
  omega

theorem even_leftCoordinate_tendsto :
    Tendsto (fun k : ℕ => leftCoordinate (2*k+4)) atTop (𝓝 1) :=
  leftCoordinate_tendsto.comp even_index_tendsto

theorem even_rightCoordinate_tendsto :
    Tendsto (fun k : ℕ => rightCoordinate (2*k+4)) atTop (𝓝 2) :=
  rightCoordinate_tendsto.comp even_index_tendsto

theorem even_selected_real_root_classification (k : ℕ) (x : ℝ) :
    (Counting.complexDominationPolynomial (2*k+4)).eval (x:ℂ) = 0 ↔
      x = 0 ∨ x = -leftCoordinate (2*k+4) ∨ x = -rightCoordinate (2*k+4) := by
  apply selected_even_real_root_classification
  · exact ⟨k+2,by omega⟩
  · omega

#print axioms leftCoordinate_spec
#print axioms rightCoordinate_spec
#print axioms a_lt_one
#print axioms F_increases_order
#print axioms F_eventually_positive
#print axioms leftCoordinate_strict_motion
#print axioms rightCoordinate_strict_motion
#print axioms leftCoordinate_tendsto
#print axioms rightCoordinate_tendsto
#print axioms selected_even_real_root_classification
#print axioms even_index_tendsto
#print axioms even_leftCoordinate_tendsto
#print axioms even_rightCoordinate_tendsto
#print axioms even_selected_real_root_classification
end SquareFlowerCompletion.RealCompanion
