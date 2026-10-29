import Forcing

set_option maxHeartbeats 2000000
noncomputable section
namespace Motzkin.Forcing
open Motzkin.Certificate

def ScaledHypotheses (B : ℝ) (a e : ℕ → ℝ) : Prop :=
  0 ≤ B ∧ 900*B < a 12 ∧ L 12 < a 13/a 12 ∧ a 13/a 12 < U 12 ∧
  ∀ m : ℕ, 14 ≤ m → |e m| ≤ B ∧
    ((m:ℝ)+2)*a m = (m:ℝ)*(2*a (m-1)+3*a (m-2))+e m

theorem scale_hypotheses (a e : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hseed : 1800 < c*a 12) (hL : L 12 < a 13/a 12) (hU : a 13/a 12 < U 12)
    (hrec : ∀ m : ℕ, 14 ≤ m → |c*e m| ≤ 2 ∧
      ((m:ℝ)+2)*a m = (m:ℝ)*(2*a (m-1)+3*a (m-2))+e m) :
    Hypotheses (fun n => c*a n) (fun n => c*e n) := by
  refine ⟨hseed,?_,?_,?_⟩
  · simpa only [mul_div_mul_left _ _ (ne_of_gt hc)] using hL
  · simpa only [mul_div_mul_left _ _ (ne_of_gt hc)] using hU
  · intro m hm
    refine ⟨(hrec m hm).1,?_⟩
    linear_combination c*(hrec m hm).2

theorem positive_scale_transfer (a e : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (h : Hypotheses (fun n => c*a n) (fun n => c*e n)) (n : ℕ) (hn : 12 ≤ n) :
    8*((n:ℝ)+3)^2 < c*a n ∧ L (n:ℝ) < a (n+1)/a n ∧
      a (n+1)/a n < U (n:ℝ) ∧ QuarticGap a n := by
  have hscaled := robust_bounded_forcing _ _ h n hn
  have hgap : c^4*(800*(a n)^4) <
      c^4*(((n:ℝ)+3)^3*(a n*(a (n+2))^3-(a (n+1))^3*a (n+3))) := by
    convert hscaled.2.2.2 using 1 <;> ring
  refine ⟨hscaled.1,?_,?_,?_⟩
  · simpa only [mul_div_mul_left _ _ (ne_of_gt hc)] using hscaled.2.1
  · simpa only [mul_div_mul_left _ _ (ne_of_gt hc)] using hscaled.2.2.1
  · exact (mul_lt_mul_left (pow_pos hc 4)).mp hgap

theorem scaled_bounded_forcing (B : ℝ) (a e : ℕ → ℝ) (h : ScaledHypotheses B a e) :
    ∀ n : ℕ, 12 ≤ n →
      4*B*((n:ℝ)+3)^2 < a n ∧
      L (n:ℝ) < a (n+1)/a n ∧ a (n+1)/a n < U (n:ℝ) ∧ QuarticGap a n := by
  rcases h with ⟨hB,hseed,hL,hU,hrec⟩
  by_cases hz : B=0
  · have ha12 : 0 < a 12 := by simpa only [hz,mul_zero] using hseed
    let c : ℝ := 1801/a 12
    have hc : 0 < c := div_pos (by norm_num) ha12
    have hca : c*a 12=1801 := by dsimp [c]; field_simp
    have hs : 1800 < c*a 12 := by rw [hca]; norm_num
    have hscaled := scale_hypotheses a e c hc hs hL hU (by
      intro m hm
      have hmrec := hrec m hm
      have hem : e m=0 := by
        have he := hmrec.1
        rw [hz] at he
        exact abs_eq_zero.mp (le_antisymm he (abs_nonneg _))
      exact ⟨by rw [hem,mul_zero,abs_zero]; norm_num,hmrec.2⟩)
    intro n hn
    have ht := positive_scale_transfer a e c hc hscaled n hn
    refine ⟨?_,ht.2.1,ht.2.2.1,ht.2.2.2⟩
    rw [hz,mul_zero,zero_mul]
    have hpos : 0 < c*a n := lt_of_le_of_lt (by positivity) ht.1
    nlinarith
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hz)
    let c : ℝ := 2/B
    have hc : 0 < c := div_pos (by norm_num) hBpos
    have hcB : c*B=2 := by dsimp [c]; field_simp
    have hs : 1800 < c*a 12 := by
      have hp := mul_lt_mul_of_pos_left hseed hc
      have hid : c*(900*B)=1800 := by
        calc
          c*(900*B)=900*(c*B) := by ring
          _ = 1800 := by rw [hcB]; norm_num
      rw [hid] at hp
      exact hp
    have hscaled := scale_hypotheses a e c hc hs hL hU (by
      intro m hm
      have hmrec := hrec m hm
      refine ⟨?_,hmrec.2⟩
      rw [abs_mul,abs_of_pos hc]
      exact (mul_le_mul_of_nonneg_left hmrec.1 (le_of_lt hc)).trans_eq hcB)
    intro n hn
    have ht := positive_scale_transfer a e c hc hscaled n hn
    refine ⟨?_,ht.2.1,ht.2.2.1,ht.2.2.2⟩
    apply (mul_lt_mul_left hc).mp
    convert ht.1 using 1
    calc
      c*(4*B*((n:ℝ)+3)^2) = 4*(c*B)*((n:ℝ)+3)^2 := by ring
      _ = 8*((n:ℝ)+3)^2 := by rw [hcB]; ring

theorem scaled_bounded_forcing_division (B : ℝ) (a e : ℕ → ℝ) (h : ScaledHypotheses B a e) :
    ∀ n : ℕ, 12 ≤ n →
      4*B*((n:ℝ)+3)^2 < a n ∧
      L (n:ℝ) < a (n+1)/a n ∧ a (n+1)/a n < U (n:ℝ) ∧
      800*(a n)^4/((n:ℝ)+3)^3 < a n*(a (n+2))^3-(a (n+1))^3*a (n+3) ∧
      0 < 800*(a n)^4/((n:ℝ)+3)^3 := by
  intro n hn
  have ht := scaled_bounded_forcing B a e h n hn
  have hB := h.1
  have ha : 0 < a n := lt_of_le_of_lt (by positivity : 0 ≤ 4*B*((n:ℝ)+3)^2) ht.1
  have h3 : 0 < (n:ℝ)+3 := by positivity
  refine ⟨ht.1,ht.2.1,ht.2.2.1,?_,?_⟩
  · apply (div_lt_iff₀ (pow_pos h3 3)).2
    have hgap := ht.2.2.2
    unfold QuarticGap at hgap
    simpa only [mul_comm] using hgap
  · positivity

#print axioms positive_scale_transfer
#print axioms scaled_bounded_forcing
#print axioms scaled_bounded_forcing_division
end Motzkin.Forcing
