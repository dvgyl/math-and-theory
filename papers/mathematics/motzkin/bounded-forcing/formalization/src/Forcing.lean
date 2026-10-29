import Growth
import Rectangle
import Corner

set_option maxHeartbeats 2000000
noncomputable section
namespace Motzkin.Forcing
open Motzkin.Certificate

def QuarticGap (a : ℕ → ℝ) (n : ℕ) : Prop :=
  800*(a n)^4 < ((n:ℝ)+3)^3*(a n*(a (n+2))^3-(a (n+1))^3*a (n+3))

theorem local_normalization (a e : ℕ → ℝ) (h : Hypotheses a e)
    (n : ℕ) (hn : 12 ≤ n) :
    F (n:ℝ) (a (n+1)/a n) (e (n+2)/(2*a n)) (e (n+3)/(2*a n)) =
      (a n*(a (n+2))^3-(a (n+1))^3*a (n+3))/(a n)^4 := by
  have hg := (growth_ratio a e h n hn).1
  have ha : 0 < a n := lt_of_le_of_lt (by positivity : 0 ≤ 8*((n:ℝ)+3)^2) hg
  have hrec2 := (h.2.2.2 (n+2) (by omega)).2
  have hrec3 := (h.2.2.2 (n+3) (by omega)).2
  have hr2 : ((n:ℝ)+4)*a (n+2) = ((n:ℝ)+2)*(2*a (n+1)+3*a n)+e (n+2) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,show n+2-1=n+1 by omega,
      show n+2-2=n by omega,show (n:ℝ)+2+2=(n:ℝ)+4 by ring] using hrec2
  have hr3 : ((n:ℝ)+5)*a (n+3) = ((n:ℝ)+3)*(2*a (n+2)+3*a (n+1))+e (n+3) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,show n+3-1=n+2 by omega,
      show n+3-2=n+1 by omega,show (n:ℝ)+3+2=(n:ℝ)+5 by ring] using hrec3
  have hy : y (n:ℝ) (a (n+1)/a n) (e (n+2)/(2*a n)) = a (n+2)/a n := by
    unfold y
    field_simp [ne_of_gt ha]
    linear_combination -(2*(a n)^2)*hr2
  have hz : z (n:ℝ) (a (n+1)/a n) (e (n+2)/(2*a n)) (e (n+3)/(2*a n)) = a (n+3)/a n := by
    unfold z
    rw [hy]
    field_simp [ne_of_gt ha]
    linear_combination -(2*(a n)^2)*hr3
  unfold F
  rw [hy,hz]
  field_simp [ne_of_gt ha]
  ring

theorem quartic_gap (a e : ℕ → ℝ) (h : Hypotheses a e)
    (n : ℕ) (hn : 12 ≤ n) : QuarticGap a n := by
  have hg := growth_ratio a e h n hn
  have hnr : (12:ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < a n := lt_of_le_of_lt (by positivity : 0 ≤ 8*((n:ℝ)+3)^2) hg.1
  have hu := normalized_error (n:ℝ) (a n) (e (n+2)) hnr hg.1
    (h.2.2.2 (n+2) (by omega)).1
  have hv := normalized_error (n:ℝ) (a n) (e (n+3)) hnr hg.1
    (h.2.2.2 (n+3) (by omega)).1
  have hc := corner_comparison (n:ℝ) (a (n+1)/a n)
    (e (n+2)/(2*a n)) (e (n+3)/(2*a n)) hnr
    (le_of_lt hg.2.1) (le_of_lt hg.2.2) (le_of_lt hu) (le_of_lt hv)
  have hbound := (corner_gap (n:ℝ) hnr).trans_le hc
  rw [local_normalization a e h n hn] at hbound
  have h3 : 0 < (n:ℝ)+3 := by positivity
  have hmul := (div_lt_div_iff₀ (pow_pos h3 3) (pow_pos ha 4)).1 hbound
  unfold QuarticGap
  simpa only [mul_comm] using hmul

theorem robust_bounded_forcing (a e : ℕ → ℝ) (h : Hypotheses a e) :
    ∀ n : ℕ, 12 ≤ n →
      8*((n:ℝ)+3)^2 < a n ∧
      L (n:ℝ) < a (n+1)/a n ∧ a (n+1)/a n < U (n:ℝ) ∧
      800*(a n)^4 < ((n:ℝ)+3)^3*(a n*(a (n+2))^3-(a (n+1))^3*a (n+3)) := by
  intro n hn
  have hg := growth_ratio a e h n hn
  exact ⟨hg.1,hg.2.1,hg.2.2,quartic_gap a e h n hn⟩

theorem robust_bounded_forcing_division (a e : ℕ → ℝ) (h : Hypotheses a e) :
    ∀ n : ℕ, 12 ≤ n →
      8*((n:ℝ)+3)^2 < a n ∧
      L (n:ℝ) < a (n+1)/a n ∧ a (n+1)/a n < U (n:ℝ) ∧
      800*(a n)^4/((n:ℝ)+3)^3 < a n*(a (n+2))^3-(a (n+1))^3*a (n+3) ∧
      0 < 800*(a n)^4/((n:ℝ)+3)^3 := by
  intro n hn
  have ht := robust_bounded_forcing a e h n hn
  have ha : 0 < a n := lt_of_le_of_lt (by positivity : 0 ≤ 8*((n:ℝ)+3)^2) ht.1
  have h3 : 0 < (n:ℝ)+3 := by positivity
  refine ⟨ht.1,ht.2.1,ht.2.2.1,?_,?_⟩
  · apply (div_lt_iff₀ (pow_pos h3 3)).2
    simpa only [mul_comm] using ht.2.2.2
  · positivity

#print axioms local_normalization
#print axioms quartic_gap
#print axioms robust_bounded_forcing
#print axioms robust_bounded_forcing_division
end Motzkin.Forcing
