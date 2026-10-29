import Invariant

set_option maxHeartbeats 2000000
noncomputable section
namespace Motzkin.Forcing
open Motzkin.Certificate

def Hypotheses (a e : ℕ → ℝ) : Prop :=
  1800 < a 12 ∧ L 12 < a 13/a 12 ∧ a 13/a 12 < U 12 ∧
  ∀ m : ℕ, 14 ≤ m → |e m| ≤ 2 ∧
    ((m:ℝ)+2)*a m = (m:ℝ)*(2*a (m-1)+3*a (m-2))+e m

def GrowthRatio (a : ℕ → ℝ) (n : ℕ) : Prop :=
  8*((n:ℝ)+3)^2 < a n ∧ L (n:ℝ) < a (n+1)/a n ∧ a (n+1)/a n < U (n:ℝ)

theorem growth_ratio (a e : ℕ → ℝ) (h : Hypotheses a e) :
    ∀ n : ℕ, 12 ≤ n → GrowthRatio a n := by
  rcases h with ⟨hseed,hL,hU,hrec⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨?_,hL,hU⟩
    norm_num
    exact hseed
  | succ n hn ih =>
    rcases ih with ⟨hg,hl,hu⟩
    have hnr : (12:ℝ) ≤ n := by exact_mod_cast hn
    have hapos : 0 < a n := lt_of_le_of_lt (by positivity : 0 ≤ 8*((n:ℝ)+3)^2) hg
    have htwo : 2 < a (n+1)/a n := by
      have hb := (interval_bounds (n:ℝ) hnr).1
      linarith
    have hadouble : 2*a n < a (n+1) := (lt_div_iff₀ hapos).1 htwo
    have hgnew : 8*(((n+1:ℕ):ℝ)+3)^2 < a (n+1) := by
      norm_num only [Nat.cast_add,Nat.cast_one]
      nlinarith [sq_nonneg (n:ℝ)]
    have hnewpos : 0 < a (n+1) := lt_of_le_of_lt
      (by positivity : 0 ≤ 8*(((n+1:ℕ):ℝ)+3)^2) hgnew
    have hrecn := hrec (n+2) (by omega)
    have he := normalized_error ((n+1:ℕ):ℝ) (a (n+1)) (e (n+2))
      (by exact_mod_cast (show 12 ≤ n+1 by omega)) hgnew hrecn.1
    have hrule : ((n:ℝ)+4)*a (n+2) =
        ((n:ℝ)+2)*(2*a (n+1)+3*a n)+e (n+2) := by
      simpa only [Nat.cast_add,Nat.cast_ofNat,
        show n+2-1=n+1 by omega,show n+2-2=n by omega,
        show (n:ℝ)+2+2=(n:ℝ)+4 by ring] using hrecn.2
    have hstep : a (n+2)/a (n+1) =
        update ((n+1:ℕ):ℝ) (a (n+1)/a n) (e (n+2)/(2*a (n+1))) := by
      unfold update
      norm_num only [Nat.cast_add,Nat.cast_one]
      field_simp [ne_of_gt hapos,ne_of_gt hnewpos]
      linear_combination (2*(a (n+1))^2*((n:ℝ)+4))*hrule
    have hi := invariant_step ((n+1:ℕ):ℝ) (a (n+1)/a n) (e (n+2)/(2*a (n+1)))
      (by exact_mod_cast (show 13 ≤ n+1 by omega))
      (by simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hl)
      (by simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hu)
      (le_of_lt (neg_lt_of_abs_lt he)) (le_of_lt (lt_of_abs_lt he))
    refine ⟨hgnew,?_,?_⟩
    · simpa only [show n+1+1=n+2 by omega,hstep] using hi.1
    · simpa only [show n+1+1=n+2 by omega,hstep] using hi.2

#print axioms growth_ratio
end Motzkin.Forcing
