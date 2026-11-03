import MarginalRank

/-!
# The sharp explicit rectangular optimizer-rank ceiling

For a target coefficient matrix of rank k in an m-by-n system, every actual
state maximizing its pure-target overlap under the two fixed marginals has
rank at most 1 + Rmax(m,n,k). This module proves the finite integer optimization
and connects it directly to the actual PSD matrix theorem in MarginalRank.
Sharpness constructions remain the exact written and symbolic witnesses in
the report; no optimality or sharpness of the numerical ceiling is axiomatized.
-/
set_option autoImplicit false
noncomputable section
open Matrix
open MilneExpanded

namespace MilneContinuation

/-- Maximum possible product rs under r≤m, s≤n and r+s+k≤m+n. -/
def residualRankMaximum (m n k : ℕ) : ℕ :=
  if n + k ≤ m then n * (m - k)
  else if m + k ≤ n then m * (n - k)
  else (m + n - k)^2 / 4

lemma product_le_unbalanced_ceiling {r s t n : ℕ}
    (hs : s ≤ n) (hn : n ≤ t) (hsum : r + s ≤ t + n) :
    r * s ≤ t * n := by
  have hs' : (s : ℤ) ≤ n := by exact_mod_cast hs
  have ht' : (s : ℤ) ≤ t := by exact_mod_cast hs.trans hn
  have he : (r : ℤ) + s ≤ (t : ℤ) + n := by exact_mod_cast hsum
  have hprod := mul_nonneg (sub_nonneg.mpr hs') (sub_nonneg.mpr ht')
  have hscaled := mul_le_mul_of_nonneg_right he (show (0 : ℤ) ≤ s by positivity)
  have hgoal : (r : ℤ) * s ≤ (t : ℤ) * n := by nlinarith
  exact_mod_cast hgoal

lemma four_product_le_square_sum_bound {r s N : ℕ} (h : r + s ≤ N) :
    4 * (r * s) ≤ N^2 := by
  have hz : (r : ℤ) + (s : ℤ) ≤ (N : ℤ) := by exact_mod_cast h
  have hr : (0 : ℤ) ≤ r := by positivity
  have hs : (0 : ℤ) ≤ s := by positivity
  have hN : (0 : ℤ) ≤ N := by positivity
  have hh : 4 * ((r : ℤ) * (s : ℤ)) ≤ (N : ℤ)^2 := by
    nlinarith [sq_nonneg ((r : ℤ) - (s : ℤ))]
  exact_mod_cast hh

/-- The exact integer product ceiling, with no analytic or spectral assumption. -/
theorem residual_product_le_maximum {m n k r s : ℕ}
    (hr : r ≤ m) (hs : s ≤ n) (hsum : r + s + k ≤ m + n) :
    r * s ≤ residualRankMaximum m n k := by
  unfold residualRankMaximum
  split_ifs with hleft hright
  · have hn : n ≤ m - k := by omega
    have htotal : r + s ≤ (m - k) + n := by omega
    simpa only [Nat.mul_comm] using product_le_unbalanced_ceiling hs hn htotal
  · have hm : m ≤ n - k := by omega
    have htotal : s + r ≤ (n - k) + m := by omega
    simpa only [Nat.mul_comm] using product_le_unbalanced_ceiling hr hm htotal
  · have htotal : r + s ≤ m + n - k := by omega
    have hfour := four_product_le_square_sum_bound htotal
    omega

/-- Every actual fixed-marginal pure-target optimizer satisfies the explicit
rectangular ceiling. Positivity, target Schmidt rank and both marginal
constraints enter through actual matrices; no support conclusion is assumed. -/
theorem every_optimizer_explicit_rectangular_rank_bound
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : A.trace = 1) (hB : B.trace = 1) (X : Matrix a b ℂ)
    (M : Matrix (a × b) (a × b) ℂ) (hM : Compatible A B M)
    (hopt : ∀ N, Compatible A B N →
      expectation N (targetVector X) ≤ expectation M (targetVector X)) :
    M.rank ≤ 1 + residualRankMaximum (Fintype.card a) (Fintype.card b) X.rank := by
  obtain ⟨r, s, hr, hs, hsum, hMbound⟩ := every_optimizer_rank_bound
    A B hA hB X M hM hopt
  exact hMbound.trans (Nat.add_le_add_left (residual_product_le_maximum hr hs hsum) 1)

end MilneContinuation

#print axioms MilneContinuation.residual_product_le_maximum
#print axioms MilneContinuation.every_optimizer_explicit_rectangular_rank_bound
