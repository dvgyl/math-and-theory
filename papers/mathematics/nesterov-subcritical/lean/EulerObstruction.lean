import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
Euler-type obstruction for an arbitrary damping `r > 1`: a scalar function `H`
with `H'' + (r / t) H' ≥ c / t²` (`c > 0`) on `[T, ∞)` cannot stay bounded
above.  Proof: `K = t^r H' - c t^(r-1) / (r-1)` is nondecreasing, hence
`G = H + K(T) t^(1-r) / (r-1) - c log t / (r-1)` is nondecreasing, which forces
logarithmic growth of `H`.  For `r = 2` this is the damping-two obstruction.
-/

set_option autoImplicit false

namespace NesterovPlanar

lemma monotoneOn_Ici_of_hasDerivAt_nonneg
    {F F' : ℝ → ℝ} {T : ℝ}
    (hF : ∀ t, T ≤ t → HasDerivAt F (F' t) t)
    (hF' : ∀ t, T ≤ t → 0 ≤ F' t) : MonotoneOn F (Set.Ici T) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici T)
  · intro t ht
    exact (hF t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hF t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hF t (interior_subset ht)).deriv]
    exact hF' t (interior_subset ht)

/-- A twice differentiable scalar function satisfying the damping-`r` Euler
differential inequality cannot remain bounded above. Explicit derivative
functions are used, so no regularity is hidden in iterated `deriv`. -/
theorem unbounded_of_euler_forcing
    {H D DD : ℝ → ℝ} {r T c : ℝ}
    (hr : 1 < r) (hT : 0 < T) (hc : 0 < c)
    (hH : ∀ t, T ≤ t → HasDerivAt H (D t) t)
    (hD : ∀ t, T ≤ t → HasDerivAt D (DD t) t)
    (hforce : ∀ t, T ≤ t → c / t ^ 2 ≤ DD t + (r / t) * D t) :
    ¬ ∃ M : ℝ, ∀ t, T ≤ t → H t ≤ M := by
  rintro ⟨M, hM⟩
  have hr1 : 0 < r - 1 := by linarith
  have hr1ne : r - 1 ≠ 0 := hr1.ne'
  have hcne : c ≠ 0 := hc.ne'
  -- `K t = t^r D t - c t^(r-1) / (r-1)` is nondecreasing on `[T, ∞)`.
  have hK : ∀ t, T ≤ t → HasDerivAt (fun s => s ^ r * D s - c / (r - 1) * s ^ (r - 1))
      (r * t ^ (r - 1) * D t + t ^ r * DD t -
        c / (r - 1) * ((r - 1) * t ^ (r - 1 - 1))) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hT ht
    exact ((Real.hasDerivAt_rpow_const (p := r) (Or.inl htpos.ne')).mul (hD t ht)).sub
      ((Real.hasDerivAt_rpow_const (p := r - 1) (Or.inl htpos.ne')).const_mul (c / (r - 1)))
  have hKnonneg : ∀ t, T ≤ t →
      0 ≤ r * t ^ (r - 1) * D t + t ^ r * DD t -
        c / (r - 1) * ((r - 1) * t ^ (r - 1 - 1)) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hT ht
    have htne : t ≠ 0 := htpos.ne'
    have hp : 0 < t ^ r := Real.rpow_pos_of_pos htpos r
    have e1 : t ^ (r - 1) = t ^ r / t := Real.rpow_sub_one htne r
    have e2 : t ^ (r - 1 - 1) = t ^ r / t / t := by
      rw [Real.rpow_sub_one htne (r - 1), e1]
    have hf := mul_le_mul_of_nonneg_left (hforce t ht) hp.le
    have key : r * t ^ (r - 1) * D t + t ^ r * DD t -
        c / (r - 1) * ((r - 1) * t ^ (r - 1 - 1)) =
        t ^ r * (DD t + r / t * D t) - t ^ r * (c / t ^ 2) := by
      rw [e1, e2]
      field_simp
      ring
    rw [key]
    linarith
  have hKmono : MonotoneOn (fun s => s ^ r * D s - c / (r - 1) * s ^ (r - 1)) (Set.Ici T) :=
    monotoneOn_Ici_of_hasDerivAt_nonneg hK hKnonneg
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = T ^ r * D T - c / (r - 1) * T ^ (r - 1) := ⟨_, rfl⟩
  -- `G t = H t + k t^(1-r) / (r-1) - c log t / (r-1)` is nondecreasing on `[T, ∞)`.
  have hG : ∀ t, T ≤ t → HasDerivAt
      (fun s => H s + k / (r - 1) * s ^ (1 - r) - c / (r - 1) * Real.log s)
      (D t + k / (r - 1) * ((1 - r) * t ^ (1 - r - 1)) - c / (r - 1) * t⁻¹) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hT ht
    exact ((hH t ht).add ((Real.hasDerivAt_rpow_const (p := 1 - r)
      (Or.inl htpos.ne')).const_mul (k / (r - 1)))).sub
      ((Real.hasDerivAt_log htpos.ne').const_mul (c / (r - 1)))
  have hGnonneg : ∀ t, T ≤ t →
      0 ≤ D t + k / (r - 1) * ((1 - r) * t ^ (1 - r - 1)) - c / (r - 1) * t⁻¹ := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hT ht
    have htne : t ≠ 0 := htpos.ne'
    have hq : 0 < t ^ (1 - r - 1) := Real.rpow_pos_of_pos htpos _
    have hqp : t ^ (1 - r - 1) * t ^ r = 1 := by
      rw [← Real.rpow_add htpos, show 1 - r - 1 + r = (0 : ℝ) by ring, Real.rpow_zero]
    have e1 : t ^ (r - 1) = t ^ r / t := Real.rpow_sub_one htne r
    have hKt : k ≤ t ^ r * D t - c / (r - 1) * t ^ (r - 1) := by
      rw [hk]
      exact hKmono Set.left_mem_Ici ht ht
    have hkq : k / (r - 1) * ((1 - r) * t ^ (1 - r - 1)) = -(k * t ^ (1 - r - 1)) := by
      field_simp
      ring
    have key : D t + k / (r - 1) * ((1 - r) * t ^ (1 - r - 1)) - c / (r - 1) * t⁻¹ =
        t ^ (1 - r - 1) * ((t ^ r * D t - c / (r - 1) * t ^ (r - 1)) - k) := by
      rw [hkq, e1]
      linear_combination (c / (r - 1) * t⁻¹ - D t) * hqp
    rw [key]
    exact mul_nonneg hq.le (sub_nonneg.mpr hKt)
  have hGmono : MonotoneOn
      (fun s => H s + k / (r - 1) * s ^ (1 - r) - c / (r - 1) * Real.log s) (Set.Ici T) :=
    monotoneOn_Ici_of_hasDerivAt_nonneg hG hGnonneg
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = H T + k / (r - 1) * T ^ (1 - r) - c / (r - 1) * Real.log T -
      |k| / (r - 1) * T ^ (1 - r) := ⟨_, rfl⟩
  -- Logarithmic lower bound `H t ≥ A + c log t / (r-1)` on `[T, ∞)`.
  have hlower : ∀ t, T ≤ t → A + c / (r - 1) * Real.log t ≤ H t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hT ht
    have hGt : H T + k / (r - 1) * T ^ (1 - r) - c / (r - 1) * Real.log T ≤
        H t + k / (r - 1) * t ^ (1 - r) - c / (r - 1) * Real.log t :=
      hGmono Set.left_mem_Ici ht ht
    have hpow : t ^ (1 - r) ≤ T ^ (1 - r) :=
      Real.rpow_le_rpow_of_exponent_nonpos hT ht (by linarith)
    have hpow0 : 0 ≤ t ^ (1 - r) := (Real.rpow_pos_of_pos htpos _).le
    have habs : k * t ^ (1 - r) ≤ |k| * T ^ (1 - r) :=
      calc
        k * t ^ (1 - r) ≤ |k| * t ^ (1 - r) :=
          mul_le_mul_of_nonneg_right (le_abs_self k) hpow0
        _ ≤ |k| * T ^ (1 - r) := mul_le_mul_of_nonneg_left hpow (abs_nonneg k)
    have hdiv : k / (r - 1) * t ^ (1 - r) ≤ |k| / (r - 1) * T ^ (1 - r) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right habs hr1.le
    rw [hA]
    linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = max T (Real.exp ((M - A + 1) * (r - 1) / c)) := ⟨_, rfl⟩
  have hTs : T ≤ s := by rw [hs]; exact le_max_left _ _
  have hlog : (M - A + 1) * (r - 1) / c ≤ Real.log s := by
    calc
      (M - A + 1) * (r - 1) / c = Real.log (Real.exp ((M - A + 1) * (r - 1) / c)) :=
        (Real.log_exp _).symm
      _ ≤ Real.log s := Real.log_le_log (Real.exp_pos _) (by rw [hs]; exact le_max_right _ _)
  have hmul : M - A + 1 ≤ c / (r - 1) * Real.log s := by
    have h := mul_le_mul_of_nonneg_left hlog (div_pos hc hr1).le
    have he : c / (r - 1) * ((M - A + 1) * (r - 1) / c) = M - A + 1 := by
      field_simp
      ring
    linarith
  have h1 := hlower s hTs
  have h2 := hM s hTs
  linarith

end NesterovPlanar
