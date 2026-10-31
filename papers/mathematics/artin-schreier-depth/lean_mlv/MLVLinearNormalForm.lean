import MLVDepthOne

/-!
# Degree-one key valuations have the actual monomial normal form

Genuine key-polynomial minimality forbids cancellation of a nonzero constant
against a multiple of the linear key.  The resulting division recurrence,
followed by induction on polynomial degree, determines the whole valuation.
The Gauss coefficient-zero bound supplies the same key for the actual base
ball.  No algebraic-closedness assumption on the ambient field is needed.
-/

noncomputable section

open Polynomial

namespace NTCThird.MLV

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

set_option maxHeartbeats 800000

/-- A nonzero constant cannot cancel against a multiple of a linear key,
because that would make its initial form divisible by the key. -/
theorem linear_key_constant_add_mul
    (μ : AddValuation K[X] (WithTop ℚ)) (a : K)
    (hk : KeyPolynomial μ (X - C a)) (c : K) (g : K[X]) :
    μ (C c + (X - C a) * g) =
      min (μ (C c)) (μ (X - C a) + μ g) := by
  rw [← μ.map_mul]
  by_cases hc : c = 0
  · simp [hc]
  have hbound : μ (C c + (X - C a) * g) ≤ μ (C c) := by
    by_contra hn
    have hlt : μ (C c) < μ (C c + (X - C a) * g) := lt_of_not_ge hn
    have hdiv : InitialDivides μ (X - C a) (C c) := by
      refine Or.inr ⟨-g, ?_⟩
      simpa only [mul_neg, sub_neg_eq_add] using hlt
    have hmin := hk.minimal (C c) (C_ne_zero.mpr hc) hdiv
    simp at hmin
  by_cases heq : μ (C c) = μ ((X - C a) * g)
  · apply le_antisymm _ (μ.map_add _ _)
    simpa only [heq, min_self] using hbound
  · exact μ.map_add_of_distinct_val heq

/-- The coefficient-zero Gauss bound proves domination by evaluation over
arbitrary ambient fields. -/
theorem baseBall_le_evaluation_at_centre_of_gauss
    (v : AddValuation E (WithTop ℚ)) (a : K) (γ : ℚ) (f : K[X]) :
    baseBall v a γ f ≤ v (algebraMap K E (f.eval a)) := by
  change gaussValue v γ
    (taylor (algebraMap K E a) (f.map (algebraMap K E))) ≤ _
  calc
    _ ≤ weightedCoefficient v γ
        (taylor (algebraMap K E a) (f.map (algebraMap K E))) 0 :=
      gaussValue_le_coefficient v γ _ 0
    _ = v (algebraMap K E (f.eval a)) := by
      simp only [weightedCoefficient, Nat.cast_zero, zero_mul,
        WithTop.coe_zero, add_zero, taylor_coeff_zero, eval_map, eval₂_at_apply]

/-- The actual base ball has its central linear key over arbitrary ambient
fields; algebraic closedness is unnecessary for this key property. -/
theorem baseBall_linear_key_of_gauss
    (v : AddValuation E (WithTop ℚ)) (a : K) (γ : ℚ) :
    KeyPolynomial (baseBall v a γ) (X - C a) := by
  apply keyPolynomial_linear _ (v.comap (algebraMap K E)) a
  · intro c
    exact baseBall_C v a c γ
  · intro f
    exact baseBall_le_evaluation_at_centre_of_gauss v a γ f
  · rw [baseBall_linear_self]
    exact WithTop.coe_ne_top

/-- Constants and the value of a common linear key determine every
polynomial value, by division by that key and degree induction. -/
theorem linear_key_valuation_ext
    (μ ν : AddValuation K[X] (WithTop ℚ)) (a : K)
    (hμ : KeyPolynomial μ (X - C a)) (hν : KeyPolynomial ν (X - C a))
    (hC : ∀ c : K, μ (C c) = ν (C c))
    (hlinear : μ (X - C a) = ν (X - C a)) : μ = ν := by
  have hclaim : ∀ n : ℕ, ∀ f : K[X], f.natDegree = n → μ f = ν f := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf
      by_cases hn : n = 0
      · have hconst := eq_C_of_natDegree_eq_zero (hf.trans hn)
        exact (congrArg μ hconst).trans
          ((hC _).trans (congrArg ν hconst).symm)
      have hdegree : (f /ₘ (X - C a)).natDegree < n := by
        rw [natDegree_divByMonic f (monic_X_sub_C a), natDegree_X_sub_C, hf]
        omega
      have hquot : μ (f /ₘ (X - C a)) = ν (f /ₘ (X - C a)) :=
        ih _ hdegree _ rfl
      have hdecomp : f = C (f.eval a) + (X - C a) * (f /ₘ (X - C a)) := by
        rw [← modByMonic_X_sub_C_eq_C_eval f a]
        exact (modByMonic_add_div f (X - C a)).symm
      calc
        μ f = μ (C (f.eval a) + (X - C a) * (f /ₘ (X - C a))) :=
          congrArg μ hdecomp
        _ = min (μ (C (f.eval a)))
            (μ (X - C a) + μ (f /ₘ (X - C a))) :=
          linear_key_constant_add_mul μ a hμ _ _
        _ = min (ν (C (f.eval a)))
            (ν (X - C a) + ν (f /ₘ (X - C a))) := by rw [hC, hlinear, hquot]
        _ = ν (C (f.eval a) + (X - C a) * (f /ₘ (X - C a))) :=
          (linear_key_constant_add_mul ν a hν _ _).symm
        _ = ν f := congrArg ν hdecomp.symm
  exact AddValuation.ext (fun f => hclaim f.natDegree f rfl)

/-- A genuine linear key gives an actual rational-radius base ball, with
the radius equal to the valuation's own value of that key. -/
theorem eq_baseBall_and_linear_value_of_linear_key
    (v : AddValuation E (WithTop ℚ)) (μ : AddValuation K[X] (WithTop ℚ))
    (hC : ∀ c : K, μ (C c) = v (algebraMap K E c))
    (a : K) (hk : KeyPolynomial μ (X - C a)) :
    ∃ γ : ℚ, μ = baseBall v a γ ∧ μ (X - C a) = (γ : WithTop ℚ) := by
  let γ : ℚ := (μ (X - C a)).untop hk.finite
  have hγ : (γ : WithTop ℚ) = μ (X - C a) := WithTop.coe_untop _ _
  refine ⟨γ, ?_, hγ.symm⟩
  apply linear_key_valuation_ext μ (baseBall v a γ) a hk
    (baseBall_linear_key_of_gauss v a γ)
  · intro c
    exact (hC c).trans (baseBall_C v a c γ).symm
  · simpa only [baseBall_linear_self] using hγ.symm

/-- Every valuation with the specified coefficient valuation and a genuine
linear key is the actual base ball at that key's centre. -/
theorem eq_baseBall_of_linear_key
    (v : AddValuation E (WithTop ℚ)) (μ : AddValuation K[X] (WithTop ℚ))
    (hC : ∀ c : K, μ (C c) = v (algebraMap K E c))
    (a : K) (hk : KeyPolynomial μ (X - C a)) :
    ∃ γ : ℚ, μ = baseBall v a γ := by
  obtain ⟨γ, hball, _⟩ := eq_baseBall_and_linear_value_of_linear_key v μ hC a hk
  exact ⟨γ, hball⟩

/-- The genuine degree-one predicate supplies a linear monic key, hence
the actual monomial normal form. -/
theorem exists_eq_baseBall_of_hasDegree_one
    (v : AddValuation E (WithTop ℚ)) (μ : AddValuation K[X] (WithTop ℚ))
    (hC : ∀ c : K, μ (C c) = v (algebraMap K E c))
    (hdegree : HasDegree μ 1) : ∃ a : K, ∃ γ : ℚ, μ = baseBall v a γ := by
  obtain ⟨φ, hφ, hdeg⟩ := hdegree.1
  have hlinear : φ = X - C (-φ.coeff 0) := by
    rw [hφ.monic.eq_X_add_C hdeg]
    simp
  have hk : KeyPolynomial μ (X - C (-φ.coeff 0)) := hlinear ▸ hφ
  obtain ⟨γ, hγ⟩ := eq_baseBall_of_linear_key v μ hC (-φ.coeff 0) hk
  exact ⟨-φ.coeff 0, γ, hγ⟩

end NTCThird.MLV
