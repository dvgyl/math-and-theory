import MLVComparison

/-!
# Rational additive Gauss valuations

The value is the finite minimum of the weighted coefficient values. Its
multiplicativity is proved by the least minimizing coefficient in each
factor. Taylor translation then gives the actual monomial valuations used by
the MLV comparison. These are standard constructions, with no novelty claim.
-/

noncomputable section

open Polynomial

namespace NTCThird.MLV

set_option maxHeartbeats 800000

variable {K : Type*} [Field K]

noncomputable def weightedCoefficient (v : AddValuation K (WithTop ℚ)) (γ : ℚ)
    (f : K[X]) (i : ℕ) : WithTop ℚ :=
  v (f.coeff i) + (((i : ℚ) * γ : ℚ) : WithTop ℚ)

noncomputable def gaussValue (v : AddValuation K (WithTop ℚ)) (γ : ℚ) (f : K[X]) : WithTop ℚ :=
  f.support.inf (weightedCoefficient v γ f)

@[simp] theorem gaussValue_zero (v : AddValuation K (WithTop ℚ)) (γ : ℚ) :
    gaussValue v γ (0 : K[X]) = ⊤ := by simp [gaussValue]

@[simp] theorem gaussValue_C (v : AddValuation K (WithTop ℚ)) (γ : ℚ) (c : K) :
    gaussValue v γ (C c) = v c := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  · simp [gaussValue, support_C, hc, weightedCoefficient]

theorem gaussValue_le_coefficient (v : AddValuation K (WithTop ℚ)) (γ : ℚ)
    (f : K[X]) (i : ℕ) : gaussValue v γ f ≤ weightedCoefficient v γ f i := by
  classical
  by_cases hi : i ∈ f.support
  · exact Finset.inf_le hi
  · have hcoeff : f.coeff i = 0 := notMem_support_iff.mp hi
    simp [weightedCoefficient, hcoeff]

@[simp] theorem gaussValue_eq_top_iff (v : AddValuation K (WithTop ℚ)) (γ : ℚ)
    (f : K[X]) : gaussValue v γ f = ⊤ ↔ f = 0 := by
  constructor
  · intro h
    ext i
    have hi := gaussValue_le_coefficient v γ f i
    rw [h] at hi
    have ht : weightedCoefficient v γ f i = ⊤ := top_le_iff.mp hi
    have hz : v (f.coeff i) = ⊤ :=
      (WithTop.add_eq_top.mp ht).resolve_right WithTop.coe_ne_top
    exact v.top_iff.mp hz
  · rintro rfl
    exact gaussValue_zero v γ

theorem gaussValue_add (v : AddValuation K (WithTop ℚ)) (γ : ℚ) (f g : K[X]) :
    min (gaussValue v γ f) (gaussValue v γ g) ≤ gaussValue v γ (f + g) := by
  apply Finset.le_inf
  intro i _
  calc
    min (gaussValue v γ f) (gaussValue v γ g) ≤
        min (weightedCoefficient v γ f i) (weightedCoefficient v γ g i) :=
      min_le_min (gaussValue_le_coefficient v γ f i) (gaussValue_le_coefficient v γ g i)
    _ = min (v (f.coeff i)) (v (g.coeff i)) + (((i : ℚ) * γ : ℚ) : WithTop ℚ) := by
      simp only [weightedCoefficient, min_add_add_right]
    _ ≤ weightedCoefficient v γ (f + g) i := by
      simpa only [weightedCoefficient, coeff_add] using
        add_le_add (v.map_add (f.coeff i) (g.coeff i))
          (le_refl ((((i : ℚ) * γ : ℚ) : WithTop ℚ)))

theorem shifted_valuation_sum_le {A : Type*}
    (v : AddValuation K (WithTop ℚ)) (s : Finset A) (f : A → K) (δ : ℚ)
    (c : WithTop ℚ) (h : ∀ i ∈ s, c ≤ v (f i) + (δ : WithTop ℚ)) :
    c ≤ v (∑ i ∈ s, f i) + (δ : WithTop ℚ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have ha := h a (Finset.mem_insert_self _ _)
    have hs := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert has]
    calc
      c ≤ min (v (f a) + (δ : WithTop ℚ)) (v (∑ i ∈ s, f i) + (δ : WithTop ℚ)) :=
        le_min ha hs
      _ = min (v (f a)) (v (∑ i ∈ s, f i)) + (δ : WithTop ℚ) := by
        rw [min_add_add_right]
      _ ≤ v (f a + ∑ i ∈ s, f i) + (δ : WithTop ℚ) :=
        add_le_add (v.map_add _ _) le_rfl

theorem weighted_product_term (v : AddValuation K (WithTop ℚ)) (γ : ℚ)
    (f g : K[X]) (i j : ℕ) :
    v (f.coeff i * g.coeff j) + ((((i + j : ℕ) : ℚ) * γ : ℚ) : WithTop ℚ) =
      weightedCoefficient v γ f i + weightedCoefficient v γ g j := by
  simp only [weightedCoefficient, v.map_mul, Nat.cast_add, add_mul, WithTop.coe_add]
  exact add_add_add_comm _ _ _ _

theorem gaussValue_mul_ge (v : AddValuation K (WithTop ℚ)) (γ : ℚ) (f g : K[X]) :
    gaussValue v γ f + gaussValue v γ g ≤ gaussValue v γ (f * g) := by
  apply Finset.le_inf
  intro n _
  unfold weightedCoefficient
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply shifted_valuation_sum_le
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have heq : i + (n - i) = n := Nat.add_sub_of_le hin
  calc
    gaussValue v γ f + gaussValue v γ g ≤
        weightedCoefficient v γ f i + weightedCoefficient v γ g (n - i) :=
      add_le_add (gaussValue_le_coefficient v γ f i) (gaussValue_le_coefficient v γ g _)
    _ = v (f.coeff i * g.coeff (n - i)) + (((n : ℚ) * γ : ℚ) : WithTop ℚ) := by
      rw [← weighted_product_term, heq]

theorem exists_minimal_gauss_coefficient
    (v : AddValuation K (WithTop ℚ)) (γ : ℚ) (f : K[X]) (hf : f ≠ 0) :
    ∃ i : ℕ, gaussValue v γ f = weightedCoefficient v γ f i ∧
      ∀ j : ℕ, j < i → gaussValue v γ f < weightedCoefficient v γ f j := by
  classical
  have hex : ∃ i : ℕ, gaussValue v γ f = weightedCoefficient v γ f i := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf f.support (support_nonempty.mpr hf)
      (weightedCoefficient v γ f)
    exact ⟨i, hi⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro j hj
  have hle := gaussValue_le_coefficient v γ f j
  by_contra hnot
  have heq := le_antisymm hle (le_of_not_gt hnot)
  have hmin : Nat.find hex ≤ j := Nat.find_min' hex heq
  omega

theorem gaussValue_mul (v : AddValuation K (WithTop ℚ)) (γ : ℚ) (f g : K[X]) :
    gaussValue v γ (f * g) = gaussValue v γ f + gaussValue v γ g := by
  classical
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  have hff : gaussValue v γ f ≠ ⊤ := by simpa using hf
  have hgf : gaussValue v γ g ≠ ⊤ := by simpa using hg
  obtain ⟨i, hi, hilt⟩ := exists_minimal_gauss_coefficient v γ f hf
  obtain ⟨j, hj, hjlt⟩ := exists_minimal_gauss_coefficient v γ g hg
  have hterm : v (f.coeff i * g.coeff j) ≠ ⊤ := by
    have hsum : weightedCoefficient v γ f i + weightedCoefficient v γ g j ≠ ⊤ := by
      rw [← hi, ← hj, WithTop.add_ne_top]
      exact ⟨hff, hgf⟩
    rw [← weighted_product_term, WithTop.add_ne_top] at hsum
    exact hsum.1
  have hunique : ∀ k ∈ Finset.range (i + j + 1), k ≠ i →
      v (f.coeff i * g.coeff j) < v (f.coeff k * g.coeff (i + j - k)) := by
    intro k hk hki
    have hkn : k ≤ i + j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsumk : k + (i + j - k) = i + j := Nat.add_sub_of_le hkn
    apply (WithTop.add_lt_add_iff_right
      (show ((((i + j : ℕ) : ℚ) * γ : ℚ) : WithTop ℚ) ≠ ⊤ from WithTop.coe_ne_top)).mp
    have hother : v (f.coeff k * g.coeff (i + j - k)) +
        ((((i + j : ℕ) : ℚ) * γ : ℚ) : WithTop ℚ) =
        weightedCoefficient v γ f k + weightedCoefficient v γ g (i + j - k) := by
      simpa only [hsumk] using weighted_product_term v γ f g k (i + j - k)
    rw [weighted_product_term]
    rw [hother]
    rw [← hi, ← hj]
    rcases lt_or_gt_of_ne hki with hki | hik
    · exact WithTop.add_lt_add_of_lt_of_le hgf (hilt k hki)
        (gaussValue_le_coefficient v γ g _)
    · have hltj : i + j - k < j := by omega
      exact WithTop.add_lt_add_of_le_of_lt hff (gaussValue_le_coefficient v γ f k)
        (hjlt _ hltj)
  have hsum : v (∑ k ∈ Finset.range (i + j + 1),
      f.coeff k * g.coeff (i + j - k)) = v (f.coeff i * g.coeff j) := by
    have hi_range : i ∈ Finset.range (i + j + 1) := by simp
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hi_range]
    simp only [Nat.add_sub_cancel_left]
    apply v.map_add_eq_of_lt_left
    apply v.map_lt_sum hterm
    intro k hk
    obtain ⟨hk, hki⟩ := Finset.mem_sdiff.mp hk
    exact hunique k hk (by simpa using hki)
  apply le_antisymm _ (gaussValue_mul_ge v γ f g)
  calc
    gaussValue v γ (f * g) ≤ weightedCoefficient v γ (f * g) (i + j) :=
      gaussValue_le_coefficient v γ (f * g) (i + j)
    _ = gaussValue v γ f + gaussValue v γ g := by
      unfold weightedCoefficient
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hsum,
        weighted_product_term, ← hi, ← hj]

/-- The Gauss construction is an actual additive valuation. -/
noncomputable def gaussValuation (v : AddValuation K (WithTop ℚ)) (γ : ℚ) :
    AddValuation K[X] (WithTop ℚ) :=
  AddValuation.of (gaussValue v γ) (gaussValue_zero v γ)
    (by simpa using gaussValue_C v γ 1) (gaussValue_add v γ) (gaussValue_mul v γ)

@[simp] theorem gaussValuation_apply (v : AddValuation K (WithTop ℚ)) (γ : ℚ)
    (f : K[X]) : gaussValuation v γ f = gaussValue v γ f := rfl

theorem gaussValue_X_sub_C (v : AddValuation K (WithTop ℚ)) (γ : ℚ) (b : K) :
    gaussValue v γ (X - C b) = min (γ : WithTop ℚ) (v b) := by
  apply le_antisymm
  · apply le_min
    · calc
        gaussValue v γ (X - C b) ≤ weightedCoefficient v γ (X - C b) 1 :=
          gaussValue_le_coefficient v γ (X - C b) 1
        _ = (γ : WithTop ℚ) := by simp [weightedCoefficient, coeff_sub]
    · calc
        gaussValue v γ (X - C b) ≤ weightedCoefficient v γ (X - C b) 0 :=
          gaussValue_le_coefficient v γ (X - C b) 0
        _ = v b := by simp [weightedCoefficient, coeff_sub]
  · apply Finset.le_inf
    intro i _
    by_cases hi0 : i = 0
    · subst i
      simpa [weightedCoefficient] using (min_le_right (γ : WithTop ℚ) (v b))
    by_cases hi1 : i = 1
    · subst i
      simpa [weightedCoefficient] using (min_le_left (γ : WithTop ℚ) (v b))
    · simp [weightedCoefficient, coeff_sub, coeff_X, coeff_C, hi0, hi1, Ne.symm hi1]

/-- The actual monomial valuation at any centre and rational radius. -/
noncomputable def linearMonomialValuation (v : AddValuation K (WithTop ℚ)) (a : K) (γ : ℚ) :
    LinearMonomialValuation v a γ where
  valuation := (gaussValuation v γ).comap (taylorAlgHom a).toRingHom
  constant_value := by
    intro c
    change gaussValue v γ (taylor a (C c)) = v c
    rw [taylor_C, gaussValue_C]
  linear_value := by
    intro b
    change gaussValue v γ (taylor a (X - C b)) = min (γ : WithTop ℚ) (v (a - b))
    rw [map_sub, taylor_X, taylor_C]
    have h : X + C a - C b = (X - C (b - a) : K[X]) := by rw [C_sub]; ring
    rw [h, gaussValue_X_sub_C, v.map_sub_swap b a]

section TerminalFamily

variable {E : Type*} [Field E] [Algebra K E] [IsAlgClosed E]

/-- Actual degree-one polynomial valuations, ordered strictly and terminating
at the evaluation valuation by a minimal-unstable-polynomial limit step.

This theorem proves a substantial portion of the MLV construction. It does
not yet prove that successive family members are ordinary augmentations in
the full expansion-formula sense, nor the reverse comparison or chain-length
invariance. Consequently it is not named or advertised as an MLV depth
theorem. -/
theorem exists_degreeOne_terminal_limit
    (v : AddValuation E (WithTop ℚ)) (θ : E) (hθ : IsIntegral K θ)
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d))
    (happrox : NTCThird.BaseApproximation K v θ) :
    ∃ ρ : ℕ → AddValuation K[X] (WithTop ℚ),
      (∀ i, HasDegree (ρ i) 1) ∧
      (∀ i j, i ≤ j → ∀ f : K[X], ρ i f ≤ ρ j f) ∧
      (∀ i j, i < j → ∃ f : K[X], ρ i f < ρ j f) ∧
      LimitAtInfinity ρ (evaluationValuation v θ) (minpoly K θ) := by
  obtain ⟨a, γ, hγ, hincr, hcofinal⟩ := exists_cofinal_approximation_sequence v θ hbetter
  let μ : ∀ i, LinearMonomialValuation v (algebraMap K E (a i)) (γ i) :=
    fun i => linearMonomialValuation v (algebraMap K E (a i)) (γ i)
  refine ⟨fun i => restrictedMonomial (K := K) (μ i), ?_, ?_, ?_, ?_⟩
  · intro i
    exact restrictedMonomial_hasDegree_one (a i) (γ i) (μ i)
  · intro i j hij f
    exact restrictedMonomial_family_le v θ a γ hγ hincr.monotone μ hij f
  · intro i j hij
    exact restrictedMonomial_family_strict v θ a γ hγ hincr μ hij
  · exact terminal_limit_of_baseApproximation v θ hθ a γ hγ hincr hcofinal happrox μ

end TerminalFamily

end NTCThird.MLV
