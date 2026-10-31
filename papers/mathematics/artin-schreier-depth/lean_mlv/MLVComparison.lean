import MLVDepth
import OkutsuDepth

/-!
# The polynomial stability step in the depth-one comparison

The monomial valuations in this file are actual additive valuations on E[X].
Their constant and linear values specify the usual Gauss valuation of a ball,
because E is algebraically closed. Existence of such valuations is NOT
asserted here without a construction. The comparison lemmas below use this
explicit interface, and keep that remaining construction visible.

The main arithmetic input is the genuine lower-degree approximation property
already proved equivalent to Okutsu length one in OkutsuDepth.lean.
-/

noncomputable section

open Polynomial

namespace NTCThird.MLV

set_option maxHeartbeats 600000

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- In rational value rank, absence of a best base approximation produces
actual natural-number-indexed cofinal centres and finite rational radii. -/
theorem exists_cofinal_approximation_sequence
    (v : AddValuation E (WithTop ℚ)) (θ : E)
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    ∃ (a : ℕ → K) (γ : ℕ → ℚ),
      (∀ n, (γ n : WithTop ℚ) = v (θ - algebraMap K E (a n))) ∧
      StrictMono γ ∧
      ∀ c : K, ∃ n, v (θ - algebraMap K E c) ≤ (γ n : WithTop ℚ) := by
  classical
  have hfinite (c : K) : v (θ - algebraMap K E c) ≠ ⊤ := by
    obtain ⟨d, hd⟩ := hbetter c
    exact ne_of_lt (hd.trans_le le_top)
  choose value hvalue using
    (fun c : K => WithTop.ne_top_iff_exists.mp (hfinite c))
  let S := {q : ℚ // ∃ c : K, (q : WithTop ℚ) = v (θ - algebraMap K E c)}
  letI : Nonempty S := ⟨⟨value 0, 0, hvalue 0⟩⟩
  letI : NoMaxOrder S := ⟨fun q => by
    obtain ⟨c, hc⟩ := q.property
    obtain ⟨d, hd⟩ := hbetter c
    refine ⟨⟨value d, d, hvalue d⟩, ?_⟩
    change q.val < value d
    apply WithTop.coe_lt_coe.mp
    rw [hc, hvalue d]
    exact hd⟩
  obtain ⟨s, hs, hcof⟩ := exists_strictMono_cofinal_nat (A := S)
  choose a ha using (fun n : ℕ => (s n).property)
  refine ⟨a, fun n => (s n).val, ha, ?_, ?_⟩
  · intro i j hij
    exact hs hij
  · intro c
    obtain ⟨n, hn⟩ := hcof ⟨value c, c, hvalue c⟩
    refine ⟨n, ?_⟩
    rw [← hvalue c]
    exact_mod_cast hn

/-- Actual monomial valuation of the closed ball with centre a and additive
radius γ. On an algebraically closed field, constants and linear factors
determine every polynomial value uniquely. This is an interface to a genuine
valuation, not an arbitrary function asserted to be multiplicative. -/
structure LinearMonomialValuation (v : AddValuation E (WithTop ℚ))
    (a : E) (γ : ℚ) where
  valuation : AddValuation E[X] (WithTop ℚ)
  constant_value : ∀ c : E, valuation (C c) = v c
  linear_value : ∀ b : E, valuation (X - C b) = min (γ : WithTop ℚ) (v (a - b))

theorem valuation_multiset_prod {R : Type*} [CommRing R]
    (μ : AddValuation R (WithTop ℚ)) (s : Multiset R) :
    μ s.prod = (s.map μ).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp [ih]

/-- Agreement on constants and on the roots of one split polynomial suffices
for agreement on that polynomial. -/
theorem valuation_eq_of_linear_factors [IsAlgClosed E]
    (μ ν : AddValuation E[X] (WithTop ℚ)) (f : E[X])
    (hC : ∀ c : E, μ (C c) = ν (C c))
    (hlinear : ∀ b ∈ f.roots, μ (X - C b) = ν (X - C b)) : μ f = ν f := by
  have hfac := (IsAlgClosed.splits f).eq_prod_roots
  rw [hfac, μ.map_mul, ν.map_mul, hC]
  congr 1
  rw [valuation_multiset_prod, valuation_multiset_prod, Multiset.map_map,
    Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl hlinear

theorem valuation_le_of_linear_factors [IsAlgClosed E]
    (μ ν : AddValuation E[X] (WithTop ℚ)) (f : E[X])
    (hC : ∀ c : E, μ (C c) ≤ ν (C c))
    (hlinear : ∀ b ∈ f.roots, μ (X - C b) ≤ ν (X - C b)) : μ f ≤ ν f := by
  have hfac := (IsAlgClosed.splits f).eq_prod_roots
  rw [hfac, μ.map_mul, ν.map_mul]
  apply add_le_add (hC _)
  rw [valuation_multiset_prod, valuation_multiset_prod, Multiset.map_map,
    Multiset.map_map]
  exact Multiset.sum_map_le_sum_map _ _ hlinear

theorem LinearMonomialValuation.ext [IsAlgClosed E]
    {v : AddValuation E (WithTop ℚ)} {a : E} {γ : ℚ}
    (μ ν : LinearMonomialValuation v a γ) : μ.valuation = ν.valuation := by
  apply AddValuation.ext
  intro f
  apply valuation_eq_of_linear_factors
  · intro c
    rw [μ.constant_value, ν.constant_value]
  · intro b _
    rw [μ.linear_value, ν.linear_value]

theorem LinearMonomialValuation.le_evaluation_at_centre [IsAlgClosed E]
    {v : AddValuation E (WithTop ℚ)} {a : E} {γ : ℚ}
    (μ : LinearMonomialValuation v a γ) (f : E[X]) :
    μ.valuation f ≤ v (f.eval a) := by
  let ν : AddValuation E[X] (WithTop ℚ) := v.comap (evalRingHom a)
  change μ.valuation f ≤ ν f
  apply valuation_le_of_linear_factors
  · intro c
    change μ.valuation (C c) ≤ v ((C c).eval a)
    simp [μ.constant_value]
  · intro b _
    change μ.valuation (X - C b) ≤ v ((X - C b).eval a)
    simpa only [μ.linear_value, eval_sub, eval_X, eval_C] using
      (min_le_right (γ : WithTop ℚ) (v (a - b)))

/-- An ultrametric ball has the same truncated distances from every centre
inside the ball. This is the elementary identity behind Gauss-family
monotonicity. -/
theorem min_distance_change_centre (v : AddValuation E (WithTop ℚ))
    (θ a b : E) :
    min (v (θ - a)) (v (a - b)) = min (v (θ - a)) (v (θ - b)) := by
  apply le_antisymm
  · apply le_min (min_le_left _ _)
    have h := v.map_add (θ - a) (a - b)
    simpa only [sub_add_sub_cancel] using h
  · apply le_min (min_le_left _ _)
    have h := v.map_sub (θ - b) (θ - a)
    have heq : θ - b - (θ - a) = a - b := by ring
    rw [heq, min_comm] at h
    exact h

theorem LinearMonomialValuation.linear_value_at_element
    {v : AddValuation E (WithTop ℚ)} {a : E} {γ : ℚ}
    (μ : LinearMonomialValuation v a γ) (θ : E)
    (hγ : (γ : WithTop ℚ) = v (θ - a)) (b : E) :
    μ.valuation (X - C b) = min (γ : WithTop ℚ) (v (θ - b)) := by
  rw [μ.linear_value, hγ, min_distance_change_centre]

/-- The actual monomial valuation has the root-product formula. -/
theorem LinearMonomialValuation.root_formula [IsAlgClosed E]
    {v : AddValuation E (WithTop ℚ)} {a : E} {γ : ℚ}
    (μ : LinearMonomialValuation v a γ) (θ : E)
    (hγ : (γ : WithTop ℚ) = v (θ - a)) (f : E[X]) :
    μ.valuation f = v f.leadingCoeff +
      (f.roots.map (fun b => min (γ : WithTop ℚ) (v (θ - b)))).sum := by
  calc
    μ.valuation f = μ.valuation
        (C f.leadingCoeff * (f.roots.map (fun b => X - C b)).prod) :=
      congrArg μ.valuation ((IsAlgClosed.splits f).eq_prod_roots)
    _ = _ := by
      rw [μ.valuation.map_mul, μ.constant_value, valuation_multiset_prod,
        Multiset.map_map]
      congr 2
      exact Multiset.map_congr rfl (fun b _ => μ.linear_value_at_element θ hγ b)

omit [Field E] in
theorem sum_min_ne_top (s : Multiset E) (γ : ℚ) (d : E → WithTop ℚ) :
    (s.map (fun b => min (γ : WithTop ℚ) (d b))).sum ≠ ⊤ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons b s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, WithTop.add_ne_top]
    exact ⟨ne_of_lt ((min_le_left _ _).trans_lt (WithTop.coe_lt_top γ)), ih⟩

omit [Field E] in
theorem sum_min_strict_of_top_member (s : Multiset E) (d : E → WithTop ℚ)
    (b : E) (hb : b ∈ s) (hdb : d b = ⊤) {γ δ : ℚ} (hγδ : γ < δ) :
    (s.map (fun c => min (γ : WithTop ℚ) (d c))).sum <
      (s.map (fun c => min (δ : WithTop ℚ) (d c))).sum := by
  classical
  rw [← Multiset.cons_erase hb, Multiset.map_cons, Multiset.map_cons,
    Multiset.sum_cons, Multiset.sum_cons, hdb]
  simp only [min_eq_left le_top]
  apply WithTop.add_lt_add_of_lt_of_le (sum_min_ne_top _ _ _)
  · exact_mod_cast hγδ
  · exact Multiset.sum_map_le_sum_map _ _
      (fun c _ => min_le_min (by exact_mod_cast hγδ.le) le_rfl)

/-- Once the ball radius is above the distance from θ to every root of f,
the actual monomial valuation agrees with actual evaluation at θ. -/
theorem LinearMonomialValuation.eq_evaluation_of_roots [IsAlgClosed E]
    {v : AddValuation E (WithTop ℚ)} {a : E} {γ : ℚ}
    (μ : LinearMonomialValuation v a γ) (θ : E)
    (hγ : (γ : WithTop ℚ) = v (θ - a)) (f : E[X])
    (hroots : ∀ b ∈ f.roots, v (θ - b) < (γ : WithTop ℚ)) :
    μ.valuation f = v (f.eval θ) := by
  let ν : AddValuation E[X] (WithTop ℚ) := v.comap (evalRingHom θ)
  change μ.valuation f = ν f
  apply valuation_eq_of_linear_factors
  · intro c
    change μ.valuation (C c) = v ((C c).eval θ)
    simp [μ.constant_value]
  · intro b hb
    change μ.valuation (X - C b) = v ((X - C b).eval θ)
    rw [μ.linear_value_at_element θ hγ]
    simp [min_eq_right (hroots b hb).le]

/-- Every root of a nonzero polynomial has minimal-polynomial degree bounded
by its degree; no separability or choice of conjugate is suppressed. -/
theorem elementDegree_le_of_aroot {f : K[X]} {b : E} (hb : b ∈ f.aroots E) :
    NTCThird.elementDegree K b ≤ f.natDegree := by
  obtain ⟨hf, hb⟩ := mem_aroots.mp hb
  exact natDegree_le_of_dvd (minpoly.dvd K b hb) hf

/-- A strictly improving cofinal family of base approximations eventually
overtakes every member of a fixed finite set of lower-degree elements. -/
theorem eventually_dominates_finite_lower_degree
    {I : Type*} [LinearOrder I] [NoMaxOrder I] [Nonempty I]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (γ : I → ℚ)
    (hincr : StrictMono γ)
    (hcofinal : ∀ c : K, ∃ i, v (θ - algebraMap K E c) ≤ (γ i : WithTop ℚ))
    (happrox : NTCThird.BaseApproximation K v θ)
    (s : Finset E) (hs : ∀ b ∈ s,
      NTCThird.elementDegree K b < NTCThird.elementDegree K θ) :
    ∃ i : I, ∀ j : I, i ≤ j → ∀ b ∈ s, v (θ - b) < (γ j : WithTop ℚ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.choice inferInstance, by simp⟩
  | @insert b s hbs ih =>
    obtain ⟨i, hi⟩ := ih (fun c hc => hs c (Finset.mem_insert_of_mem hc))
    obtain ⟨c, hc⟩ := happrox b (hs b (Finset.mem_insert_self _ _))
    obtain ⟨k, hk⟩ := hcofinal c
    obtain ⟨l, hkl⟩ := exists_gt k
    refine ⟨max i l, ?_⟩
    intro j hj d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · have hlj : l ≤ j := (le_max_right _ _).trans hj
      have hstrict : (γ k : WithTop ℚ) < (γ l : WithTop ℚ) := by
        exact_mod_cast hincr hkl
      have hweak : (γ l : WithTop ℚ) ≤ (γ j : WithTop ℚ) := by
        exact_mod_cast hincr.monotone hlj
      exact ((hc.trans hk).trans_lt hstrict).trans_le hweak
    · exact hi j ((le_max_left _ _).trans hj) d hd

/-- The restriction to K[X] of the actual ball valuation. -/
noncomputable def restrictedMonomial
    {v : AddValuation E (WithTop ℚ)} {a : E} {γ : ℚ}
    (μ : LinearMonomialValuation v a γ) : AddValuation K[X] (WithTop ℚ) :=
  μ.valuation.comap (Polynomial.mapRingHom (algebraMap K E))

@[simp] theorem restrictedMonomial_apply
    {v : AddValuation E (WithTop ℚ)} {a : E} {γ : ℚ}
    (μ : LinearMonomialValuation v a γ) (f : K[X]) :
    restrictedMonomial (K := K) μ f = μ.valuation (f.map (algebraMap K E)) := rfl

/-- The linear key polynomial at each centre is verified against the actual
minimality/primality definition, so the restricted valuation has degree one. -/
theorem restrictedMonomial_hasDegree_one [IsAlgClosed E]
    {v : AddValuation E (WithTop ℚ)} (a : K) (γ : ℚ)
    (μ : LinearMonomialValuation v (algebraMap K E a) γ) :
    HasDegree (restrictedMonomial (K := K) μ) 1 := by
  apply hasDegree_one_of_linear_key _ a
  let vK : AddValuation K (WithTop ℚ) := v.comap (algebraMap K E)
  apply keyPolynomial_linear _ vK a
  · intro c
    change μ.valuation ((C c).map (algebraMap K E)) = v (algebraMap K E c)
    rw [map_C, μ.constant_value]
  · intro f
    change μ.valuation (f.map (algebraMap K E)) ≤ v (algebraMap K E (f.eval a))
    simpa only [eval_map, eval₂_at_apply] using
      μ.le_evaluation_at_centre (f.map (algebraMap K E))
  · change μ.valuation ((X - C a).map (algebraMap K E)) ≠ ⊤
    rw [Polynomial.map_sub, map_X, map_C, μ.linear_value]
    simp

theorem restrictedMonomial_family_le [IsAlgClosed E]
    {I : Type*} [LinearOrder I]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a : I → K) (γ : I → ℚ)
    (hγ : ∀ i, (γ i : WithTop ℚ) = v (θ - algebraMap K E (a i)))
    (hincr : Monotone γ)
    (μ : ∀ i, LinearMonomialValuation v (algebraMap K E (a i)) (γ i))
    {i j : I} (hij : i ≤ j) (f : K[X]) :
    restrictedMonomial (μ i) f ≤ restrictedMonomial (μ j) f := by
  rw [restrictedMonomial_apply, restrictedMonomial_apply]
  apply valuation_le_of_linear_factors
  · intro c
    rw [(μ i).constant_value, (μ j).constant_value]
  · intro b _
    rw [(μ i).linear_value_at_element θ (hγ i), (μ j).linear_value_at_element θ (hγ j)]
    exact min_le_min (by exact_mod_cast hincr hij) le_rfl

/-- Strictness is witnessed by the later centre's linear polynomial. -/
theorem restrictedMonomial_family_strict [IsAlgClosed E]
    {I : Type*} [LinearOrder I]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a : I → K) (γ : I → ℚ)
    (hγ : ∀ i, (γ i : WithTop ℚ) = v (θ - algebraMap K E (a i)))
    (hincr : StrictMono γ)
    (μ : ∀ i, LinearMonomialValuation v (algebraMap K E (a i)) (γ i))
    {i j : I} (hij : i < j) :
    ∃ f : K[X], restrictedMonomial (μ i) f < restrictedMonomial (μ j) f := by
  refine ⟨X - C (a j), ?_⟩
  rw [restrictedMonomial_apply, restrictedMonomial_apply,
    Polynomial.map_sub, map_X, map_C,
    (μ i).linear_value_at_element θ (hγ i),
    (μ j).linear_value_at_element θ (hγ j), ← hγ j, min_self]
  have hlt : (γ i : WithTop ℚ) < (γ j : WithTop ℚ) := by exact_mod_cast hincr hij
  rw [min_eq_left hlt.le]
  exact hlt

/-- Every monic annihilating polynomial is unstable along a strictly
improving family. The root θ supplies one strictly increasing summand; all
other root contributions are monotone and finite. -/
theorem monic_annihilator_unstable [IsAlgClosed E]
    {I : Type*} [LinearOrder I]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a : I → K) (γ : I → ℚ)
    (hγ : ∀ i, (γ i : WithTop ℚ) = v (θ - algebraMap K E (a i)))
    (hincr : StrictMono γ)
    (μ : ∀ i, LinearMonomialValuation v (algebraMap K E (a i)) (γ i))
    (f : K[X]) (hf : f.Monic) (hroot : aeval θ f = 0) :
    Unstable (fun i => restrictedMonomial (K := K) (μ i)) f := by
  intro i j hij
  change restrictedMonomial (μ i) f < restrictedMonomial (μ j) f
  rw [restrictedMonomial_apply, restrictedMonomial_apply,
    (μ i).root_formula θ (hγ i), (μ j).root_formula θ (hγ j)]
  have hmon : (f.map (algebraMap K E)).Monic := hf.map _
  rw [hmon.leadingCoeff, v.map_one, zero_add, zero_add]
  apply sum_min_strict_of_top_member _ (fun b => v (θ - b)) θ
  · exact mem_aroots.mpr ⟨hf.ne_zero, hroot⟩
  · simp
  · exact hincr hij

/-- Polynomial stability below the true algebraic degree follows from the
Okutsu length-one approximation property, for every cofinal monomial family.
This is the substantive stability step in the terminal limit augmentation. -/
theorem stable_evaluation_of_baseApproximation [IsAlgClosed E]
    {I : Type*} [LinearOrder I] [NoMaxOrder I] [Nonempty I]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a : I → K) (γ : I → ℚ)
    (hγ : ∀ i, (γ i : WithTop ℚ) = v (θ - algebraMap K E (a i)))
    (hincr : StrictMono γ)
    (hcofinal : ∀ c : K, ∃ i, v (θ - algebraMap K E c) ≤ (γ i : WithTop ℚ))
    (happrox : NTCThird.BaseApproximation K v θ)
    (μ : ∀ i, LinearMonomialValuation v (algebraMap K E (a i)) (γ i))
    (f : K[X]) (hf : f.natDegree < NTCThird.elementDegree K θ) :
    StableValue (fun i => restrictedMonomial (K := K) (μ i)) f (v (aeval θ f)) := by
  classical
  obtain ⟨i, hi⟩ := eventually_dominates_finite_lower_degree v θ γ hincr
    hcofinal happrox (f.aroots E).toFinset (by
      intro b hb
      exact (elementDegree_le_of_aroot (Multiset.mem_toFinset.mp hb)).trans_lt hf)
  refine ⟨i, ?_⟩
  intro j hj
  rw [restrictedMonomial_apply,
    (μ j).eq_evaluation_of_roots θ (hγ j) (f.map (algebraMap K E))]
  · exact congrArg v (eval_map_algebraMap f θ)
  · intro b hb
    exact hi j hj b (Multiset.mem_toFinset.mpr hb)

/-- The minimal polynomial is a genuine limit key polynomial: it is unstable,
and every strictly smaller-degree polynomial has already become stable. -/
theorem minpoly_limitKey_of_baseApproximation [IsAlgClosed E]
    {I : Type*} [LinearOrder I] [NoMaxOrder I] [Nonempty I]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (hθ : IsIntegral K θ)
    (a : I → K) (γ : I → ℚ)
    (hγ : ∀ i, (γ i : WithTop ℚ) = v (θ - algebraMap K E (a i)))
    (hincr : StrictMono γ)
    (hcofinal : ∀ c : K, ∃ i, v (θ - algebraMap K E c) ≤ (γ i : WithTop ℚ))
    (happrox : NTCThird.BaseApproximation K v θ)
    (μ : ∀ i, LinearMonomialValuation v (algebraMap K E (a i)) (γ i)) :
    LimitKeyPolynomial (fun i => restrictedMonomial (K := K) (μ i)) (minpoly K θ) := by
  refine ⟨minpoly.monic hθ,
    monic_annihilator_unstable v θ a γ hγ hincr μ (minpoly K θ)
      (minpoly.monic hθ) (minpoly.aeval K θ), ?_⟩
  intro f hf
  apply le_of_not_gt
  intro hdeg
  exact not_unstable_of_stableValue
    (stable_evaluation_of_baseApproximation v θ a γ hγ hincr hcofinal happrox μ f hdeg) hf

/-- The terminal limit augmentation at infinity, including its actual
evaluation valuation and exact remainder formula. This is a terminal step,
not yet a theorem about full chain existence or intrinsic MLV depth. -/
theorem terminal_limit_of_baseApproximation [IsAlgClosed E]
    {I : Type*} [LinearOrder I] [NoMaxOrder I] [Nonempty I]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (hθ : IsIntegral K θ)
    (a : I → K) (γ : I → ℚ)
    (hγ : ∀ i, (γ i : WithTop ℚ) = v (θ - algebraMap K E (a i)))
    (hincr : StrictMono γ)
    (hcofinal : ∀ c : K, ∃ i, v (θ - algebraMap K E c) ≤ (γ i : WithTop ℚ))
    (happrox : NTCThird.BaseApproximation K v θ)
    (μ : ∀ i, LinearMonomialValuation v (algebraMap K E (a i)) (γ i)) :
    LimitAtInfinity (fun i => restrictedMonomial (K := K) (μ i))
      (evaluationValuation v θ) (minpoly K θ) := by
  apply limitAtInfinity_of_stable_evaluation
    (fun i => restrictedMonomial (K := K) (μ i)) v θ (minpoly K θ)
    (minpoly_limitKey_of_baseApproximation v θ hθ a γ hγ hincr hcofinal happrox μ)
    (minpoly.ne_one K θ) (minpoly.aeval K θ)
  intro f hf
  exact stable_evaluation_of_baseApproximation v θ a γ hγ hincr hcofinal happrox μ f hf

end NTCThird.MLV
