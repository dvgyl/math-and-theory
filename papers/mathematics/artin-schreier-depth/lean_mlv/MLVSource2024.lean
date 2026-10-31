import MLVIntrinsic

/-!
# Degree-one families in the 2024 presentation

These elementary ball lemmas are used by the separate length-one
correspondence module.  In particular, eventual stability is proved from
strictly increasing degree-one valuations; it is not added as a premise to
the source-side continuous-family record.

The seven original MLV modules are unchanged.
-/

noncomputable section

open Polynomial

namespace NTCThird.MLV

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

set_option maxHeartbeats 1000000

theorem min_distance_change_centre_of_le
    (v : AddValuation E (WithTop ℚ)) (θ a b : E) (γ : WithTop ℚ)
    (hγ : γ ≤ v (θ - a)) :
    min γ (v (a - b)) = min γ (v (θ - b)) := by
  calc
    min γ (v (a - b)) = min (min γ (v (θ - a))) (v (a - b)) := by
      rw [min_eq_left hγ]
    _ = min γ (min (v (θ - a)) (v (a - b))) := min_assoc _ _ _
    _ = min γ (min (v (θ - a)) (v (θ - b))) := by
      rw [min_distance_change_centre]
    _ = min γ (v (θ - b)) := by rw [← min_assoc, min_eq_left hγ]

theorem LinearMonomialValuation.linear_value_at_element_of_le
    {v : AddValuation E (WithTop ℚ)} {a : E} {γ : ℚ}
    (μ : LinearMonomialValuation v a γ) (θ : E)
    (hγ : (γ : WithTop ℚ) ≤ v (θ - a)) (b : E) :
    μ.valuation (X - C b) = min (γ : WithTop ℚ) (v (θ - b)) := by
  rw [μ.linear_value, min_distance_change_centre_of_le v θ a b _ hγ]

theorem LinearMonomialValuation.root_formula_of_le [IsAlgClosed E]
    {v : AddValuation E (WithTop ℚ)} {a : E} {γ : ℚ}
    (μ : LinearMonomialValuation v a γ) (θ : E)
    (hγ : (γ : WithTop ℚ) ≤ v (θ - a)) (f : E[X]) :
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
      exact Multiset.map_congr rfl (fun b _ => μ.linear_value_at_element_of_le θ hγ b)

theorem evaluation_root_formula [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (f : E[X]) :
    v (f.eval θ) = v f.leadingCoeff +
      (f.roots.map (fun b => v (θ - b))).sum := by
  let ν : AddValuation E[X] (WithTop ℚ) := v.comap (evalRingHom θ)
  change ν f = _
  conv_lhs => rw [(IsAlgClosed.splits f).eq_prod_roots]
  rw [ν.map_mul, valuation_multiset_prod, Multiset.map_map]
  change v ((C f.leadingCoeff).eval θ) +
    (f.roots.map (fun b => v ((X - C b).eval θ))).sum = _
  simp

theorem baseBall_radius_le_of_le
    (v : AddValuation E (WithTop ℚ)) (a b : K) (γ δ : ℚ)
    (hle : ∀ f : K[X], baseBall v a γ f ≤ baseBall v b δ f) : γ ≤ δ := by
  have h := hle (X - C a)
  rw [baseBall_linear_self, baseBall_linear] at h
  exact WithTop.coe_le_coe.mp (h.trans (min_le_left _ _))

theorem baseBall_centre_le_of_le
    (v : AddValuation E (WithTop ℚ)) (a b : K) (γ δ : ℚ)
    (hle : ∀ f : K[X], baseBall v a γ f ≤ baseBall v b δ f) :
    (γ : WithTop ℚ) ≤ v (algebraMap K E a - algebraMap K E b) := by
  have h := hle (X - C a)
  rw [baseBall_linear_self, baseBall_linear, v.map_sub_swap] at h
  exact h.trans (min_le_right _ _)

theorem baseBall_le_of_radius_centre [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ)) (a b : K) (γ δ : ℚ)
    (hγδ : γ ≤ δ)
    (hab : (γ : WithTop ℚ) ≤ v (algebraMap K E b - algebraMap K E a))
    (f : K[X]) : baseBall v a γ f ≤ baseBall v b δ f := by
  change (linearMonomialValuation v (algebraMap K E a) γ).valuation
      (f.map (algebraMap K E)) ≤
    (linearMonomialValuation v (algebraMap K E b) δ).valuation
      (f.map (algebraMap K E))
  apply valuation_le_of_linear_factors
  · intro c
    rw [(linearMonomialValuation v (algebraMap K E a) γ).constant_value,
      (linearMonomialValuation v (algebraMap K E b) δ).constant_value]
  · intro c _
    rw [(linearMonomialValuation v (algebraMap K E a) γ).linear_value_at_element_of_le
        (algebraMap K E b) hab,
      (linearMonomialValuation v (algebraMap K E b) δ).linear_value]
    exact min_le_min (by exact_mod_cast hγδ) le_rfl

theorem baseBall_radius_lt_of_lt [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ)) (a b : K) (γ δ : ℚ)
    (hle : ∀ f : K[X], baseBall v a γ f ≤ baseBall v b δ f)
    (hlt : ∃ f : K[X], baseBall v a γ f < baseBall v b δ f) : γ < δ := by
  have hγδ := baseBall_radius_le_of_le v a b γ δ hle
  apply lt_of_le_of_ne hγδ
  intro heq
  subst δ
  have hab := baseBall_centre_le_of_le v a b γ γ hle
  obtain ⟨f, hf⟩ := hlt
  exact (not_lt_of_ge (baseBall_le_of_radius_centre v b a γ γ le_rfl hab f)) hf

theorem baseBall_le_evaluation_of_radius_le [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a : K) (γ : ℚ)
    (hγ : (γ : WithTop ℚ) ≤ v (θ - algebraMap K E a)) (f : K[X]) :
    baseBall v a γ f ≤ evaluationValuation v θ f := by
  let ν : AddValuation E[X] (WithTop ℚ) := v.comap (evalRingHom θ)
  change (linearMonomialValuation v (algebraMap K E a) γ).valuation
    (f.map (algebraMap K E)) ≤ v (aeval θ f)
  rw [← eval_map_algebraMap]
  change (linearMonomialValuation v (algebraMap K E a) γ).valuation
    (f.map (algebraMap K E)) ≤ ν (f.map (algebraMap K E))
  apply valuation_le_of_linear_factors
  · intro c
    change (linearMonomialValuation v (algebraMap K E a) γ).valuation (C c) ≤
      v ((C c).eval θ)
    simp [(linearMonomialValuation v (algebraMap K E a) γ).constant_value]
  · intro b _
    change (linearMonomialValuation v (algebraMap K E a) γ).valuation (X - C b) ≤
      v ((X - C b).eval θ)
    rw [(linearMonomialValuation v (algebraMap K E a) γ).linear_value_at_element_of_le
      θ hγ]
    simpa using min_le_right (γ : WithTop ℚ) (v (θ - b))

omit [Field E] in
theorem sum_min_strict_of_cutoff_member (s : Multiset E) (d : E → WithTop ℚ)
    (b : E) (hb : b ∈ s) {γ δ : ℚ} (hγδ : γ < δ)
    (hdb : (γ : WithTop ℚ) < d b) :
    (s.map (fun c => min (γ : WithTop ℚ) (d c))).sum <
      (s.map (fun c => min (δ : WithTop ℚ) (d c))).sum := by
  classical
  rw [← Multiset.cons_erase hb, Multiset.map_cons, Multiset.map_cons,
    Multiset.sum_cons, Multiset.sum_cons, min_eq_left hdb.le]
  apply WithTop.add_lt_add_of_lt_of_le (sum_min_ne_top _ _ _)
  · exact lt_min (by exact_mod_cast hγδ) hdb
  · exact Multiset.sum_map_le_sum_map _ _
      (fun c _ => min_le_min (by exact_mod_cast hγδ.le) le_rfl)

omit [Field E] in
theorem sum_min_lt_sum_of_cutoff_member (s : Multiset E) (d : E → WithTop ℚ)
    (b : E) (hb : b ∈ s) (γ : ℚ) (hdb : (γ : WithTop ℚ) < d b) :
    (s.map (fun c => min (γ : WithTop ℚ) (d c))).sum < (s.map d).sum := by
  classical
  rw [← Multiset.cons_erase hb, Multiset.map_cons, Multiset.map_cons,
    Multiset.sum_cons, Multiset.sum_cons, min_eq_left hdb.le]
  apply WithTop.add_lt_add_of_lt_of_le (sum_min_ne_top _ _ _) hdb
  exact Multiset.sum_map_le_sum_map _ _ (fun c _ => min_le_right _ _)

theorem baseBall_lt_evaluation_of_root [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a : K) (γ : ℚ)
    (hγ : (γ : WithTop ℚ) ≤ v (θ - algebraMap K E a))
    (f : K[X]) (hf : f ≠ 0) (b : E) (hb : b ∈ f.aroots E)
    (hdb : (γ : WithTop ℚ) < v (θ - b)) :
    baseBall v a γ f < evaluationValuation v θ f := by
  change (linearMonomialValuation v (algebraMap K E a) γ).valuation
    (f.map (algebraMap K E)) < v (aeval θ f)
  rw [(linearMonomialValuation v (algebraMap K E a) γ).root_formula_of_le θ hγ,
    ← eval_map_algebraMap, evaluation_root_formula]
  apply WithTop.add_lt_add_left
    (v.ne_top_iff.mpr (leadingCoeff_ne_zero.mpr (map_ne_zero hf)))
  exact sum_min_lt_sum_of_cutoff_member _ (fun c => v (θ - c)) b hb γ hdb

theorem baseBall_lt_of_root_above_earlier_radius [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ)) (a b : K) (γ δ : ℚ)
    (hγδ : γ < δ)
    (hab : (γ : WithTop ℚ) ≤ v (algebraMap K E b - algebraMap K E a))
    (f : K[X]) (hf : f ≠ 0) (c : E) (hc : c ∈ f.aroots E)
    (hdc : (γ : WithTop ℚ) < v (algebraMap K E b - c)) :
    baseBall v a γ f < baseBall v b δ f := by
  change (linearMonomialValuation v (algebraMap K E a) γ).valuation
      (f.map (algebraMap K E)) <
    (linearMonomialValuation v (algebraMap K E b) δ).valuation
      (f.map (algebraMap K E))
  rw [(linearMonomialValuation v (algebraMap K E a) γ).root_formula_of_le
      (algebraMap K E b) hab,
    (linearMonomialValuation v (algebraMap K E b) δ).root_formula_of_le
      (algebraMap K E b) (by simp)]
  apply WithTop.add_lt_add_left
    (v.ne_top_iff.mpr (leadingCoeff_ne_zero.mpr (map_ne_zero hf)))
  exact sum_min_strict_of_cutoff_member _ (fun d => v (algebraMap K E b - d))
    c hc hγδ hdc

theorem LinearMonomialValuation.eq_evaluation_of_roots_outside [IsAlgClosed E]
    {v : AddValuation E (WithTop ℚ)} {a : E} {γ : ℚ}
    (μ : LinearMonomialValuation v a γ) (θ : E) (f : E[X])
    (hroots : ∀ b ∈ f.roots,
      v (θ - b) < (γ : WithTop ℚ) ∧ v (θ - b) < v (θ - a)) :
    μ.valuation f = v (f.eval θ) := by
  let ν : AddValuation E[X] (WithTop ℚ) := v.comap (evalRingHom θ)
  change μ.valuation f = ν f
  apply valuation_eq_of_linear_factors
  · intro c
    change μ.valuation (C c) = v ((C c).eval θ)
    simp [μ.constant_value]
  · intro b hb
    obtain ⟨hγ, ha⟩ := hroots b hb
    have hdiff : v (a - b) = v (θ - b) := by
      convert v.map_sub_eq_of_lt_left ha using 1
      congr 1
      ring
    change μ.valuation (X - C b) = v ((X - C b).eval θ)
    rw [μ.linear_value, hdiff, min_eq_right hγ.le]
    simp

/-- For nested balls of strictly increasing radii, a failure of strict
increase on a polynomial forces an eventually constant value. No no-maximal
index or well-order assumption is used. -/
theorem baseBall_family_stable_of_not_unstable [IsAlgClosed E]
    {I : Type*} [LinearOrder I] [Nonempty I]
    (v : AddValuation E (WithTop ℚ)) (a : I → K) (γ : I → ℚ)
    (hincr : StrictMono γ)
    (hnest : ∀ i j, i ≤ j →
      (γ i : WithTop ℚ) ≤ v (algebraMap K E (a j) - algebraMap K E (a i)))
    (f : K[X]) (hu : ¬Unstable (fun i => baseBall v (a i) (γ i)) f) :
    ∃ δ : WithTop ℚ, StableValue (fun i => baseBall v (a i) (γ i)) f δ := by
  classical
  by_cases hf : f = 0
  · subst f
    exact ⟨⊤, Classical.arbitrary I, by simp⟩
  change ¬(∀ ⦃i j : I⦄, i < j →
    baseBall v (a i) (γ i) f < baseBall v (a j) (γ j) f) at hu
  push_neg at hu
  obtain ⟨i, j, hij, hnot⟩ := hu
  have hroots : ∀ b ∈ f.aroots E,
      v (algebraMap K E (a j) - b) ≤ (γ i : WithTop ℚ) := by
    intro b hb
    by_contra hn
    have hlt := lt_of_not_ge hn
    exact (not_lt_of_ge hnot) (baseBall_lt_of_root_above_earlier_radius v
      (a i) (a j) (γ i) (γ j) (hincr hij) (hnest i j hij.le) f hf b hb hlt)
  refine ⟨v (algebraMap K E (f.eval (a j))), j, ?_⟩
  intro k hjk
  change (linearMonomialValuation v (algebraMap K E (a k)) (γ k)).valuation
    (f.map (algebraMap K E)) = _
  rw [(linearMonomialValuation v (algebraMap K E (a k)) (γ k)).eq_evaluation_of_roots_outside
    (algebraMap K E (a j)) (f.map (algebraMap K E))]
  · simp only [eval_map, eval₂_at_apply]
  · intro b hb
    have hd : v (algebraMap K E (a j) - b) < (γ j : WithTop ℚ) :=
      (hroots b hb).trans_lt (by exact_mod_cast hincr hij)
    refine ⟨hd.trans_le (by exact_mod_cast hincr.monotone hjk), ?_⟩
    have hcentre := hnest j k hjk
    rw [v.map_sub_swap (algebraMap K E (a k)) (algebraMap K E (a j))] at hcentre
    exact hd.trans_le hcentre

/-- Constants cannot lie in a tangent direction between valuations with the
same restriction to the base field. -/
theorem positive_degree_of_strict_increase
    {μ ν : AddValuation K[X] (WithTop ℚ)}
    (hC : ∀ c : K, μ (C c) = ν (C c))
    (f : K[X]) (hf : μ f < ν f) : 0 < f.natDegree := by
  by_contra hn
  have hzero : f.natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero hzero, hC] at hf
  exact lt_irrefl _ hf

/-- In the length-one situation, a better base approximation supplies an
actual degree-one tangent polynomial. This verifies the degree appearing in
Nart (2021), Definition 4.1, rather than identifying it by convention. -/
theorem exists_tangentDirection_baseBall
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a : K) (γ : ℚ)
    (hγ : (γ : WithTop ℚ) = v (θ - algebraMap K E a))
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    ∃ b : K, TangentDirection (baseBall v a γ) (evaluationValuation v θ) (X - C b) := by
  obtain ⟨b, hb⟩ := hbetter a
  have hlt : (γ : WithTop ℚ) < v (θ - algebraMap K E b) := by rwa [hγ]
  refine ⟨b, monic_X_sub_C b, ?_, ?_⟩
  · rw [baseBall_linear_at_element v θ a b γ hγ, min_eq_left hlt.le]
    simpa using hlt
  · intro f _ hf
    rw [natDegree_X_sub_C]
    exact positive_degree_of_strict_increase
      (fun c => by simp) f hf

theorem tangentDirection_baseBall_degree_one
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a : K) (γ : ℚ)
    (hγ : (γ : WithTop ℚ) = v (θ - algebraMap K E a))
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d))
    (f : K[X]) (hf : TangentDirection (baseBall v a γ) (evaluationValuation v θ) f) :
    f.natDegree = 1 := by
  obtain ⟨b, hb⟩ := exists_tangentDirection_baseBall v θ a γ hγ hbetter
  have hupper := hf.2.2 (X - C b) hb.1 hb.2.1
  rw [natDegree_X_sub_C] at hupper
  have hC : ∀ c : K,
      baseBall v a γ (C c) = evaluationValuation v θ (C c) := by
    intro c
    simp
  have hlower := positive_degree_of_strict_increase hC f hf.2.1
  omega

/-- Every formal length-one chain under the no-best-approximation hypothesis
has a genuine degree-one tangent direction, and every member of that
direction has degree one. Thus its limit-family stable degree agrees with
the degree of the tangent direction in the 2021 definition. -/
theorem finiteMLVChain_one_tangent_degree
    (v : AddValuation E (WithTop ℚ)) (θ : E)
    (C : FiniteMLVChain (v.comap (algebraMap K E))
      (evaluationValuation v θ) (minpoly K θ) 1)
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    (∃ f : K[X], TangentDirection (C.valuation 0) (C.valuation 1) f) ∧
      ∀ f : K[X], TangentDirection (C.valuation 0) (C.valuation 1) f → f.natDegree = 1 := by
  have hν : C.valuation 1 = evaluationValuation v θ := C.terminal_valuation
  have hγ : C.value 0 = v (θ - algebraMap K E C.initial_center) := by
    have h := C.endpoint_values (0 : Fin 1)
    change evaluationValuation v θ (C.polynomial 0) = C.value 0 at h
    rw [C.initial_polynomial] at h
    simpa using h.symm
  obtain ⟨b, hb⟩ := hbetter C.initial_center
  have hfinite : C.value 0 ≠ ⊤ := by
    rw [hγ]
    exact ne_of_lt (hb.trans_le le_top)
  obtain ⟨γ, hco⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hμ : C.valuation 0 = baseBall v C.initial_center γ := by
    apply InitialMonomial.ext (γ := (γ : WithTop ℚ))
    · rw [hco]
      exact C.initial_formula
    · exact baseBall_initial v C.initial_center γ
  rw [hμ, hν]
  have hγ' := hco.trans hγ
  obtain ⟨c, hc⟩ := exists_tangentDirection_baseBall v θ C.initial_center γ hγ' hbetter
  exact ⟨⟨X - Polynomial.C c, hc⟩,
    tangentDirection_baseBall_degree_one v θ C.initial_center γ hγ' hbetter⟩

/-- The tangent direction in the previous theorem is taken between
pointwise comparable valuations, with a strict witness. -/
theorem finiteMLVChain_one_strict_endpoint [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ)) (θ : E)
    (C : FiniteMLVChain (v.comap (algebraMap K E))
      (evaluationValuation v θ) (minpoly K θ) 1)
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    (∀ f : K[X], C.valuation 0 f ≤ C.valuation 1 f) ∧
      ∃ f : K[X], C.valuation 0 f < C.valuation 1 f := by
  have hν : C.valuation 1 = evaluationValuation v θ := C.terminal_valuation
  have hγ : C.value 0 = v (θ - algebraMap K E C.initial_center) := by
    have h := C.endpoint_values (0 : Fin 1)
    change evaluationValuation v θ (C.polynomial 0) = C.value 0 at h
    rw [C.initial_polynomial] at h
    simpa using h.symm
  obtain ⟨b, hb⟩ := hbetter C.initial_center
  have hfinite : C.value 0 ≠ ⊤ := by
    rw [hγ]
    exact ne_of_lt (hb.trans_le le_top)
  obtain ⟨γ, hco⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hμ : C.valuation 0 = baseBall v C.initial_center γ := by
    apply InitialMonomial.ext (γ := (γ : WithTop ℚ))
    · rw [hco]
      exact C.initial_formula
    · exact baseBall_initial v C.initial_center γ
  obtain ⟨f, hf⟩ := (finiteMLVChain_one_tangent_degree v θ C hbetter).1
  refine ⟨?_, ⟨f, hf.2.1⟩⟩
  rw [hμ, hν]
  exact baseBall_le_evaluation_of_radius_le v θ C.initial_center γ (hco.trans hγ).le

/-- In a genuine degree-one 2021 continuous augmentation family, every
assigned weight already belongs to the base value group. This is an actual
value of a difference of two base centres, not an assumption that every
rational monomial belongs to the base field. -/
theorem ContinuousFamily.degree_one_value_in_base
    (v : AddValuation E (WithTop ℚ)) {μ : AddValuation K[X] (WithTop ℚ)}
    (A : ContinuousFamily μ) (hdeg : A.stable_degree = 1)
    (hC : ∀ c : K, μ (C c) = v (algebraMap K E c)) (i : A.Index) :
    ∃ c : K, v (algebraMap K E c) = (A.value i : WithTop ℚ) := by
  letI := A.indexOrder
  letI := A.indexNoMax
  obtain ⟨j, hij⟩ := exists_gt i
  have hk := (A.compatible i j hij).key
  have hne := A.inequivalent i j hij
  rw [A.degree_one_valuation v hdeg hC i, A.degree_one_polynomial hdeg j] at hk
  rw [A.degree_one_valuation v hdeg hC i, A.degree_one_polynomial hdeg i,
    A.degree_one_polynomial hdeg j] at hne
  simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_neg] at hne
  have hd := baseBall_key_inequivalent_center_value v _ _ _ hk hne
  refine ⟨-(A.polynomial i).coeff 0 - (-(A.polynomial j).coeff 0), ?_⟩
  rw [map_sub]
  exact hd

end NTCThird.MLV
