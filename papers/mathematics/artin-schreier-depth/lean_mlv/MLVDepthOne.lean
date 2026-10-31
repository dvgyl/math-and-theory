import MLVChains

/-!
# A complete MLV chain of length one

This file constructs a complete finite MLV chain from the lower-degree
approximation property. It verifies ordinary augmentation, inequivalence,
the full limit formula, endpoint normalization and the tangent restriction.
The ambient objects are the finite MLV chains of MLVChains.lean. The reverse
comparison is proved separately in MLVReverse.lean.
-/

noncomputable section

open Polynomial

namespace NTCThird.MLV

universe u

variable {K : Type u} {E : Type*} [Field K] [Field E] [Algebra K E]

set_option maxHeartbeats 800000

noncomputable def baseBall (v : AddValuation E (WithTop ℚ)) (a : K) (γ : ℚ) :
    AddValuation K[X] (WithTop ℚ) :=
  restrictedMonomial (K := K) (linearMonomialValuation v (algebraMap K E a) γ)

@[simp] theorem baseBall_C (v : AddValuation E (WithTop ℚ)) (a c : K) (γ : ℚ) :
    baseBall v a γ (C c) = v (algebraMap K E c) := by
  change (linearMonomialValuation v (algebraMap K E a) γ).valuation
    ((C c).map (algebraMap K E)) = _
  rw [map_C, (linearMonomialValuation v (algebraMap K E a) γ).constant_value]

theorem baseBall_linear (v : AddValuation E (WithTop ℚ)) (a b : K) (γ : ℚ) :
    baseBall v a γ (X - C b) = min (γ : WithTop ℚ)
      (v (algebraMap K E a - algebraMap K E b)) := by
  change (linearMonomialValuation v (algebraMap K E a) γ).valuation
    ((X - C b).map (algebraMap K E)) = _
  rw [Polynomial.map_sub, map_X, map_C,
    (linearMonomialValuation v (algebraMap K E a) γ).linear_value]

@[simp] theorem baseBall_linear_self (v : AddValuation E (WithTop ℚ)) (a : K) (γ : ℚ) :
    baseBall v a γ (X - C a) = (γ : WithTop ℚ) := by
  rw [baseBall_linear]
  simp

theorem baseBall_linear_at_element
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a b : K) (γ : ℚ)
    (hγ : (γ : WithTop ℚ) = v (θ - algebraMap K E a)) :
    baseBall v a γ (X - C b) = min (γ : WithTop ℚ) (v (θ - algebraMap K E b)) := by
  rw [baseBall_linear, hγ, min_distance_change_centre]

theorem baseBall_le_evaluation_at_centre [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ)) (a : K) (γ : ℚ) (f : K[X]) :
    baseBall v a γ f ≤ v (algebraMap K E (f.eval a)) := by
  change (linearMonomialValuation v (algebraMap K E a) γ).valuation
    (f.map (algebraMap K E)) ≤ _
  simpa only [eval_map, eval₂_at_apply] using
    (linearMonomialValuation v (algebraMap K E a) γ).le_evaluation_at_centre
      (f.map (algebraMap K E))

theorem baseBall_linear_key [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ)) (a : K) (γ : ℚ) :
    KeyPolynomial (baseBall v a γ) (X - C a) := by
  apply keyPolynomial_linear _ (v.comap (algebraMap K E)) a
  · intro c
    exact baseBall_C v a c γ
  · intro f
    exact baseBall_le_evaluation_at_centre v a γ f
  · rw [baseBall_linear_self]
    exact WithTop.coe_ne_top

theorem baseBall_hasDegree_one [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ)) (a : K) (γ : ℚ) : HasDegree (baseBall v a γ) 1 :=
  hasDegree_one_of_linear_key _ a (baseBall_linear_key v a γ)

theorem baseBall_initial
    (v : AddValuation E (WithTop ℚ)) (a : K) (γ : ℚ) :
    InitialMonomial (v.comap (algebraMap K E)) a (γ : WithTop ℚ) (baseBall v a γ) :=
  restrictedMonomial_initialFormula v a γ

theorem baseBall_family_ordinary [IsAlgClosed E]
    {I : Type*} [LinearOrder I]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a : I → K) (γ : I → ℚ)
    (hγ : ∀ i, (γ i : WithTop ℚ) = v (θ - algebraMap K E (a i)))
    (hincr : StrictMono γ) {i j : I} (hij : i < j) :
    OrdinaryAugmentation (baseBall v (a i) (γ i)) (baseBall v (a j) (γ j))
      (X - C (a j)) (γ j : WithTop ℚ) := by
  apply ordinary_of_linear_initial _ _ (v.comap (algebraMap K E)) (a j) (γ j)
  · intro c
    exact baseBall_C v (a i) c (γ i)
  · intro f
    change baseBall v (a i) (γ i) f ≤ v (algebraMap K E (f.eval (a j)))
    apply le_trans _ (baseBall_le_evaluation_at_centre v (a j) (γ j) f)
    exact restrictedMonomial_family_le v θ a γ hγ hincr.monotone
      (fun k => linearMonomialValuation v (algebraMap K E (a k)) (γ k)) hij.le f
  · rw [baseBall_linear_at_element v θ (a i) (a j) (γ i) (hγ i), ← hγ j]
    have hlt : (γ i : WithTop ℚ) < (γ j : WithTop ℚ) := by exact_mod_cast hincr hij
    rw [min_eq_left hlt.le]
    exact hlt
  · exact baseBall_initial v (a j) (γ j)

theorem centre_difference_value
    {I : Type*} [LinearOrder I]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a : I → K) (γ : I → ℚ)
    (hγ : ∀ i, (γ i : WithTop ℚ) = v (θ - algebraMap K E (a i)))
    (hincr : StrictMono γ) {i j : I} (hij : i < j) :
    v (algebraMap K E (a j - a i)) = (γ i : WithTop ℚ) := by
  have hlt : v (θ - algebraMap K E (a i)) < v (θ - algebraMap K E (a j)) := by
    rw [← hγ i, ← hγ j]
    exact_mod_cast hincr hij
  have h := v.map_sub_eq_of_lt_left hlt
  rw [← hγ i] at h
  convert h using 1
  congr 1
  rw [map_sub]
  ring

theorem baseBall_family_inequivalent
    {I : Type*} [LinearOrder I]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a : I → K) (γ : I → ℚ)
    (hγ : ∀ i, (γ i : WithTop ℚ) = v (θ - algebraMap K E (a i)))
    (hincr : StrictMono γ) {i j : I} (hij : i < j) :
    ¬SameInitial (baseBall v (a i) (γ i)) (X - C (a i)) (X - C (a j)) := by
  rintro ⟨_, hlt⟩
  have hpoly : (X - C (a i)) - (X - C (a j)) = (C (a j - a i) : K[X]) := by
    rw [C_sub]
    ring
  rw [baseBall_linear_self, hpoly, baseBall_C,
    centre_difference_value v θ a γ hγ hincr hij] at hlt
  exact lt_irrefl _ hlt

/-- The strictly improving tail is an actual continuous family of ordinary
augmentations of the initial Gauss valuation, including inequivalence. -/
noncomputable def continuousBaseBallFamily [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a : ℕ → K) (γ : ℕ → ℚ)
    (hγ : ∀ i, (γ i : WithTop ℚ) = v (θ - algebraMap K E (a i)))
    (hincr : StrictMono γ) : ContinuousFamily (baseBall v (a 0) (γ 0)) where
  Index := ULift.{u} ℕ
  indexOrder := inferInstance
  indexNonempty := inferInstance
  indexNoMax := ⟨fun i => ⟨⟨i.down + 1⟩, Nat.lt_succ_self i.down⟩⟩
  valuation i := baseBall v (a (i.down + 1)) (γ (i.down + 1))
  polynomial i := X - C (a (i.down + 1))
  value i := γ (i.down + 1)
  strict_values := by
    intro i j hij
    exact hincr (Nat.add_lt_add_right hij 1)
  stable_degree := 1
  positive_degree := by decide
  common_degree := by intro i; simp
  from_base := by
    intro i
    exact baseBall_family_ordinary v θ a γ hγ hincr (Nat.zero_lt_succ i.down)
  compatible := by
    intro i j hij
    exact baseBall_family_ordinary v θ a γ hγ hincr (Nat.add_lt_add_right hij 1)
  inequivalent := by
    intro i j hij
    exact baseBall_family_inequivalent v θ a γ hγ hincr (Nat.add_lt_add_right hij 1)

/-- A linear key polynomial must define a centre inside the original ball.
The proof uses key-polynomial minimality on an actual constant polynomial. -/
theorem baseBall_key_center_bound
    (v : AddValuation E (WithTop ℚ)) (a b : K) (γ : ℚ)
    (hk : KeyPolynomial (baseBall v a γ) (X - C b)) :
    (γ : WithTop ℚ) ≤ v (algebraMap K E a - algebraMap K E b) := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hpoly : C (a - b) - (X - C b) * 1 = -(X - C a : K[X]) := by
    rw [C_sub]
    ring
  have hc : baseBall v a γ (C (a - b)) ≠ ⊤ := by
    rw [baseBall_C, map_sub]
    exact ne_of_lt (hlt.trans_le le_top)
  have hdiv : InitialDivides (baseBall v a γ) (X - C b) (C (a - b)) := by
    refine Or.inr ⟨1, ?_⟩
    rw [hpoly, (baseBall v a γ).map_neg, baseBall_linear_self, baseBall_C, map_sub]
    exact hlt
  have hc0 : (C (a - b) : K[X]) ≠ 0 := by
    intro hz
    apply hc
    rw [hz, (baseBall v a γ).map_zero]
  have hmin := hk.minimal (C (a - b)) hc0 hdiv
  simpa using hmin

theorem baseBall_key_inequivalent_center_value
    (v : AddValuation E (WithTop ℚ)) (a b : K) (γ : ℚ)
    (hk : KeyPolynomial (baseBall v a γ) (X - C b))
    (hne : ¬SameInitial (baseBall v a γ) (X - C a) (X - C b)) :
    v (algebraMap K E a - algebraMap K E b) = (γ : WithTop ℚ) := by
  apply le_antisymm
  · by_contra hn
    have hlt := lt_of_not_ge hn
    apply hne
    refine ⟨?_, ?_⟩
    · rw [baseBall_linear_self, baseBall_linear, min_eq_left hlt.le]
    · have hpoly : (X - C a) - (X - C b) = (C (b - a) : K[X]) := by
        rw [C_sub]
        ring
      rw [baseBall_linear_self, hpoly, baseBall_C, map_sub, v.map_sub_swap]
      exact hlt
  · exact baseBall_key_center_bound v a b γ hk

theorem ContinuousFamily.degree_one_polynomial
    {μ : AddValuation K[X] (WithTop ℚ)} (A : ContinuousFamily μ)
    (hdeg : A.stable_degree = 1) (i : A.Index) :
    A.polynomial i = X - C (-(A.polynomial i).coeff 0) := by
  rw [(A.from_base i).key.monic.eq_X_add_C ((A.common_degree i).trans hdeg)]
  simp

theorem ContinuousFamily.degree_one_valuation
    (v : AddValuation E (WithTop ℚ)) {μ : AddValuation K[X] (WithTop ℚ)}
    (A : ContinuousFamily μ) (hdeg : A.stable_degree = 1)
    (hC : ∀ c : K, μ (C c) = v (algebraMap K E c)) (i : A.Index) :
    A.valuation i = baseBall v (-(A.polynomial i).coeff 0) (A.value i) := by
  have haug := A.from_base i
  rw [A.degree_one_polynomial hdeg i] at haug
  exact (haug.initial_of_linear hC).ext (baseBall_initial v _ _)

/-- The inequivalence requirement makes each family's own linear key stable
at its assigned value. This derives the endpoint radii, rather than adding
an approximation property to the chain definition. -/
theorem ContinuousFamily.stable_degree_one_key
    (v : AddValuation E (WithTop ℚ)) {μ : AddValuation K[X] (WithTop ℚ)}
    (A : ContinuousFamily μ) (hdeg : A.stable_degree = 1)
    (hC : ∀ c : K, μ (C c) = v (algebraMap K E c)) (i : A.Index) :
    letI := A.indexOrder; StableValue A.valuation (A.polynomial i) (A.value i : WithTop ℚ) := by
  letI := A.indexOrder
  refine ⟨i, ?_⟩
  intro j hij
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact (A.from_base i).key_value
  · have hk := (A.compatible i j hij).key
    have hne := A.inequivalent i j hij
    rw [A.degree_one_valuation v hdeg hC i, A.degree_one_polynomial hdeg j] at hk
    rw [A.degree_one_valuation v hdeg hC i, A.degree_one_polynomial hdeg i,
      A.degree_one_polynomial hdeg j] at hne
    simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_neg] at hne
    have hd := baseBall_key_inequivalent_center_value v _ _ _ hk hne
    rw [A.degree_one_valuation v hdeg hC j, A.degree_one_polynomial hdeg i,
      baseBall_linear, v.map_sub_swap, hd]
    apply min_eq_right
    exact_mod_cast (A.strict_values hij).le

theorem LimitAugmentation.degree_one_family_value
    (v : AddValuation E (WithTop ℚ)) (θ : E)
    {μ : AddValuation K[X] (WithTop ℚ)} {F : K[X]} {γ : WithTop ℚ}
    (L : LimitAugmentation μ (evaluationValuation v θ) F γ)
    (hdeg : L.family.stable_degree = 1)
    (hC : ∀ c : K, μ (C c) = v (algebraMap K E c)) (i : L.family.Index) :
    (L.family.value i : WithTop ℚ) =
      v (θ - algebraMap K E (-(L.family.polynomial i).coeff 0)) := by
  have hf : (L.family.polynomial i).natDegree < F.natDegree := by
    rw [L.family.common_degree]
    exact L.essential
  have hv := L.stable_value_eq (L.family.polynomial i) hf _
    (L.family.stable_degree_one_key v hdeg hC i)
  rw [L.family.degree_one_polynomial hdeg i] at hv
  simpa using hv.symm

theorem evaluation_expansion_at_top
    (v : AddValuation E (WithTop ℚ)) (θ : E) (F : K[X])
    (hF : aeval θ F = 0) (s : Finset ℕ) (a : ℕ → K[X]) :
    evaluationValuation v θ (∑ i ∈ s, a i * F ^ i) =
      s.inf (fun i => v (aeval θ (a i)) + i • (⊤ : WithTop ℚ)) := by
  classical
  have heval : aeval θ (∑ i ∈ s, a i * F ^ i) =
      if 0 ∈ s then aeval θ (a 0) else 0 := by
    simp [map_sum, map_mul, map_pow, hF, zero_pow_eq, mul_ite]
  rw [evaluationValuation_apply, heval]
  by_cases hz : 0 ∈ s
  · rw [if_pos hz]
    apply le_antisymm
    · apply Finset.le_inf
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        simp
      · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        simp [succ_nsmul]
    · simpa using Finset.inf_le (f := fun i =>
        v (aeval θ (a i)) + i • (⊤ : WithTop ℚ)) hz
  · rw [if_neg hz, v.map_zero]
    symm
    apply top_unique
    apply Finset.le_inf
    intro i hi
    have hi0 : i ≠ 0 := by rintro rfl; exact hz hi
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    simp [succ_nsmul]

/-- A cofinal degree-one approximation family constructs a complete MLV
chain of length one, including the full limit-expansion formula and the
initial tangent restriction. -/
theorem exists_finiteMLVChain_one_of_baseApproximation [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (hθ : IsIntegral K θ)
    (hdegree : 1 < NTCThird.elementDegree K θ)
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d))
    (happrox : NTCThird.BaseApproximation K v θ) :
    Nonempty (FiniteMLVChain (v.comap (algebraMap K E))
      (evaluationValuation v θ) (minpoly K θ) 1) := by
  classical
  obtain ⟨a, γ, hγ, hincr, hcofinal⟩ := exists_cofinal_approximation_sequence v θ hbetter
  let A := continuousBaseBallFamily v θ a γ hγ hincr
  letI := A.indexOrder
  letI := A.indexNonempty
  letI := A.indexNoMax
  let a' : A.Index → K := fun i => a (i.down + 1)
  let γ' : A.Index → ℚ := fun i => γ (i.down + 1)
  have hγ' : ∀ i, (γ' i : WithTop ℚ) = v (θ - algebraMap K E (a' i)) :=
    fun i => hγ (i.down + 1)
  have hincr' : StrictMono γ' := by
    intro i j hij
    exact hincr (Nat.add_lt_add_right hij 1)
  have hcofinal' : ∀ c : K, ∃ i, v (θ - algebraMap K E c) ≤ (γ' i : WithTop ℚ) := by
    intro c
    obtain ⟨n, hn⟩ := hcofinal c
    refine ⟨ULift.up n, hn.trans ?_⟩
    change (γ n : WithTop ℚ) ≤ (γ (n + 1) : WithTop ℚ)
    exact_mod_cast (hincr (Nat.lt_succ_self n)).le
  let μ' : ∀ i, LinearMonomialValuation v (algebraMap K E (a' i)) (γ' i) :=
    fun i => linearMonomialValuation v (algebraMap K E (a' i)) (γ' i)
  have hstable : ∀ f : K[X], f.natDegree < (minpoly K θ).natDegree →
      StableValue A.valuation f (v (aeval θ f)) := by
    intro f hf
    exact stable_evaluation_of_baseApproximation v θ a' γ' hγ' hincr' hcofinal'
      happrox μ' f hf
  have hkey : LimitKeyPolynomial A.valuation (minpoly K θ) :=
    minpoly_limitKey_of_baseApproximation v θ hθ a' γ' hγ' hincr' hcofinal' happrox μ'
  let L : LimitAugmentation (baseBall v (a 0) (γ 0))
      (evaluationValuation v θ) (minpoly K θ) ⊤ := {
    family := A
    essential := hdegree
    key := hkey
    stable_below := fun f hf => ⟨_, hstable f hf⟩
    increase := by
      intro i
      obtain ⟨j, hij⟩ := exists_gt i
      exact (hkey.unstable hij).trans_le le_top
    expansion_formula := by
      intro s b δ hb hδ
      rw [evaluation_expansion_at_top v θ (minpoly K θ) (minpoly.aeval K θ)]
      apply Finset.inf_congr rfl
      intro i hi
      rw [stableValue_unique (hδ i hi) (hstable (b i) (hb i hi))] }
  refine ⟨{
    valuation := ![baseBall v (a 0) (γ 0), evaluationValuation v θ]
    polynomial := ![X - C (a 0), minpoly K θ]
    value := ![(γ 0 : WithTop ℚ), ⊤]
    base_extension := ?_
    monic := ?_
    initial_center := a 0
    initial_polynomial := rfl
    initial_formula := baseBall_initial v (a 0) (γ 0)
    terminal_polynomial := rfl
    terminal_valuation := rfl
    terminal_value := rfl
    key_values := ?_
    nonterminal_key := ?_
    nonterminal_degree := ?_
    strict_degrees := ?_
    endpoint_values := ?_
    step := ?_ }⟩
  · intro i c
    fin_cases i <;> simpa using (show v (algebraMap K E c) =
      (v.comap (algebraMap K E)) c from rfl)
  · intro i
    fin_cases i
    · exact monic_X_sub_C _
    · exact minpoly.monic hθ
  · intro i
    fin_cases i
    · exact baseBall_linear_self v (a 0) (γ 0)
    · simp [evaluationValuation_apply, minpoly.aeval]
  · intro i
    fin_cases i
    exact baseBall_linear_key v (a 0) (γ 0)
  · intro i
    fin_cases i
    simpa using baseBall_hasDegree_one v (a 0) (γ 0)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [NTCThird.elementDegree]
    exact hdegree
  · intro i
    fin_cases i
    simpa using (hγ 0).symm
  · intro i
    fin_cases i
    right
    refine ⟨L, ?_, ?_⟩
    · change 1 = (X - C (a 0) : K[X]).natDegree
      simp
    · rintro ⟨_, hlt, _⟩
      change baseBall v (a 0) (γ 0) (X - C (a 0)) <
        evaluationValuation v θ (X - C (a 0)) at hlt
      rw [baseBall_linear_self] at hlt
      have heval : evaluationValuation v θ (X - C (a 0)) = (γ 0 : WithTop ℚ) := by
        simpa using (hγ 0).symm
      rw [heval] at hlt
      exact lt_irrefl _ hlt

end NTCThird.MLV
