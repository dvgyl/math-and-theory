import MLVGauss

/-!
# Finite Mac Lane--Vaquie chains

The definitions in this file retain actual polynomial valuations, actual key
polynomials, arbitrary finite polynomial expansions, compatible continuous
families, their stable degree, and the initial-key restriction. They follow
Nart (2021), Definitions 3.2 and 4.1, and the equivalent finite-support
formulation in Nart (2024), Definition 1.11.

Neither an Okutsu sequence nor an approximation predicate occurs in these
definitions. General existence or length invariance is not assumed.
-/

noncomputable section

open Polynomial

namespace NTCThird.MLV

universe u

variable {K : Type u} [Field K]

/-- The full ordinary augmentation formula, on every finite φ-expansion.
Using an arbitrary finite support also covers zero coefficients and zero
polynomials, without an implicit nonzero-polynomial convention. -/
structure OrdinaryAugmentation
    (μ ν : AddValuation K[X] (WithTop ℚ)) (φ : K[X]) (γ : WithTop ℚ) : Prop where
  key : KeyPolynomial μ φ
  increase : μ φ < γ
  expansion_formula : ∀ (s : Finset ℕ) (a : ℕ → K[X]),
    (∀ i ∈ s, (a i).natDegree < φ.natDegree) →
    ν (∑ i ∈ s, a i * φ ^ i) = s.inf (fun i => μ (a i) + i • γ)

theorem OrdinaryAugmentation.low_degree_eq
    {μ ν : AddValuation K[X] (WithTop ℚ)} {φ : K[X]} {γ : WithTop ℚ}
    (A : OrdinaryAugmentation μ ν φ γ) (f : K[X])
    (hf : f.natDegree < φ.natDegree) : ν f = μ f := by
  simpa using A.expansion_formula {0} (fun _ => f) (by simpa using hf)

theorem OrdinaryAugmentation.key_value
    {μ ν : AddValuation K[X] (WithTop ℚ)} {φ : K[X]} {γ : WithTop ℚ}
    (A : OrdinaryAugmentation μ ν φ γ) : ν φ = γ := by
  simpa using A.expansion_formula {1} (fun _ => 1) (by
    simpa using A.key.positive_degree)

/-- Equality of nonzero initial forms; the polynomials where this is used are
key polynomials, so their initial forms are nonzero. -/
noncomputable def SameInitial (μ : AddValuation K[X] (WithTop ℚ)) (f g : K[X]) : Prop :=
  μ f = μ g ∧ μ f < μ (f - g)

/-- A continuous family of ordinary augmentations, with all three clauses
of Nart (2021), Definition 3.2 retained. Its indices are not restricted to ℕ.
The family values lie in Q because the ambient valuation space is rational. -/
structure ContinuousFamily (μ : AddValuation K[X] (WithTop ℚ)) where
  Index : Type u
  indexOrder : LinearOrder Index
  indexNonempty : Nonempty Index
  indexNoMax : letI := indexOrder; NoMaxOrder Index
  valuation : Index → AddValuation K[X] (WithTop ℚ)
  polynomial : Index → K[X]
  value : Index → ℚ
  strict_values : letI := indexOrder; StrictMono value
  stable_degree : ℕ
  positive_degree : 0 < stable_degree
  common_degree : ∀ i, (polynomial i).natDegree = stable_degree
  from_base : ∀ i, OrdinaryAugmentation μ (valuation i) (polynomial i) (value i : WithTop ℚ)
  compatible : letI := indexOrder; ∀ i j, i < j →
    OrdinaryAugmentation (valuation i) (valuation j) (polynomial j) (value j : WithTop ℚ)
  inequivalent : letI := indexOrder; ∀ i j, i < j →
    ¬SameInitial (valuation i) (polynomial i) (polynomial j)

/-- A genuine limit augmentation, including the stable-value existence needed
to make its expansion formula meaningful. An essential family has unstable
degree strictly greater than its stable degree. -/
structure LimitAugmentation
    (μ ν : AddValuation K[X] (WithTop ℚ)) (φ : K[X]) (γ : WithTop ℚ) where
  family : ContinuousFamily μ
  essential : family.stable_degree < φ.natDegree
  key : letI := family.indexOrder; LimitKeyPolynomial family.valuation φ
  stable_below : letI := family.indexOrder; ∀ f : K[X], f.natDegree < φ.natDegree →
    ∃ δ : WithTop ℚ, StableValue family.valuation f δ
  increase : ∀ i, family.valuation i φ < γ
  expansion_formula : letI := family.indexOrder;
    ∀ (s : Finset ℕ) (a : ℕ → K[X]) (δ : ℕ → WithTop ℚ),
      (∀ i ∈ s, (a i).natDegree < φ.natDegree) →
      (∀ i ∈ s, StableValue family.valuation (a i) (δ i)) →
      ν (∑ i ∈ s, a i * φ ^ i) = s.inf (fun i => δ i + i • γ)

theorem LimitAugmentation.stable_value_eq
    {μ ν : AddValuation K[X] (WithTop ℚ)} {φ : K[X]} {γ : WithTop ℚ}
    (L : LimitAugmentation μ ν φ γ) (f : K[X]) (hf : f.natDegree < φ.natDegree)
    (δ : WithTop ℚ)
    (hδ : letI := L.family.indexOrder; StableValue L.family.valuation f δ) : ν f = δ := by
  letI := L.family.indexOrder
  simpa using L.expansion_formula {0} (fun _ => f) (fun _ => δ)
    (by simpa using hf) (by simpa using hδ)

theorem LimitAugmentation.stable_at_endpoint
    {μ ν : AddValuation K[X] (WithTop ℚ)} {φ : K[X]} {γ : WithTop ℚ}
    (L : LimitAugmentation μ ν φ γ) (f : K[X]) (hf : f.natDegree < φ.natDegree) :
    letI := L.family.indexOrder; StableValue L.family.valuation f (ν f) := by
  letI := L.family.indexOrder
  obtain ⟨δ, hδ⟩ := L.stable_below f hf
  rw [L.stable_value_eq f hf δ hδ]
  exact hδ

/-- The defining expansion formula of the initial monomial valuation. This
also permits value infinity, needed for depth-zero evaluation valuations of
linear polynomials. -/
noncomputable def InitialMonomial
    (v : AddValuation K (WithTop ℚ)) (a : K) (γ : WithTop ℚ)
    (μ : AddValuation K[X] (WithTop ℚ)) : Prop :=
  ∀ (s : Finset ℕ) (c : ℕ → K),
    μ (∑ i ∈ s, C (c i) * (X - C a) ^ i) = s.inf (fun i => v (c i) + i • γ)

theorem InitialMonomial.ext
    {v : AddValuation K (WithTop ℚ)} {a : K} {γ : WithTop ℚ}
    {μ ν : AddValuation K[X] (WithTop ℚ)}
    (hμ : InitialMonomial v a γ μ) (hν : InitialMonomial v a γ ν) : μ = ν := by
  apply AddValuation.ext
  intro f
  rw [← sum_taylor_eq f a]
  exact (hμ _ _).trans (hν _ _).symm

theorem OrdinaryAugmentation.initial_of_linear
    {μ ν : AddValuation K[X] (WithTop ℚ)} {v : AddValuation K (WithTop ℚ)}
    {a : K} {γ : WithTop ℚ}
    (A : OrdinaryAugmentation μ ν (X - C a) γ)
    (hC : ∀ c : K, μ (C c) = v c) : InitialMonomial v a γ ν := by
  intro s c
  rw [A.expansion_formula s (fun i => C (c i)) (by simp)]
  apply Finset.inf_congr rfl
  intro i _
  rw [hC]

/-- The tangent direction consists of the monic polynomials of smallest
degree where the later valuation is strictly larger. -/
noncomputable def TangentDirection
    (μ ν : AddValuation K[X] (WithTop ℚ)) (φ : K[X]) : Prop :=
  φ.Monic ∧ μ φ < ν φ ∧
    ∀ g : K[X], g.Monic → μ g < ν g → φ.natDegree ≤ g.natDegree

/-- A finite complete MLV chain with the actual endpoint and its defining
polynomial. The length counts genuine ordinary/limit augmentation steps,
after the initial monomial valuation. -/
structure FiniteMLVChain
    (v : AddValuation K (WithTop ℚ)) (ν : AddValuation K[X] (WithTop ℚ))
    (F : K[X]) (r : ℕ) where
  valuation : Fin (r + 1) → AddValuation K[X] (WithTop ℚ)
  polynomial : Fin (r + 1) → K[X]
  value : Fin (r + 1) → WithTop ℚ
  base_extension : ∀ i c, valuation i (C c) = v c
  monic : ∀ i, (polynomial i).Monic
  initial_center : K
  initial_polynomial : polynomial 0 = X - C initial_center
  initial_formula : InitialMonomial v initial_center (value 0) (valuation 0)
  terminal_polynomial : polynomial (Fin.last r) = F
  terminal_valuation : valuation (Fin.last r) = ν
  terminal_value : value (Fin.last r) = ⊤
  key_values : ∀ i, valuation i (polynomial i) = value i
  nonterminal_key : ∀ i : Fin r,
    KeyPolynomial (valuation i.castSucc) (polynomial i.castSucc)
  nonterminal_degree : ∀ i : Fin r,
    HasDegree (valuation i.castSucc) (polynomial i.castSucc).natDegree
  strict_degrees : StrictMono (fun i => (polynomial i).natDegree)
  endpoint_values : ∀ i : Fin r, ν (polynomial i.castSucc) = value i.castSucc
  step : ∀ i : Fin r,
    OrdinaryAugmentation (valuation i.castSucc) (valuation i.succ)
      (polynomial i.succ) (value i.succ) ∨
    ∃ L : LimitAugmentation (valuation i.castSucc) (valuation i.succ)
        (polynomial i.succ) (value i.succ),
      L.family.stable_degree = (polynomial i.castSucc).natDegree ∧
      ¬TangentDirection (valuation i.castSucc) (valuation i.succ) (polynomial i.castSucc)

theorem finiteMLVChain_zero_degree
    {v : AddValuation K (WithTop ℚ)} {ν : AddValuation K[X] (WithTop ℚ)} {F : K[X]}
    (C : FiniteMLVChain v ν F 0) : F.natDegree = 1 := by
  have hz : (Fin.last 0 : Fin (0 + 1)) = 0 := rfl
  rw [← C.terminal_polynomial, hz, C.initial_polynomial, natDegree_X_sub_C]

/-- A nonlinear minimal polynomial cannot acquire spurious depth zero. -/
theorem no_finiteMLVChain_zero
    {v : AddValuation K (WithTop ℚ)} {ν : AddValuation K[X] (WithTop ℚ)} {F : K[X]}
    (hF : 1 < F.natDegree) : ¬Nonempty (FiniteMLVChain v ν F 0) := by
  rintro ⟨C⟩
  have h := finiteMLVChain_zero_degree C
  omega

theorem rational_weight_eq_nsmul (i : ℕ) (γ : ℚ) :
    (((i : ℚ) * γ : ℚ) : WithTop ℚ) = i • (γ : WithTop ℚ) := by
  simpa only [nsmul_eq_mul] using (WithTop.coe_nsmul γ i)

theorem gaussValue_eq_inf_of_support_subset
    (v : AddValuation K (WithTop ℚ)) (γ : ℚ) (f : K[X]) (s : Finset ℕ)
    (hs : f.support ⊆ s) :
    gaussValue v γ f = s.inf (weightedCoefficient v γ f) := by
  apply le_antisymm
  · exact Finset.le_inf (fun i _ => gaussValue_le_coefficient v γ f i)
  · exact Finset.le_inf (fun i hi => Finset.inf_le (hs hi))

theorem gaussValue_sum_C_mul_X_pow
    (v : AddValuation K (WithTop ℚ)) (γ : ℚ) (s : Finset ℕ) (c : ℕ → K) :
    gaussValue v γ (∑ i ∈ s, C (c i) * X ^ i) =
      s.inf (fun i => v (c i) + i • (γ : WithTop ℚ)) := by
  classical
  let P : K[X] := ∑ i ∈ s, C (c i) * X ^ i
  have hcoeff (n : ℕ) : P.coeff n = if n ∈ s then c n else 0 := by
    simp [P, finsetSum_coeff, coeff_C_mul_X_pow]
  have hs : P.support ⊆ s := by
    intro n hn
    by_contra hnot
    have hzero : P.coeff n = 0 := by rw [hcoeff, if_neg hnot]
    exact (mem_support_iff.mp hn) hzero
  change gaussValue v γ P = _
  rw [gaussValue_eq_inf_of_support_subset v γ P s hs]
  apply Finset.inf_congr rfl
  intro i hi
  rw [weightedCoefficient, hcoeff, if_pos hi, rational_weight_eq_nsmul]

theorem linearMonomialValuation_expansion
    (v : AddValuation K (WithTop ℚ)) (a : K) (γ : ℚ)
    (s : Finset ℕ) (c : ℕ → K) :
    (linearMonomialValuation v a γ).valuation (∑ i ∈ s, C (c i) * (X - C a) ^ i) =
      s.inf (fun i => v (c i) + i • (γ : WithTop ℚ)) := by
  change gaussValue v γ (taylor a (∑ i ∈ s, C (c i) * (X - C a) ^ i)) = _
  have ht : taylor a (∑ i ∈ s, C (c i) * (X - C a) ^ i) =
      ∑ i ∈ s, C (c i) * X ^ i := by
    change (taylorAlgHom a) (∑ i ∈ s, C (c i) * (X - C a) ^ i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, map_pow]
    change taylor a (C (c i)) * (taylor a (X - C a)) ^ i = _
    rw [taylor_C, map_sub, taylor_X, taylor_C]
    simp
  rw [ht, gaussValue_sum_C_mul_X_pow]

theorem restrictedMonomial_initialFormula
    {E : Type*} [Field E] [Algebra K E]
    (v : AddValuation E (WithTop ℚ)) (a : K) (γ : ℚ) :
    InitialMonomial (v.comap (algebraMap K E)) a (γ : WithTop ℚ)
      (restrictedMonomial (K := K) (linearMonomialValuation v (algebraMap K E a) γ)) := by
  intro s c
  change (linearMonomialValuation v (algebraMap K E a) γ).valuation
    ((∑ i ∈ s, C (c i) * (X - C a) ^ i).map (algebraMap K E)) =
      s.inf (fun i => v (algebraMap K E (c i)) + i • (γ : WithTop ℚ))
  rw [Polynomial.map_sum]
  simp_rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_C, map_X]
  exact linearMonomialValuation_expansion v (algebraMap K E a) γ s
    (fun i => algebraMap K E (c i))

/-- Full ordinary augmentation by a linear key polynomial, with every
admissible polynomial coefficient reduced to its constant coefficient. -/
theorem ordinary_of_linear_initial
    (μ ν : AddValuation K[X] (WithTop ℚ)) (v : AddValuation K (WithTop ℚ))
    (a : K) (γ : WithTop ℚ)
    (hC : ∀ c : K, μ (C c) = v c)
    (hdom : ∀ f : K[X], μ f ≤ v (f.eval a))
    (hinc : μ (X - C a) < γ) (hν : InitialMonomial v a γ ν) :
    OrdinaryAugmentation μ ν (X - C a) γ := by
  refine ⟨keyPolynomial_linear μ v a hC hdom (ne_of_lt (hinc.trans_le le_top)), hinc, ?_⟩
  intro s b hb
  have hconst : ∀ i ∈ s, b i = C ((b i).coeff 0) := by
    intro i hi
    apply eq_C_of_natDegree_eq_zero
    have h := hb i hi
    rw [natDegree_X_sub_C] at h
    omega
  calc
    ν (∑ i ∈ s, b i * (X - C a) ^ i) =
        ν (∑ i ∈ s, C ((b i).coeff 0) * (X - C a) ^ i) := by
      congr 1
      exact Finset.sum_congr rfl (fun i hi =>
        congrArg (fun p : K[X] => p * (X - C a) ^ i) (hconst i hi))
    _ = s.inf (fun i => v ((b i).coeff 0) + i • γ) := hν s (fun i => (b i).coeff 0)
    _ = s.inf (fun i => μ (b i) + i • γ) := by
      apply Finset.inf_congr rfl
      intro i hi
      rw [hconst i hi, hC, coeff_C_zero]

end NTCThird.MLV
