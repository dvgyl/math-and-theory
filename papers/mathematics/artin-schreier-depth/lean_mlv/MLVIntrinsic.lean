import MLVReverse

/-!
# Minimum MLV length over all primitive generators

The set below is formed from actual complete finite Mac Lane--Vaquie chains
ending at evaluation at each primitive generator. No approximation predicate
occurs in its definition. The comparison with the independently defined
Okutsu minimum is proved at length one for extensions without a maximal base
approximation. General all-length comparison or chain-length invariance is
not assumed.
-/

noncomputable section

open scoped IntermediateField

namespace NTCThird.MLV

universe u

variable (K : Type u) {E : Type*} [Field K] [Field E] [Algebra K E]

/-- Every length of an actual complete MLV chain for every primitive generator
of the actual intermediate field. Both existential quantifiers are literal. -/
noncomputable def realizedMLVLengths (v : AddValuation E (WithTop ℚ))
    (L : IntermediateField K E) : Set ℕ :=
  {r | ∃ θ : E, K⟮θ⟯ = L ∧
    Nonempty (FiniteMLVChain (v.comap (algebraMap K E))
      (evaluationValuation v θ) (minpoly K θ) r)}

theorem zero_not_mem_realizedMLVLengths (v : AddValuation E (WithTop ℚ))
    (L : IntermediateField K E) (hL : L ≠ ⊥) :
    0 ∉ realizedMLVLengths K v L := by
  rintro ⟨θ, hgen, ⟨C⟩⟩
  apply hL
  rw [← hgen]
  exact (NTCThird.elementDegree_one_iff_adjoin_eq_bot K θ).mp
    (finiteMLVChain_zero_degree C)

theorem finiteMLVChain_one_iff_okutsuSequence_one
    [IsAlgClosed E] [Algebra.IsAlgebraic K E]
    (v : AddValuation E (WithTop ℚ)) (θ : E)
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    Nonempty (FiniteMLVChain (v.comap (algebraMap K E))
      (evaluationValuation v θ) (minpoly K θ) 1) ↔
      Nonempty (NTCThird.OkutsuSequence K v θ 1) :=
  (finiteMLVChain_one_iff v θ hbetter).trans (NTCThird.okutsuSequence_one_iff K v θ).symm

/-- The minimum ranges over all primitive generators, including generators
unrelated to the one chosen in the forward construction. -/
theorem minimum_mlvLength_one_iff
    [IsAlgClosed E] [Algebra.IsAlgebraic K E]
    (v : AddValuation E (WithTop ℚ)) (L : IntermediateField K E) (hL : L ≠ ⊥)
    (hbetter : ∀ θ : E, K⟮θ⟯ = L → ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    IsLeast (realizedMLVLengths K v L) 1 ↔
      ∃ θ : E, K⟮θ⟯ = L ∧
        1 < NTCThird.elementDegree K θ ∧ NTCThird.BaseApproximation K v θ := by
  constructor
  · rintro ⟨⟨θ, hgen, hchain⟩, _⟩
    exact ⟨θ, hgen, (finiteMLVChain_one_iff v θ (hbetter θ hgen)).mp hchain⟩
  · rintro ⟨θ, hgen, hdegree, happrox⟩
    refine ⟨⟨θ, hgen, (finiteMLVChain_one_iff v θ (hbetter θ hgen)).mpr
      ⟨hdegree, happrox⟩⟩, ?_⟩
    intro r hr
    have hr0 : r ≠ 0 := by
      intro h
      subst r
      exact zero_not_mem_realizedMLVLengths K v L hL hr
    omega

/-- Exact equality of the two minimum-one assertions, with the genuine MLV
set and the genuine Okutsu set defined independently. -/
theorem minimum_mlvLength_one_iff_okutsu
    [IsAlgClosed E] [Algebra.IsAlgebraic K E]
    (v : AddValuation E (WithTop ℚ)) (L : IntermediateField K E) (hL : L ≠ ⊥)
    (hbetter : ∀ θ : E, K⟮θ⟯ = L → ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    IsLeast (realizedMLVLengths K v L) 1 ↔
      IsLeast (NTCThird.realizedOkutsuLengths K v L) 1 := by
  rw [minimum_mlvLength_one_iff K v L hL hbetter,
    NTCThird.minimum_okutsuLength_one_iff K v L hL]

theorem minimum_mlvLength_one_iff_algebraic
    [IsAlgClosed E] [Algebra.IsAlgebraic K E]
    (v : AddValuation E (WithTop ℚ)) (L : IntermediateField K E) (hL : L ≠ ⊥)
    (hbetter : ∀ θ : E, K⟮θ⟯ = L → ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    IsLeast (realizedMLVLengths K v L) 1 ↔
      ∃ θ : E, K⟮θ⟯ = L ∧ NTCThird.BaseApproximation K v θ :=
  (minimum_mlvLength_one_iff_okutsu K v L hL hbetter).trans
    (NTCThird.minimum_okutsuLength_one_iff_algebraic K v L hL)

end NTCThird.MLV
