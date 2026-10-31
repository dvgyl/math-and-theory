import MLVSource2024
import MLVLinearNormalForm

/-!
# The two published MLV conventions at length one

`Source2024LimitFamily` records the degree-one specialization of Nart (2024),
Definitions 1.9--1.10: an infinite well-ordered increasing family containing
the predecessor as its first member.  It does not assume that its indices
have no maximum, nor does it assume eventual stability of lower-degree
polynomials.  The latter is derived below from genuine key polynomials and
the full Gauss normal form.

`Source2024ChainOne` includes either an ordinary or a limit step, the actual
evaluation endpoint, the initial monomial formula, strict degree increase,
and endpoint normalization.  The comparison is existential at length one;
it does not assert a conversion of every longer chain or preservation of
the original family when constructing the converse witness.

References:
* Nart (2021), arXiv:1911.01714v4, Definitions 3.2 and 4.1;
* Nart (2024), doi:10.69763/polyjmath.1.4, Definitions 1.9--1.11.
-/

noncomputable section

open Polynomial
open scoped IntermediateField

namespace NTCThird.MLV

universe u uI uE

variable {K : Type u} {E : Type uE} [Field K] [Field E] [Algebra K E]

set_option maxHeartbeats 1200000

/-- The degree-one specialization of the continuous limit family used in
the 2024 presentation.  In particular, `Index` may have a last element:
no no-maximal-index condition is silently added to that source definition.
The formula quantifies over every finite polynomial expansion. -/
structure Source2024LimitFamily
    (v : AddValuation K (WithTop ℚ))
    (μ ν : AddValuation K[X] (WithTop ℚ)) (F : K[X]) where
  Index : Type uI
  indexOrder : LinearOrder Index
  indexWellFounded : letI := indexOrder; WellFoundedLT Index
  indexInfinite : Infinite Index
  first : Index
  first_le : letI := indexOrder; ∀ i, first ≤ i
  valuation : Index → AddValuation K[X] (WithTop ℚ)
  first_valuation : valuation first = μ
  base_extension : ∀ i c, valuation i (C c) = v c
  degree_one : ∀ i, HasDegree (valuation i) 1
  increasing : letI := indexOrder; ∀ i j, i < j →
    (∀ f : K[X], valuation i f ≤ valuation j f) ∧
      ∃ f : K[X], valuation i f < valuation j f
  key : letI := indexOrder; LimitKeyPolynomial valuation F
  increase : ∀ i, valuation i F < ⊤
  expansion_formula : letI := indexOrder;
    ∀ (s : Finset ℕ) (a : ℕ → K[X]) (δ : ℕ → WithTop ℚ),
      (∀ i ∈ s, (a i).natDegree < F.natDegree) →
      (∀ i ∈ s, StableValue valuation (a i) (δ i)) →
      ν (∑ i ∈ s, a i * F ^ i) = s.inf (fun i => δ i + i • (⊤ : WithTop ℚ))

theorem Source2024LimitFamily.monotone
    {v : AddValuation K (WithTop ℚ)}
    {μ ν : AddValuation K[X] (WithTop ℚ)} {F : K[X]}
    (A : Source2024LimitFamily.{u, uI} v μ ν F) :
    letI := A.indexOrder;
    ∀ i j, i ≤ j → ∀ f : K[X], A.valuation i f ≤ A.valuation j f := by
  letI := A.indexOrder
  intro i j hij f
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact le_rfl
  · exact (A.increasing i j hij).1 f

/-- A polynomial that is not strictly unstable is eventually constant. -/
theorem Source2024LimitFamily.stable_of_not_unstable [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ))
    {μ ν : AddValuation K[X] (WithTop ℚ)} {F : K[X]}
    (A : Source2024LimitFamily.{u, uI} (v.comap (algebraMap K E)) μ ν F)
    (f : K[X])
    (hnot : letI := A.indexOrder; ¬Unstable A.valuation f) :
    letI := A.indexOrder;
    ∃ δ : WithTop ℚ, StableValue A.valuation f δ := by
  classical
  letI := A.indexOrder
  letI : Nonempty A.Index := ⟨A.first⟩
  choose a γ hρ using (fun i =>
    exists_eq_baseBall_of_hasDegree_one v (A.valuation i)
      (A.base_extension i) (A.degree_one i))
  have hρfun : A.valuation = fun i => baseBall v (a i) (γ i) := funext hρ
  have hincr : StrictMono γ := by
    intro i j hij
    have h := A.increasing i j hij
    rw [hρ i, hρ j] at h
    exact baseBall_radius_lt_of_lt v (a i) (a j) (γ i) (γ j) h.1 h.2
  have hnest : ∀ i j, i ≤ j →
      (γ i : WithTop ℚ) ≤ v (algebraMap K E (a j) - algebraMap K E (a i)) := by
    intro i j hij
    have h := A.monotone i j hij
    rw [hρ i, hρ j] at h
    rw [v.map_sub_swap]
    exact baseBall_centre_le_of_le v (a i) (a j) (γ i) (γ j) h
  rw [hρfun] at hnot ⊢
  exact baseBall_family_stable_of_not_unstable v a γ hincr hnest f hnot

/-- Every lower-degree polynomial is eventually constant. This is proved
from the source-side clauses, not supplied as an extra record premise. -/
theorem Source2024LimitFamily.stable_below [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ))
    {μ ν : AddValuation K[X] (WithTop ℚ)} {F : K[X]}
    (A : Source2024LimitFamily.{u, uI} (v.comap (algebraMap K E)) μ ν F)
    (f : K[X]) (hf : f.natDegree < F.natDegree) :
    letI := A.indexOrder;
    ∃ δ : WithTop ℚ, StableValue A.valuation f δ := by
  letI := A.indexOrder
  apply A.stable_of_not_unstable v f
  intro hu
  exact (not_le_of_gt hf) (A.key.minimal f hu)

/-- A nonlinear minimal unstable polynomial excludes a last index. This
derives the missing no-maximal-index clause from the literal 2024 data. -/
theorem Source2024LimitFamily.noMaxOrder [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ))
    {μ ν : AddValuation K[X] (WithTop ℚ)} {F : K[X]}
    (A : Source2024LimitFamily.{u, uI} (v.comap (algebraMap K E)) μ ν F)
    (hdegree : 1 < F.natDegree) :
    letI := A.indexOrder; NoMaxOrder A.Index := by
  classical
  letI := A.indexOrder
  choose a γ hρ using (fun i =>
    exists_eq_baseBall_of_hasDegree_one v (A.valuation i)
      (A.base_extension i) (A.degree_one i))
  refine ⟨fun i => ?_⟩
  by_contra hn
  have hmax : ∀ j : A.Index, j ≤ i := by
    intro j
    exact le_of_not_gt (fun hij => hn ⟨j, hij⟩)
  have hlinear : ∀ j, A.valuation j (X - C (a i)) = (γ j : WithTop ℚ) := by
    intro j
    have h := A.monotone j i (hmax j)
    rw [hρ j, hρ i] at h
    have hcentre := baseBall_centre_le_of_le v (a j) (a i) (γ j) (γ i) h
    rw [hρ j, baseBall_linear, min_eq_left hcentre]
  have hu : Unstable A.valuation (X - C (a i)) := by
    intro j k hjk
    change A.valuation j (X - C (a i)) < A.valuation k (X - C (a i))
    rw [hlinear, hlinear]
    have h := A.increasing j k hjk
    rw [hρ j, hρ k] at h
    exact_mod_cast baseBall_radius_lt_of_lt v (a j) (a k) (γ j) (γ k) h.1 h.2
  have hmin := A.key.minimal (X - C (a i)) hu
  rw [natDegree_X_sub_C] at hmin
  omega

theorem Source2024LimitFamily.unstable_iff_not_stable [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ))
    {μ ν : AddValuation K[X] (WithTop ℚ)} {F : K[X]}
    (A : Source2024LimitFamily.{u, uI} (v.comap (algebraMap K E)) μ ν F)
    (hdegree : 1 < F.natDegree) (f : K[X]) :
    letI := A.indexOrder;
    Unstable A.valuation f ↔ ¬∃ δ : WithTop ℚ, StableValue A.valuation f δ := by
  letI := A.indexOrder
  letI := A.noMaxOrder v hdegree
  constructor
  · rintro hu ⟨δ, hδ⟩
    exact not_unstable_of_stableValue hδ hu
  · intro h
    by_contra hu
    exact h (A.stable_of_not_unstable v f hu)

theorem Source2024LimitFamily.stable_value_eq
    {v : AddValuation K (WithTop ℚ)}
    {μ ν : AddValuation K[X] (WithTop ℚ)} {F : K[X]}
    (A : Source2024LimitFamily.{u, uI} v μ ν F)
    (f : K[X]) (hf : f.natDegree < F.natDegree) (δ : WithTop ℚ)
    (hδ : letI := A.indexOrder; StableValue A.valuation f δ) : ν f = δ := by
  letI := A.indexOrder
  simpa using A.expansion_formula {0} (fun _ => f) (fun _ => δ)
    (by simpa using hf) (by simpa using hδ)

theorem Source2024LimitFamily.stable_at_endpoint [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ))
    {μ ν : AddValuation K[X] (WithTop ℚ)} {F : K[X]}
    (A : Source2024LimitFamily.{u, uI} (v.comap (algebraMap K E)) μ ν F)
    (f : K[X]) (hf : f.natDegree < F.natDegree) :
    letI := A.indexOrder; StableValue A.valuation f (ν f) := by
  letI := A.indexOrder
  obtain ⟨δ, hδ⟩ := A.stable_below v f hf
  rw [A.stable_value_eq f hf δ hδ]
  exact hδ

theorem Source2024LimitFamily.le_endpoint_below [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ))
    {μ ν : AddValuation K[X] (WithTop ℚ)} {F : K[X]}
    (A : Source2024LimitFamily.{u, uI} (v.comap (algebraMap K E)) μ ν F)
    (i : A.Index) (f : K[X]) (hf : f.natDegree < F.natDegree) :
    A.valuation i f ≤ ν f := by
  letI := A.indexOrder
  obtain ⟨j, hj⟩ := A.stable_at_endpoint v f hf
  exact (A.monotone i (max i j) (le_max_left _ _) f).trans_eq
    (hj (max i j) (le_max_right _ _))

/-- The reverse comparison applies to every family with the actual 2024
quantifiers. It uses neither a cofinal subsequence nor a no-maximal-index
assumption, and does not assume the chosen key values equal endpoint values. -/
theorem Source2024LimitFamily.baseApproximation [IsAlgClosed E]
    [Algebra.IsAlgebraic K E]
    (v : AddValuation E (WithTop ℚ)) (θ : E)
    {μ : AddValuation K[X] (WithTop ℚ)}
    (A : Source2024LimitFamily.{u, uI} (v.comap (algebraMap K E))
      μ (evaluationValuation v θ) (minpoly K θ))
    (hdegree : 1 < (minpoly K θ).natDegree)
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    NTCThird.BaseApproximation K v θ := by
  classical
  letI := A.indexOrder
  intro b hb
  have hbint : IsIntegral K b := (Algebra.IsAlgebraic.isAlgebraic (R := K) b).isIntegral
  have hmon := minpoly.monic hbint
  obtain ⟨i, hi⟩ := A.stable_at_endpoint v (minpoly K b) hb
  obtain ⟨a, γ, hρ⟩ := exists_eq_baseBall_of_hasDegree_one v (A.valuation i)
    (A.base_extension i) (A.degree_one i)
  have hγ : (γ : WithTop ℚ) ≤ v (θ - algebraMap K E a) := by
    have h := A.le_endpoint_below v i (X - C a) (by simpa using hdegree)
    rw [hρ, baseBall_linear_self] at h
    simpa using h
  have hvalue : v (θ - b) ≤ (γ : WithTop ℚ) := by
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hroot : b ∈ (minpoly K b).aroots E :=
      mem_aroots.mpr ⟨hmon.ne_zero, minpoly.aeval K b⟩
    have hstrict := baseBall_lt_evaluation_of_root v θ a γ hγ
      (minpoly K b) hmon.ne_zero b hroot hlt
    have heq := hi i le_rfl
    rw [hρ] at heq
    exact (ne_of_lt hstrict) heq
  obtain ⟨d, hd⟩ := hbetter a
  exact ⟨d, ((hvalue.trans hγ).trans_lt hd).le⟩

/-- A length-one chain in the 2024 presentation. The initial valuation is
the actual finite coefficient-minimum Gauss valuation, and either published
kind of augmentation is permitted. -/
structure Source2024ChainOne (v : AddValuation E (WithTop ℚ)) (θ : E) where
  initial_center : K
  initial_value : ℚ
  endpoint_value : (initial_value : WithTop ℚ) =
    v (θ - algebraMap K E initial_center)
  degree_jump : 1 < (minpoly K θ).natDegree
  step : OrdinaryAugmentation (baseBall v initial_center initial_value)
      (evaluationValuation v θ) (minpoly K θ) ⊤ ∨
    Nonempty (Source2024LimitFamily.{u, uI} (v.comap (algebraMap K E))
      (baseBall v initial_center initial_value) (evaluationValuation v θ) (minpoly K θ))

theorem Source2024ChainOne.baseApproximation [IsAlgClosed E]
    [Algebra.IsAlgebraic K E]
    (v : AddValuation E (WithTop ℚ)) (θ : E)
    (C : Source2024ChainOne.{u, uI, uE} (K := K) v θ)
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    NTCThird.BaseApproximation K v θ := by
  rcases C.step with A | hA
  · exact (no_ordinary_terminal_of_no_max v θ
      (baseBall v C.initial_center C.initial_value) C.initial_center C.initial_value
      (baseBall_initial v C.initial_center C.initial_value) C.endpoint_value
      C.degree_jump hbetter A).elim
  · obtain ⟨A⟩ := hA
    exact A.baseApproximation v θ C.degree_jump hbetter

theorem exists_source2024ChainOne_of_baseApproximation [IsAlgClosed E]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (hθ : IsIntegral K θ)
    (hdegree : 1 < NTCThird.elementDegree K θ)
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d))
    (happrox : NTCThird.BaseApproximation K v θ) :
    Nonempty (Source2024ChainOne.{u, uI, uE} (K := K) v θ) := by
  classical
  obtain ⟨a, γ, hγ, hincr, hcofinal⟩ := exists_cofinal_approximation_sequence v θ hbetter
  let I := ULift.{uI} ℕ
  letI : NoMaxOrder I := ⟨fun i => ⟨ULift.up (i.down + 1), Nat.lt_succ_self i.down⟩⟩
  let a' : I → K := fun i => a i.down
  let γ' : I → ℚ := fun i => γ i.down
  let ρ : I → AddValuation K[X] (WithTop ℚ) := fun i => baseBall v (a' i) (γ' i)
  have hγ' : ∀ i, (γ' i : WithTop ℚ) = v (θ - algebraMap K E (a' i)) :=
    fun i => hγ i.down
  have hincr' : StrictMono γ' := fun _ _ hij => hincr hij
  have hcofinal' : ∀ c : K, ∃ i, v (θ - algebraMap K E c) ≤ (γ' i : WithTop ℚ) := by
    intro c
    obtain ⟨n, hn⟩ := hcofinal c
    exact ⟨ULift.up n, hn⟩
  let μ' : ∀ i, LinearMonomialValuation v (algebraMap K E (a' i)) (γ' i) :=
    fun i => linearMonomialValuation v (algebraMap K E (a' i)) (γ' i)
  have hstable : ∀ f : K[X], f.natDegree < (minpoly K θ).natDegree →
      StableValue ρ f (v (aeval θ f)) := by
    intro f hf
    exact stable_evaluation_of_baseApproximation v θ a' γ' hγ' hincr' hcofinal'
      happrox μ' f hf
  have hkey : LimitKeyPolynomial ρ (minpoly K θ) :=
    minpoly_limitKey_of_baseApproximation v θ hθ a' γ' hγ' hincr' hcofinal' happrox μ'
  let A : Source2024LimitFamily.{u, uI} (v.comap (algebraMap K E))
      (baseBall v (a 0) (γ 0)) (evaluationValuation v θ) (minpoly K θ) := {
    Index := I
    indexOrder := inferInstance
    indexWellFounded := inferInstance
    indexInfinite := inferInstance
    first := ULift.up 0
    first_le := fun i => Nat.zero_le i.down
    valuation := ρ
    first_valuation := rfl
    base_extension := fun i c => baseBall_C v (a' i) c (γ' i)
    degree_one := fun i => baseBall_hasDegree_one v (a' i) (γ' i)
    increasing := by
      intro i j hij
      exact ⟨restrictedMonomial_family_le v θ a' γ' hγ' hincr'.monotone μ' hij.le,
        restrictedMonomial_family_strict v θ a' γ' hγ' hincr' μ' hij⟩
    key := hkey
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
  exact ⟨⟨a 0, γ 0, hγ 0, hdegree, Or.inr ⟨A⟩⟩⟩

/-- Existential length-one equivalence, for an arbitrary universe of the
well-ordered source index. The reverse covers every source family. -/
theorem source2024ChainOne_iff_finiteMLVChain_one [IsAlgClosed E]
    [Algebra.IsAlgebraic K E]
    (v : AddValuation E (WithTop ℚ)) (θ : E)
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    Nonempty (Source2024ChainOne.{u, uI, uE} (K := K) v θ) ↔
      Nonempty (FiniteMLVChain (v.comap (algebraMap K E))
        (evaluationValuation v θ) (minpoly K θ) 1) := by
  rw [finiteMLVChain_one_iff v θ hbetter]
  constructor
  · rintro ⟨C⟩
    exact ⟨C.degree_jump, C.baseApproximation v θ hbetter⟩
  · rintro ⟨hdegree, happrox⟩
    exact exists_source2024ChainOne_of_baseApproximation v θ
      (Algebra.IsAlgebraic.isAlgebraic (R := K) θ).isIntegral hdegree hbetter happrox

/-- The minimum still ranges over every primitive generator. Only the
length-one witness is replaced by the other published presentation. -/
theorem minimum_mlvLength_one_iff_source2024 [IsAlgClosed E]
    [Algebra.IsAlgebraic K E]
    (v : AddValuation E (WithTop ℚ)) (L : IntermediateField K E)
    (hL : L ≠ ⊥)
    (hbetter : ∀ θ : E, K⟮θ⟯ = L → ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    IsLeast (realizedMLVLengths K v L) 1 ↔
      ∃ θ : E, K⟮θ⟯ = L ∧ Nonempty (Source2024ChainOne.{u, uI, uE} (K := K) v θ) := by
  constructor
  · intro h
    obtain ⟨θ, hθ, C⟩ := h.1
    exact ⟨θ, hθ, (source2024ChainOne_iff_finiteMLVChain_one v θ (hbetter θ hθ)).mpr C⟩
  · rintro ⟨θ, hθ, C⟩
    refine ⟨⟨θ, hθ,
      (source2024ChainOne_iff_finiteMLVChain_one v θ (hbetter θ hθ)).mp C⟩, ?_⟩
    intro r hr
    have hz : r ≠ 0 := by
      intro heq
      subst r
      exact zero_not_mem_realizedMLVLengths K v L hL hr
    omega

end NTCThird.MLV
