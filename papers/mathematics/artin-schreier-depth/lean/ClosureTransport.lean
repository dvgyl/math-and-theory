import HenselianKrasner
import OkutsuDepth

/-!
# Actual valued embeddings into the base algebraic closure

The source Okutsu criterion belongs in an algebraic closure. This file
constructs an actual embedding of an algebraic valued extension into that
closure and proves that the valuation is preserved by genuine uniqueness of
extensions. Actual minimal polynomials and their degrees are preserved.

The transport theorems only compare elements of an algebraic extension M/K.
They do not specialize Okutsu sequences to the full transcendental Hahn
field, and they do not assume or rename the unformalized comparison with
Mac Lane--Vaquie depth.
-/

noncomputable section

open IntermediateField

namespace NTCThird

universe u

section Embedding

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
    [Algebra.IsAlgebraic K M]

/-- An actual K-algebra embedding of the algebraic extension M into the
specified algebraic closure of K. It is supplied by mathlib's extension
embedding construction, not a freely assumed map. -/
def algebraicClosureEmbedding : M →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift

/-- Choose the actual unique extending rational valuation on the base
algebraic closure using the valued-henselian existence property. -/
def henselianClosureValuation (vK : AddValuation K (WithTop ℚ))
    (hK : RationalValuedHenselian vK) : AddValuation (AlgebraicClosure K) (WithTop ℚ) :=
  Classical.choose (hK (AlgebraicClosure K))

theorem henselianClosureValuation_extends (vK : AddValuation K (WithTop ℚ))
    (hK : RationalValuedHenselian vK) (a : K) :
    henselianClosureValuation vK hK (algebraMap K (AlgebraicClosure K) a) = vK a :=
  (Classical.choose_spec (hK (AlgebraicClosure K))).1 a

/-- Any actual embedding into any valued extension of K preserves the chosen
valuation on algebraic M when both valuations extend the same henselian base.
The uniqueness is used on M itself, where every element is algebraic. -/
theorem valuation_pullback_eq_of_henselian
    {A : Type*} [Field A] [Algebra K A]
    (vK : AddValuation K (WithTop ℚ)) (hK : RationalValuedHenselian vK)
    (vM : AddValuation M (WithTop ℚ))
    (hM : ∀ a : K, vM (algebraMap K M a) = vK a)
    (w : AddValuation A (WithTop ℚ))
    (hw : ∀ a : K, w (algebraMap K A a) = vK a)
    (ι : M →ₐ[K] A) : w.comap ι.toRingHom = vM := by
  apply hK.uniqueExtension
  · intro a
    change w (ι (algebraMap K M a)) = vK a
    rw [ι.commutes, hw]
  · exact hM

theorem valuation_embedding_apply_of_henselian
    {A : Type*} [Field A] [Algebra K A]
    (vK : AddValuation K (WithTop ℚ)) (hK : RationalValuedHenselian vK)
    (vM : AddValuation M (WithTop ℚ))
    (hM : ∀ a : K, vM (algebraMap K M a) = vK a)
    (w : AddValuation A (WithTop ℚ))
    (hw : ∀ a : K, w (algebraMap K A a) = vK a)
    (ι : M →ₐ[K] A) (x : M) : w (ι x) = vM x :=
  congrArg (fun v : AddValuation M (WithTop ℚ) => v x)
    (valuation_pullback_eq_of_henselian vK hK vM hM w hw ι)

/-- The constructed algebraic-closure embedding preserves the actual valued
field structure, pointwise on every element of M. -/
theorem henselianClosureValuation_embedding
    (vK : AddValuation K (WithTop ℚ)) (hK : RationalValuedHenselian vK)
    (vM : AddValuation M (WithTop ℚ))
    (hM : ∀ a : K, vM (algebraMap K M a) = vK a) (x : M) :
    henselianClosureValuation vK hK (algebraicClosureEmbedding (K := K) x) = vM x :=
  valuation_embedding_apply_of_henselian vK hK vM hM _
    (henselianClosureValuation_extends vK hK) algebraicClosureEmbedding x

/-- The requested actual embedding and valuation exist together, with the
base-extension and pointwise valuation assertions both proved. -/
theorem exists_valued_embedding_algebraicClosure
    (vK : AddValuation K (WithTop ℚ)) (hK : RationalValuedHenselian vK)
    (vM : AddValuation M (WithTop ℚ))
    (hM : ∀ a : K, vM (algebraMap K M a) = vK a) :
    ∃ ι : M →ₐ[K] AlgebraicClosure K,
      ∃ w : AddValuation (AlgebraicClosure K) (WithTop ℚ),
        (∀ a : K, w (algebraMap K (AlgebraicClosure K) a) = vK a) ∧
        ∀ x : M, w (ι x) = vM x :=
  ⟨algebraicClosureEmbedding, henselianClosureValuation vK hK,
    henselianClosureValuation_extends vK hK,
    henselianClosureValuation_embedding vK hK vM hM⟩

end Embedding

section Degrees

variable {K M A : Type*} [Field K] [Field M] [Field A]
    [Algebra K M] [Algebra K A]

/-- The actual minimal polynomial is unchanged under an injective field
homomorphism fixing the base; this is mathlib's minpoly functoriality. -/
theorem minpoly_embedding_eq (ι : M →ₐ[K] A) (x : M) :
    minpoly K (ι x) = minpoly K x := minpoly.algHom_eq ι ι.injective x

/-- Consequently the actual algebraic element degree is unchanged. -/
theorem elementDegree_algHom (ι : M →ₐ[K] A) (x : M) :
    elementDegree K (ι x) = elementDegree K x := by
  unfold elementDegree
  rw [minpoly_embedding_eq ι x]

end Degrees

section Criterion

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
    [Algebra.IsAlgebraic K M]

/-- The genuine algebraic-closure lower-degree approximation condition
implies the condition on elements of the actual algebraic subextension M.
This is deliberately one-way: M need not contain every algebraic approximant. -/
theorem baseApproximation_internal_of_closure
    (ι : M →ₐ[K] AlgebraicClosure K)
    (vM : AddValuation M (WithTop ℚ))
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hval : ∀ x : M, w (ι x) = vM x)
    (θ : M) (happ : BaseApproximation K w (ι θ)) :
    BaseApproximation K vM θ := by
  intro b hb
  have hdegree : elementDegree K (ι b) < elementDegree K (ι θ) := by
    simpa only [elementDegree_algHom] using hb
  obtain ⟨a, ha⟩ := happ (ι b) hdegree
  refine ⟨a, ?_⟩
  have hbval : w (ι θ - ι b) = vM (θ - b) := by
    rw [← map_sub ι θ b, hval]
  have haval : w (ι θ - algebraMap K (AlgebraicClosure K) a) =
      vM (θ - algebraMap K M a) := by
    rw [← ι.commutes a, ← map_sub ι θ (algebraMap K M a), hval]
  rwa [hbval, haval] at ha

/-- An actual length-one Okutsu sequence in the algebraic closure yields
an internal length-one sequence on algebraic M, via the proved criterion.
No identification of these lengths with MLV depth is made here. -/
theorem okutsuSequence_one_internal_of_closure
    (ι : M →ₐ[K] AlgebraicClosure K)
    (vM : AddValuation M (WithTop ℚ))
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hval : ∀ x : M, w (ι x) = vM x)
    (θ : M) (hs : Nonempty (OkutsuSequence K w (ι θ) 1)) :
    Nonempty (OkutsuSequence K vM θ 1) := by
  obtain ⟨hdegree, happ⟩ := (okutsuSequence_one_iff K w (ι θ)).mp hs
  apply (okutsuSequence_one_iff K vM θ).mpr
  exact ⟨by simpa only [elementDegree_algHom] using hdegree,
    baseApproximation_internal_of_closure ι vM w hval θ happ⟩

/-- An actual lower-degree obstruction inside algebraic M rules out the
source's length-one Okutsu sequence in the full algebraic closure. -/
theorem not_closure_okutsuSequence_one_of_internal_obstruction
    (ι : M →ₐ[K] AlgebraicClosure K)
    (vM : AddValuation M (WithTop ℚ))
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hval : ∀ x : M, w (ι x) = vM x)
    (θ α : M) (hdegree : elementDegree K α < elementDegree K θ)
    (hsep : ∀ a : K, vM (θ - algebraMap K M a) < vM (θ - α)) :
    ¬Nonempty (OkutsuSequence K w (ι θ) 1) := by
  intro hs
  exact not_okutsuSequence_one_of_lower_degree K vM θ α hdegree hsep
    (okutsuSequence_one_internal_of_closure ι vM w hval θ hs)

/-- A contained internal first-block field that beats every base
approximation must equal the generator field if the actual embedded generator
has a length-one Okutsu sequence in the base algebraic closure. -/
theorem adjoin_eq_of_closure_okutsuSequence_one
    (ι : M →ₐ[K] AlgebraicClosure K)
    (vM : AddValuation M (WithTop ℚ))
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hval : ∀ x : M, w (ι x) = vM x)
    (θ α : M) (hs : Nonempty (OkutsuSequence K w (ι θ) 1))
    (hsub : K⟮α⟯ ≤ K⟮θ⟯)
    (hsep : ∀ a : K, vM (θ - algebraMap K M a) < vM (θ - α)) :
    K⟮α⟯ = K⟮θ⟯ :=
  adjoin_eq_of_okutsuSequence_one K vM θ α
    (Algebra.IsIntegral.isIntegral θ) (Algebra.IsIntegral.isIntegral α)
    (okutsuSequence_one_internal_of_closure ι vM w hval θ hs) hsub hsep

/-- Direct packaged form using the constructed valued algebraic-closure
embedding, rather than assuming any valuation isometry. -/
theorem adjoin_eq_of_henselian_closure_okutsuSequence_one
    (vK : AddValuation K (WithTop ℚ)) (hK : RationalValuedHenselian vK)
    (vM : AddValuation M (WithTop ℚ))
    (hM : ∀ a : K, vM (algebraMap K M a) = vK a)
    (θ α : M)
    (hs : Nonempty (OkutsuSequence K (henselianClosureValuation vK hK)
      (algebraicClosureEmbedding (K := K) θ) 1))
    (hsub : K⟮α⟯ ≤ K⟮θ⟯)
    (hsep : ∀ a : K, vM (θ - algebraMap K M a) < vM (θ - α)) :
    K⟮α⟯ = K⟮θ⟯ :=
  adjoin_eq_of_closure_okutsuSequence_one algebraicClosureEmbedding vM _
    (henselianClosureValuation_embedding vK hK vM hM) θ α hs hsub hsep

/-- The actual minimum over all primitive generators of the embedded field
in the algebraic closure supplies a primitive generator in M itself, with
its genuine algebraic-closure Okutsu sequence retained. -/
theorem exists_primitive_generator_of_closure_minimum
    (ι : M →ₐ[K] AlgebraicClosure K)
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hmin : IsLeast (realizedOkutsuLengths K w ι.fieldRange) 1) :
    ∃ θ : M, K⟮θ⟯ = ⊤ ∧ Nonempty (OkutsuSequence K w (ι θ) 1) := by
  obtain ⟨θA, hgenA, hsA⟩ := hmin.1
  have hmem : θA ∈ ι.fieldRange :=
    hgenA ▸ IntermediateField.mem_adjoin_simple_self K θA
  obtain ⟨θ, hθ⟩ := AlgHom.mem_fieldRange.mp hmem
  have hgen : K⟮θ⟯ = ⊤ := by
    apply IntermediateField.map_injective ι
    calc
      (K⟮θ⟯).map ι = K⟮ι θ⟯ := by
        rw [IntermediateField.adjoin_map, Set.image_singleton]
      _ = ι.fieldRange := by simpa only [hθ] using hgenA
      _ = (⊤ : IntermediateField K M).map ι := ι.fieldRange_eq_map
  exact ⟨θ, hgen, by simpa only [hθ] using hsA⟩

/-- The intrinsic minimum in the actual algebraic closure yields the
internal approximation criterion for a genuine primitive generator, using
only the constructed valued embedding and uniqueness of extensions. -/
theorem exists_generator_criterion_of_henselian_closure_minimum
    (vK : AddValuation K (WithTop ℚ)) (hK : RationalValuedHenselian vK)
    (vM : AddValuation M (WithTop ℚ))
    (hM : ∀ a : K, vM (algebraMap K M a) = vK a)
    (hmin : IsLeast (realizedOkutsuLengths K (henselianClosureValuation vK hK)
      (algebraicClosureEmbedding (K := K) (M := M)).fieldRange) 1) :
    ∃ θ : M, K⟮θ⟯ = ⊤ ∧ BaseApproximation K vM θ := by
  obtain ⟨θ, hgen, hs⟩ := exists_primitive_generator_of_closure_minimum
    algebraicClosureEmbedding (henselianClosureValuation vK hK) hmin
  refine ⟨θ, hgen, ?_⟩
  exact baseApproximation_internal_of_closure algebraicClosureEmbedding vM _
    (henselianClosureValuation_embedding vK hK vM hM) θ
    ((okutsuSequence_one_iff K _ _).mp hs).2

end Criterion

end NTCThird
