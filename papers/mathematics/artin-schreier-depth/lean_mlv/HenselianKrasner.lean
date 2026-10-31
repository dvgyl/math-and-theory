import LegacyCompat
import HahnSupport

/-!
# Krasner containment from genuine valuation-extension uniqueness

This file proves the valued Galois-theoretic core of Krasner's lemma. The input
is an actual additive valuation on a Galois ambient field. Its invariance can be
derived from an actual uniqueness assertion for extensions of the base
valuation. No `IsKrasner` class or conclusion-shaped field-containment input is
used.

The implication from henselianity of the valuation ring to valuation-extension
uniqueness is NOT established in this file. In particular, the automatic
`HenselianLocalRing` instance on a field is not used. All results here are
standard mathematics, with no novelty claim.
-/

noncomputable section

set_option maxHeartbeats 600000

open IntermediateField Polynomial

namespace NTCThird

variable {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
  [LinearOrderedAddCommMonoidWithTop Γ]

/-- Actual uniqueness of Γ-valued extensions to the specified extension field.
This definition does not assert a Krasner conclusion or a field containment.
Existence is supplied separately by an explicit extending valuation. -/
def UniqueAddValuationExtension (vK : AddValuation K Γ) (L : Type*)
    [Field L] [Algebra K L] : Prop :=
  ∀ v₁ v₂ : AddValuation L Γ,
    (∀ x : K, v₁ (algebraMap K L x) = vK x) →
    (∀ x : K, v₂ (algebraMap K L x) = vK x) → v₁ = v₂

/-- Uniqueness of actual valuation extensions forces every base automorphism
to preserve the chosen extension valuation. -/
theorem addValuation_invariant_of_unique_extension
    (vK : AddValuation K Γ) (v : AddValuation L Γ)
    (hext : ∀ x : K, v (algebraMap K L x) = vK x)
    (hunique : UniqueAddValuationExtension vK L)
    (σ : L ≃ₐ[K] L) (x : L) : v (σ x) = v x := by
  have hext' : ∀ a : K, (v.comap σ.toRingEquiv.toRingHom) (algebraMap K L a) = vK a := by
    intro a
    change v (σ (algebraMap K L a)) = vK a
    rw [σ.commutes, hext]
  have heq : v.comap σ.toRingEquiv.toRingHom = v := hunique _ _ hext' hext
  exact congrArg (fun w : AddValuation L Γ => w x) heq

/-- The actual Krasner field-membership conclusion in an arbitrary (possibly
infinite) Galois ambient extension, with an invariant additive valuation. -/
theorem krasner_mem_of_invariant_valuation [IsGalois K L]
    (v : AddValuation L Γ)
    (hinv : ∀ (σ : L ≃ₐ[K] L) (x : L), v (σ x) = v x)
    (α β : L)
    (hclose : ∀ σ : L ≃ₐ[K] L, σ α ≠ α → v (α - σ α) < v (α - β)) :
    α ∈ K⟮β⟯ := by
  classical
  rw [← InfiniteGalois.fixedField_fixingSubgroup K⟮β⟯]
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hβ : σ β = β := by
    have hfix := (IntermediateField.mem_fixingSubgroup_iff K⟮β⟯ σ).mp hσ
    exact hfix β (IntermediateField.mem_adjoin_simple_self K β)
  by_cases hα : σ α = α
  · exact hα
  exfalso
  have hstrict := hclose σ hα
  have hσdiff : v (σ α - β) = v (α - β) := by
    calc
      v (σ α - β) = v (σ (α - β)) := by rw [map_sub σ α β, hβ]
      _ = v (α - β) := hinv σ (α - β)
  have hbound : v (α - β) ≤ v (α - σ α) := by
    have h := v.map_sub (α - β) (σ α - β)
    rw [hσdiff, min_self] at h
    convert h using 1
    congr 1
    ring
  exact (not_lt_of_ge hbound) hstrict

theorem krasner_adjoin_le_of_invariant_valuation [IsGalois K L]
    (v : AddValuation L Γ)
    (hinv : ∀ (σ : L ≃ₐ[K] L) (x : L), v (σ x) = v x)
    (α β : L)
    (hclose : ∀ σ : L ≃ₐ[K] L, σ α ≠ α → v (α - σ α) < v (α - β)) :
    K⟮α⟯ ≤ K⟮β⟯ :=
  IntermediateField.adjoin_simple_le_iff.mpr
    (krasner_mem_of_invariant_valuation v hinv α β hclose)

/-- A root-language version of the same actual containment statement. -/
theorem krasner_mem_of_conjugate_distances [IsGalois K L]
    (v : AddValuation L Γ)
    (hinv : ∀ (σ : L ≃ₐ[K] L) (x : L), v (σ x) = v x)
    (α β : L)
    (hclose : ∀ α' : L, IsConjRoot K α α' → α' ≠ α →
      v (α - α') < v (α - β)) : α ∈ K⟮β⟯ := by
  apply krasner_mem_of_invariant_valuation v hinv α β
  intro σ hσ
  exact hclose (σ α) (isConjRoot_of_algEquiv α σ) hσ

/-- The uniqueness formulation, without assuming valuation invariance or
Krasner's lemma as an independent class. -/
theorem krasner_mem_of_unique_valuation_extension [IsGalois K L]
    (vK : AddValuation K Γ) (v : AddValuation L Γ)
    (hext : ∀ x : K, v (algebraMap K L x) = vK x)
    (hunique : UniqueAddValuationExtension vK L)
    (α β : L)
    (hclose : ∀ σ : L ≃ₐ[K] L, σ α ≠ α → v (α - σ α) < v (α - β)) :
    α ∈ K⟮β⟯ :=
  krasner_mem_of_invariant_valuation v
    (addValuation_invariant_of_unique_extension vK v hext hunique) α β hclose

/-- Exact cutoff form used for the normalized first block. The common
conjugate distance is a hypothesis to be discharged by the actual additive
polynomial and Hahn monomial calculation. -/
theorem krasner_mem_of_constant_conjugate_cut [IsGalois K L]
    (v : AddValuation L Γ)
    (hinv : ∀ (σ : L ≃ₐ[K] L) (x : L), v (σ x) = v x)
    (α β : L) (δ : Γ)
    (hconj : ∀ σ : L ≃ₐ[K] L, σ α ≠ α → v (α - σ α) = δ)
    (hclose : δ < v (α - β)) : α ∈ K⟮β⟯ := by
  apply krasner_mem_of_invariant_valuation v hinv α β
  intro σ hσ
  rw [hconj σ hσ]
  exact hclose

/-! ## The unique-extension characterization of valued henselianity

For rational-valued fields we use the standard unique-extension
characterization with all quantifiers visible: for every algebraic extension,
there exists exactly one rational-valued additive valuation extending the
specified base valuation pointwise. The value-group normalization is fixed by
pointwise equality on the base field. This is a property of a valued field,
not the automatic `HenselianLocalRing` instance on a field.

We do not formalize the classical equivalence between this characterization
and simple-root lifting in the valuation ring. In an algebraic extension all
nonzero values are commensurable with base values; this is why the usual
uniqueness up to equivalence gives pointwise uniqueness for this fixed
rational normalization. That commensurability equivalence is also not proved
in this file.
-/

universe u

/-- The full rational-valued unique-extension characterization, including
existence and uniqueness in every algebraic extension in the base universe. -/
def RationalValuedHenselian {F : Type u} [Field F]
    (vF : AddValuation F (WithTop ℚ)) : Prop :=
  ∀ (E : Type u) [Field E] [Algebra F E] [Algebra.IsAlgebraic F E],
    ∃! vE : AddValuation E (WithTop ℚ),
      ∀ x : F, vE (algebraMap F E x) = vF x

theorem RationalValuedHenselian.uniqueExtension
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]
    {vF : AddValuation F (WithTop ℚ)} (hF : RationalValuedHenselian vF) :
    UniqueAddValuationExtension vF E := by
  obtain ⟨vE, _, huniq⟩ := hF E
  intro v₁ v₂ h₁ h₂
  exact (huniq v₁ h₁).trans (huniq v₂ h₂).symm

/-- Actual Krasner containment under the quantified valued-henselian
unique-extension characterization. -/
theorem krasner_mem_of_rationalValuedHenselian
    {F E : Type u} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    (vF : AddValuation F (WithTop ℚ)) (vE : AddValuation E (WithTop ℚ))
    (hext : ∀ x : F, vE (algebraMap F E x) = vF x)
    (hF : RationalValuedHenselian vF) (α β : E)
    (hclose : ∀ σ : E ≃ₐ[F] E, σ α ≠ α → vE (α - σ α) < vE (α - β)) :
    α ∈ F⟮β⟯ :=
  krasner_mem_of_unique_valuation_extension vF vE hext hF.uniqueExtension α β hclose

section Constants

variable {k : Type*} [Field k] [Algebra k K] [Algebra k L]
  [IsScalarTower k K L] [IsAlgClosed k]

include k

/-- A root of unity in an extension of algebraically closed constants is
itself a constant. -/
theorem rootOfUnity_mem_constant_range {n : ℕ} (hn : 0 < n) (x : L)
    (hx : x ^ n = 1) : ∃ c : k, algebraMap k L c = x := by
  let P : k[X] := Polynomial.X ^ n - Polynomial.C 1
  have hP : P ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hn 1
  have hroot : Polynomial.aeval x P = 0 := by simp [P, hx]
  have hi : IsIntegral k x := (show IsAlgebraic k x from ⟨P, hP, hroot⟩).isIntegral
  exact hi.mem_range_algebraMap_of_minpoly_splits (IsAlgClosed.splits_domain _)

/-- Once one radical is present, its polynomial splits over a field
containing algebraically closed constants. This includes inseparable
polynomials: separability will come separately from the perfect base. -/
theorem kummer_polynomial_splits (α : L) (hα : α ≠ 0) (n : ℕ) :
    (X ^ n - C (α ^ n) : L[X]).Splits := by
  have hs : (X ^ n - 1 : L[X]).Splits := by
    have hk : ((X ^ n - C (1 : k)).map (algebraMap k L)).Splits :=
      IsAlgClosed.splits_domain _
    simpa using hk
  have hc := hs.comp_of_degree_le_one (degree_C_mul_X_le (α⁻¹))
  have hm := (Splits.C (α ^ n)).mul hc
  convert hm using 1
  rw [sub_comp, pow_comp, X_comp, one_comp, mul_sub, mul_pow,
    ← C_pow, ← mul_assoc, ← C_mul, ← mul_pow, mul_inv_cancel₀ hα,
    one_pow, C_1, one_mul, mul_one]

/-- A field generated by a radical over algebraically closed constants is
an actual splitting field of its radical polynomial. -/
theorem kummer_isSplittingField
    (α : L) (hα : α ≠ 0) (n : ℕ) (hn : 0 < n) (a : K)
    (hpow : α ^ n = algebraMap K L a) (hgen : K⟮α⟯ = ⊤) :
    IsSplittingField K L (X ^ n - C a) := by
  have hnz : (X ^ n - C a : K[X]) ≠ 0 := X_pow_sub_C_ne_zero hn a
  have hroot : aeval α (X ^ n - C a : K[X]) = 0 := by simp [hpow]
  have hint : IsIntegral K α :=
    (show IsAlgebraic K α from ⟨X ^ n - C a, hnz, hroot⟩).isIntegral
  have hg : Algebra.adjoin K ({α} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral hint,
      hgen, IntermediateField.top_toSubalgebra]
  constructor
  · rw [Polynomial.map_sub, Polynomial.map_pow,
      map_X, map_C, ← hpow]
    exact kummer_polynomial_splits (k := k) α hα n
  · apply top_unique
    rw [← hg]
    apply Algebra.adjoin_mono
    rw [Set.singleton_subset_iff, mem_rootSet_of_ne hnz]
    exact hroot

/-- Perfection of the base supplies separability even when the chosen
radical equation has exponent divisible by the characteristic. -/
theorem kummer_isGalois [PerfectField K]
    (α : L) (hα : α ≠ 0) (n : ℕ) (hn : 0 < n) (a : K)
    (hpow : α ^ n = algebraMap K L a) (hgen : K⟮α⟯ = ⊤) :
    IsGalois K L := by
  letI : IsSplittingField K L (X ^ n - C a) :=
    kummer_isSplittingField (k := k) α hα n hn a hpow hgen
  letI : Normal K L := Normal.of_isSplittingField (X ^ n - C a)
  exact { to_isSeparable := inferInstance, to_normal := inferInstance }

/-- All distinct conjugates of a Kummer element over algebraically closed,
trivially valued constants have distance equal to its own value. No
prime-to-characteristic assumption is needed for this distance calculation. -/
theorem kummer_conjugate_distance
    (v : AddValuation L Γ)
    (hconst : ∀ c : k, c ≠ 0 → v (algebraMap k L c) = 0)
    (α : L) (hα : α ≠ 0) (n : ℕ) (hn : 0 < n) (a : K)
    (hpow : α ^ n = algebraMap K L a)
    (σ : L ≃ₐ[K] L) (hσ : σ α ≠ α) : v (α - σ α) = v α := by
  have hratio : (σ α / α) ^ n = 1 := by
    rw [div_pow, ← map_pow σ α n, hpow, σ.commutes]
    exact div_self (hpow ▸ pow_ne_zero n hα)
  obtain ⟨c, hc⟩ := rootOfUnity_mem_constant_range (k := k) hn (σ α / α) hratio
  have hσα : σ α = α * algebraMap k L c := by
    rw [hc, mul_div_cancel₀ _ hα]
  have hc1 : c ≠ 1 := by
    intro heq
    apply hσ
    simpa [heq] using hσα
  have hdiff : α - σ α = α * algebraMap k L (1 - c) := by
    rw [hσα, map_sub, map_one]
    ring
  rw [hdiff, v.map_mul, hconst (1 - c) (sub_ne_zero.mpr hc1.symm), add_zero]

/-- Kummer rigidity from the actual Krasner argument: an element whose
positive power belongs to the base and whose relative error from a base
element has positive value already belongs to the base. This is the
monomial step used in the Hahn-series argument. -/
theorem kummer_mem_base_of_close [IsGalois K L]
    (v : AddValuation L Γ)
    (hinv : ∀ (σ : L ≃ₐ[K] L) (x : L), v (σ x) = v x)
    (hconst : ∀ c : k, c ≠ 0 → v (algebraMap k L c) = 0)
    (α : L) (hα : α ≠ 0) (n : ℕ) (hn : 0 < n) (a b : K)
    (hpow : α ^ n = algebraMap K L a)
    (hclose : v α < v (α - algebraMap K L b)) :
    ∃ c : K, algebraMap K L c = α := by
  have hmem := krasner_mem_of_constant_conjugate_cut v hinv α
    (algebraMap K L b) (v α)
    (fun σ hσ => kummer_conjugate_distance v hconst α hα n hn a hpow σ hσ) hclose
  have hbot : K⟮algebraMap K L b⟯ = ⊥ :=
    IntermediateField.adjoin_simple_eq_bot_iff.mpr
      (IntermediateField.mem_bot.mpr ⟨b, rfl⟩)
  rw [hbot, IntermediateField.mem_bot] at hmem
  exact hmem

end Constants

/-- Kummer rigidity in an arbitrary ambient extension. The proof constructs
the actual simple extension, proves it Galois, restricts the ambient valuation,
and uses the quantified valued-henselian uniqueness property. Thus no
normality or invariance assumption on the ambient extension is required. -/
theorem kummer_mem_base_of_rationalValuedHenselian
    {F E : Type u} [Field F] [Field E] [Algebra F E] [PerfectField F]
    {k : Type*} [Field k] [Algebra k F] [Algebra k E]
    [IsScalarTower k F E] [IsAlgClosed k]
    (vF : AddValuation F (WithTop ℚ)) (vE : AddValuation E (WithTop ℚ))
    (hext : ∀ x : F, vE (algebraMap F E x) = vF x)
    (hF : RationalValuedHenselian vF)
    (hconst : ∀ c : k, c ≠ 0 → vE (algebraMap k E c) = 0)
    (α : E) (hα : α ≠ 0) (n : ℕ) (hn : 0 < n) (a b : F)
    (hpow : α ^ n = algebraMap F E a)
    (hclose : vE α < vE (α - algebraMap F E b)) :
    ∃ c : F, algebraMap F E c = α := by
  let S : IntermediateField F E := F⟮α⟯
  let αS : S := AdjoinSimple.gen F α
  have hnz : (X ^ n - C a : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hn a
  have hint : IsIntegral F α :=
    (show IsAlgebraic F α from ⟨X ^ n - C a, hnz, by simp [hpow]⟩).isIntegral
  letI : Algebra.IsAlgebraic F S := IntermediateField.isAlgebraic_adjoin_simple hint
  letI : Algebra k S := ((algebraMap F S).comp (algebraMap k F)).toAlgebra
  letI : IsScalarTower k F S := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k S E := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k E c = algebraMap F E (algebraMap k F c)
    exact IsScalarTower.algebraMap_apply k F E c
  have hαS : αS ≠ 0 := by
    intro h
    apply hα
    exact congrArg (fun x : S => (x : E)) h
  have hpowS : αS ^ n = algebraMap F S a := by
    apply Subtype.ext
    exact hpow
  have hgen : F⟮αS⟯ = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra F _ (IntermediateField.adjoin.powerBasis hint).adjoin_gen_eq_top
  letI : IsGalois F S := kummer_isGalois (k := k) αS hαS n hn a hpowS hgen
  let vS : AddValuation S (WithTop ℚ) := vE.comap S.val.toRingHom
  have hextS : ∀ x : F, vS (algebraMap F S x) = vF x := hext
  have hconstS : ∀ c : k, c ≠ 0 → vS (algebraMap k S c) = 0 := by
    intro c hc
    change vE (algebraMap S E (algebraMap k S c)) = 0
    rw [← IsScalarTower.algebraMap_apply k S E]
    exact hconst c hc
  have hinv := addValuation_invariant_of_unique_extension vF vS hextS hF.uniqueExtension
  obtain ⟨c, hc⟩ := kummer_mem_base_of_close vS hinv hconstS αS hαS n hn a b hpowS hclose
  exact ⟨c, congrArg (fun x : S => (x : E)) hc⟩

/-- In an actual Galois valued extension, a base-approximable element is
fixed by every automorphism and therefore belongs to the base. No bound on
all conjugates at once, completeness or density theorem is assumed. -/
theorem mem_base_of_arbitrarily_close_in_galois
    {F E : Type*} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    (v : AddValuation E (WithTop ℚ))
    (hinv : ∀ (σ : E ≃ₐ[F] E) (x : E), v (σ x) = v x)
    (θ : E)
    (happrox : ∀ q : ℚ, ∃ a : F, (q : WithTop ℚ) < v (θ - algebraMap F E a)) :
    ∃ a : F, algebraMap F E a = θ := by
  classical
  apply IntermediateField.mem_bot.mp
  rw [← InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField F E)]
  rw [IntermediateField.mem_fixedField_iff]
  intro σ _
  by_cases hσ : σ θ = θ
  · exact hσ
  exfalso
  have hne : θ - σ θ ≠ 0 := sub_ne_zero.mpr (fun h => hσ h.symm)
  have htop : v (θ - σ θ) ≠ ⊤ := by
    intro h
    exact hne (v.top_iff.mp h)
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp htop
  obtain ⟨a, ha⟩ := happrox q
  have hσdiff : v (σ θ - algebraMap F E a) = v (θ - algebraMap F E a) := by
    calc
      _ = v (σ (θ - algebraMap F E a)) := by
        rw [map_sub σ θ (algebraMap F E a), σ.commutes]
      _ = _ := hinv σ _
  have hle : v (θ - algebraMap F E a) ≤ v (θ - σ θ) := by
    have h := v.map_sub (θ - algebraMap F E a) (σ θ - algebraMap F E a)
    rw [hσdiff, min_self] at h
    convert h using 1
    congr 1
    ring
  rw [← hq] at hle
  exact (not_lt_of_ge hle) ha

/-- A perfect valued-henselian field is relatively algebraically closed
among elements of an arbitrary valued extension that can be approximated
arbitrarily well by base elements. The proof actually constructs an algebraic
closure of the simple extension and transports the original valuation by
uniqueness. No normality assumption on the ambient field is needed. -/
theorem algebraic_mem_base_of_arbitrarily_close
    {F E : Type u} [Field F] [Field E] [Algebra F E] [PerfectField F]
    (vF : AddValuation F (WithTop ℚ)) (vE : AddValuation E (WithTop ℚ))
    (hext : ∀ a : F, vE (algebraMap F E a) = vF a)
    (hF : RationalValuedHenselian vF)
    (θ : E) (hint : IsIntegral F θ)
    (happrox : ∀ q : ℚ, ∃ a : F, (q : WithTop ℚ) < vE (θ - algebraMap F E a)) :
    ∃ a : F, algebraMap F E a = θ := by
  let S : IntermediateField F E := F⟮θ⟯
  let θS : S := AdjoinSimple.gen F θ
  letI : Algebra.IsAlgebraic F S := IntermediateField.isAlgebraic_adjoin_simple hint
  let A := AlgebraicClosure S
  letI : IsGalois F A := { to_isSeparable := inferInstance, to_normal := inferInstance }
  obtain ⟨vA, hextA, _⟩ := hF A
  let vS : AddValuation S (WithTop ℚ) := vE.comap S.val.toRingHom
  have hextS : ∀ a : F, vS (algebraMap F S a) = vF a := hext
  have hrest : vA.comap (algebraMap S A) = vS := by
    apply hF.uniqueExtension
    · intro a
      change vA (algebraMap S A (algebraMap F S a)) = vF a
      rw [← IsScalarTower.algebraMap_apply F S A]
      exact hextA a
    · exact hextS
  have hval (x : S) : vA (algebraMap S A x) = vE (x : E) :=
    congrArg (fun w : AddValuation S (WithTop ℚ) => w x) hrest
  have hinv := addValuation_invariant_of_unique_extension vF vA hextA hF.uniqueExtension
  have happroxA : ∀ q : ℚ, ∃ a : F,
      (q : WithTop ℚ) < vA (algebraMap S A θS - algebraMap F A a) := by
    intro q
    obtain ⟨a, ha⟩ := happrox q
    refine ⟨a, ?_⟩
    have hd : algebraMap S A θS - algebraMap F A a =
        algebraMap S A (θS - algebraMap F S a) := by
      rw [map_sub (algebraMap S A) θS (algebraMap F S a),
        ← IsScalarTower.algebraMap_apply F S A]
    rw [hd, hval]
    exact ha
  obtain ⟨a, ha⟩ := mem_base_of_arbitrarily_close_in_galois vA hinv
    (algebraMap S A θS) happroxA
  have haS : algebraMap F S a = θS := by
    apply (algebraMap S A).injective
    simpa only [← IsScalarTower.algebraMap_apply F S A] using ha
  exact ⟨a, congrArg (fun x : S => (x : E)) haS⟩

/-- Arbitrary-ambient Krasner containment when the simple field generated
by alpha is normal. All distance hypotheses are stated for actual
K-automorphisms of K(alpha) and the actual ambient valuation. The proof
constructs an algebraic Galois closure of K(alpha,beta), transfers valuation
by uniqueness, restricts its automorphisms to K(alpha), applies Krasner, and
descends membership through injective field maps. -/
theorem krasner_mem_of_normal_adjoin
    {F E : Type u} [Field F] [Field E] [Algebra F E] [PerfectField F]
    (vF : AddValuation F (WithTop ℚ)) (vE : AddValuation E (WithTop ℚ))
    (hext : ∀ a : F, vE (algebraMap F E a) = vF a)
    (hF : RationalValuedHenselian vF)
    (α β : E) (hα : IsIntegral F α) (hβ : IsIntegral F β)
    (hnormal : Normal F F⟮α⟯)
    (hclose : ∀ σ : F⟮α⟯ ≃ₐ[F] F⟮α⟯,
      σ (AdjoinSimple.gen F α) ≠ AdjoinSimple.gen F α →
      vE (α - (σ (AdjoinSimple.gen F α) : E)) < vE (α - β)) :
    α ∈ F⟮β⟯ := by
  classical
  let S : IntermediateField F E := IntermediateField.adjoin F ({α, β} : Set E)
  have hmemα : α ∈ S := IntermediateField.subset_adjoin F _ (by simp)
  have hmemβ : β ∈ S := IntermediateField.subset_adjoin F _ (by simp)
  let αS : S := ⟨α, hmemα⟩
  let βS : S := ⟨β, hmemβ⟩
  letI : Algebra.IsAlgebraic F S := IntermediateField.isAlgebraic_adjoin (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hα
    · exact hβ)
  let T : IntermediateField F E := F⟮α⟯
  let αT : T := AdjoinSimple.gen F α
  have hTS : T ≤ S := IntermediateField.adjoin_simple_le_iff.mpr hmemα
  let ι : T →ₐ[F] S := IntermediateField.inclusion hTS
  letI : Algebra T S := ι.toRingHom.toAlgebra
  letI : IsScalarTower F T S := IsScalarTower.of_algebraMap_eq fun a => (ι.commutes a).symm
  letI : Normal F T := hnormal
  let A := AlgebraicClosure S
  letI : IsGalois F A := { to_isSeparable := inferInstance, to_normal := inferInstance }
  obtain ⟨vA, hextA, _⟩ := hF A
  let vS : AddValuation S (WithTop ℚ) := vE.comap S.val.toRingHom
  have hextS : ∀ a : F, vS (algebraMap F S a) = vF a := hext
  have hrest : vA.comap (algebraMap S A) = vS := by
    apply hF.uniqueExtension
    · intro a
      change vA (algebraMap S A (algebraMap F S a)) = vF a
      rw [← IsScalarTower.algebraMap_apply F S A]
      exact hextA a
    · exact hextS
  have hval (x : S) : vA (algebraMap S A x) = vE (x : E) :=
    congrArg (fun w : AddValuation S (WithTop ℚ) => w x) hrest
  have hinv := addValuation_invariant_of_unique_extension vF vA hextA hF.uniqueExtension
  have hαA : algebraMap T A αT = algebraMap S A αS := by
    rw [IsScalarTower.algebraMap_apply T S A]
    rfl
  have hcloseA : ∀ σ : A ≃ₐ[F] A, σ (algebraMap S A αS) ≠ algebraMap S A αS →
      vA (algebraMap S A αS - σ (algebraMap S A αS)) <
        vA (algebraMap S A αS - algebraMap S A βS) := by
    intro σ hσ
    let τ : T ≃ₐ[F] T := σ.restrictNormal T
    have hs : algebraMap S A (ι (τ αT)) = σ (algebraMap S A αS) := by
      change algebraMap S A (algebraMap T S (τ αT)) = _
      rw [← IsScalarTower.algebraMap_apply T S A]
      change algebraMap T A (σ.restrictNormal T αT) = _
      rw [AlgEquiv.restrictNormal_commutes, hαA]
    have hτ : τ αT ≠ αT := by
      intro h
      apply hσ
      rw [← hs, h]
      rfl
    rw [← hs, ← map_sub (algebraMap S A) αS (ι (τ αT)), hval,
      ← map_sub (algebraMap S A) αS βS, hval]
    exact hclose τ hτ
  have hmemA := krasner_mem_of_invariant_valuation vA hinv
    (algebraMap S A αS) (algebraMap S A βS) hcloseA
  let j : S →ₐ[F] A := IsScalarTower.toAlgHom F S A
  have hmap : (F⟮βS⟯).map j = F⟮algebraMap S A βS⟯ := by
    change (F⟮βS⟯).map j = F⟮j βS⟯
    simpa only [Set.image_singleton] using IntermediateField.adjoin_map F ({βS} : Set S) j
  rw [← hmap] at hmemA
  obtain ⟨x, hx, hxeq⟩ := hmemA
  have hxα : x = αS := j.injective hxeq
  have hmemS : αS ∈ F⟮βS⟯ := hxα ▸ hx
  have hmapE : (F⟮βS⟯).map S.val = F⟮β⟯ := by
    change (F⟮βS⟯).map S.val = F⟮S.val βS⟯
    simpa only [Set.image_singleton] using
      IntermediateField.adjoin_map F ({βS} : Set S) S.val
  have hmemE : (αS : E) ∈ (F⟮βS⟯).map S.val := ⟨αS, hmemS, rfl⟩
  rw [hmapE] at hmemE
  exact hmemE

section HahnMonomials

attribute [local instance 2000] HahnSeries.instAlgebra

variable {k : Type u} [Field k]

/-- The direct Hahn coefficient algebra is selected locally to avoid the
power-series algebra/pointwise scalar-action diamond in this mathlib version. -/
theorem hahn_constant_algebraMap (c : k) :
    algebraMap k (HahnSeries ℚ k) c = HahnSeries.single (0 : ℚ) c := by
  rfl

/-- The inverse of a nonzero coefficient-one Hahn monomial. -/
theorem hahn_single_one_inv (q : ℚ) :
    (HahnSeries.single q (1 : k))⁻¹ = HahnSeries.single (-q) 1 := by
  apply inv_eq_of_mul_eq_one_left
  simp [HahnSeries.single_mul_single]

/-- A subfield containing y contains every integral power monomial. -/
theorem hahn_integer_monomial_mem (K : IntermediateField k (HahnSeries ℚ k))
    (hy : HahnSeries.single (1 : ℚ) (1 : k) ∈ K) (z : ℤ) :
    HahnSeries.single (z : ℚ) (1 : k) ∈ K := by
  have hneg : HahnSeries.single (-1 : ℚ) (1 : k) ∈ K := by
    rw [← hahn_single_one_inv]
    exact K.inv_mem hy
  refine Int.induction_on z ?_ ?_ ?_
  · simpa using K.one_mem
  · intro i hi
    convert K.mul_mem hi hy using 1
    simp [HahnSeries.single_mul_single]
  · intro i hi
    convert K.mul_mem hi hneg using 1
    simp [HahnSeries.single_mul_single, sub_eq_add_neg]

/-- Constants times integral power monomials also belong to the base. -/
theorem hahn_integer_single_mem (K : IntermediateField k (HahnSeries ℚ k))
    (hy : HahnSeries.single (1 : ℚ) (1 : k) ∈ K) (z : ℤ) (c : k) :
    HahnSeries.single (z : ℚ) c ∈ K := by
  have hc : HahnSeries.single (0 : ℚ) c ∈ K := by
    simpa only [hahn_constant_algebraMap] using K.algebraMap_mem c
  simpa [HahnSeries.single_mul_single] using
    K.mul_mem hc (hahn_integer_monomial_mem K hy z)

/-- Removing the actual leading term strictly improves Hahn valuation. -/
theorem hahn_leading_monomial_error (a : HahnSeries ℚ k) (q : ℚ)
    (ha : a.orderTop = q) :
    (q : WithTop ℚ) < (HahnSeries.single q (a.coeff q) - a).orderTop := by
  have hc := HahnSeries.coeff_orderTop_ne ha
  have hle : (q : WithTop ℚ) ≤ (HahnSeries.single q (a.coeff q) - a).orderTop := by
    simpa [HahnSeries.orderTop_single hc, ha] using
      (HahnSeries.min_orderTop_le_orderTop_sub
        (x := HahnSeries.single q (a.coeff q)) (y := a))
  have hne : (HahnSeries.single q (a.coeff q) - a).orderTop ≠ q := by
    intro h
    have hcoeff := HahnSeries.coeff_orderTop_ne h
    exact hcoeff (by simp [HahnSeries.coeff_sub])
  exact lt_of_le_of_ne hle hne.symm

/-- The actual monomial lemma for a perfect rationally valued henselian
subfield of Hahn series containing the constants and y. Every value realized
by a nonzero base element has its coefficient-one monomial in the base.
The proof uses the actual Galois/Krasner argument, not a monomial-membership
assumption or a HenselianLocalRing instance on the field. -/
theorem hahn_monomial_mem_of_value [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K) ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : HahnSeries.single (1 : ℚ) (1 : k) ∈ K)
    (a : K) (q : ℚ) (ha : (a : HahnSeries ℚ k).orderTop = q) :
    HahnSeries.single q (1 : k) ∈ K := by
  let α : HahnSeries ℚ k := HahnSeries.single q ((a : HahnSeries ℚ k).coeff q)
  have hc : (a : HahnSeries ℚ k).coeff q ≠ 0 := HahnSeries.coeff_orderTop_ne ha
  have hα : α ≠ 0 := HahnSeries.single_ne_zero hc
  have hpowmem : α ^ q.den ∈ K := by
    dsimp [α]
    rw [HahnSeries.single_pow, nsmul_eq_mul, Rat.den_mul_eq_num]
    exact hahn_integer_single_mem K hy q.num _
  let d : K := ⟨α ^ q.den, hpowmem⟩
  have hconst : ∀ c : k, c ≠ 0 →
      HahnSeries.addVal ℚ k (algebraMap k (HahnSeries ℚ k) c) = 0 := by
    intro c hc'
    rw [hahn_constant_algebraMap, HahnSeries.addVal_apply]
    simpa using HahnSeries.orderTop_single (a := (0 : ℚ)) hc'
  have hclose : HahnSeries.addVal ℚ k α <
      HahnSeries.addVal ℚ k (α - algebraMap K (HahnSeries ℚ k) a) := by
    change α.orderTop < (α - (a : HahnSeries ℚ k)).orderTop
    rw [show α.orderTop = q from HahnSeries.orderTop_single hc]
    exact hahn_leading_monomial_error (a : HahnSeries ℚ k) q ha
  obtain ⟨c, heq⟩ := kummer_mem_base_of_rationalValuedHenselian
    (F := K) (E := HahnSeries ℚ k) (k := k)
    ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)) (HahnSeries.addVal ℚ k)
    (fun _ => rfl) hK hconst α hα q.den q.pos d a rfl hclose
  have hαmem : α ∈ K := heq ▸ c.property
  have hcInv : HahnSeries.single (0 : ℚ) ((a : HahnSeries ℚ k).coeff q)⁻¹ ∈ K := by
    simpa only [hahn_constant_algebraMap] using
      K.algebraMap_mem (((a : HahnSeries ℚ k).coeff q)⁻¹)
  have hm := K.mul_mem hcInv hαmem
  simpa [α, HahnSeries.single_mul_single, inv_mul_cancel₀ hc] using hm

/-- Constant multiples of every monomial at an actual base value belong
to the base. -/
theorem hahn_single_mem_of_value [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K) ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : HahnSeries.single (1 : ℚ) (1 : k) ∈ K)
    (a : K) (q : ℚ) (ha : (a : HahnSeries ℚ k).orderTop = q) (c : k) :
    HahnSeries.single q c ∈ K := by
  have hc : HahnSeries.single (0 : ℚ) c ∈ K := by
    simpa only [hahn_constant_algebraMap] using K.algebraMap_mem c
  simpa [HahnSeries.single_mul_single] using
    K.mul_mem hc (hahn_monomial_mem_of_value K hK hy a q ha)

/-- The left-finite algebraic exclusion used in the first-accumulation
argument. Its monomial hypotheses are supplied by actual support containment
and `hahn_single_mem_of_value` in the assembled proof. -/
theorem hahn_leftFinite_algebraic_mem
    (K : Subfield (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian ((HahnSeries.addVal ℚ k).comap K.subtype))
    (θ : HahnSeries ℚ k) (hint : IsIntegral K θ) (hLF : LeftFinite θ)
    (hmon : ∀ q ∈ θ.support, HahnSeries.single q (θ.coeff q) ∈ K) : θ ∈ K := by
  have happrox : ∀ q : ℚ, ∃ a : K,
      (q : WithTop ℚ) < HahnSeries.addVal ℚ k (θ - algebraMap K (HahnSeries ℚ k) a) := by
    intro q
    let a : K := ⟨truncLT (q + 1) θ,
      truncLT_mem_subfield K (q + 1) θ (hLF (q + 1)) hmon⟩
    refine ⟨a, ?_⟩
    change (q : WithTop ℚ) < (θ - truncLT (q + 1) θ).orderTop
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by linarith))
      (le_orderTop_sub_truncLT (q + 1) θ)
  obtain ⟨a, ha⟩ := algebraic_mem_base_of_arbitrarily_close
    ((HahnSeries.addVal ℚ k).comap K.subtype) (HahnSeries.addVal ℚ k)
    (fun _ => rfl) hK θ hint happrox
  exact ha ▸ a.property

end HahnMonomials

end NTCThird
