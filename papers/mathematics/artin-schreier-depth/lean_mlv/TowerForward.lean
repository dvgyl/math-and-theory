import ClosureTransport

/-!
# The full-closure approximation step for the AS forward direction

The approximation variable in the first theorem ranges over an arbitrary
algebraic Galois ambient field.  In particular, the later specialization uses
the actual `AlgebraicClosure K`, not an internal subfield of a Hahn field.

The residue-lifting premise is a valuation-theoretic statement on every
integral element of the ambient field.  It handles the boundary case in
which a competing approximation has value exactly zero: translate that
approximation by a base element before applying Krasner.

These statements formalize a step of Nart--Novacoski, arXiv:2503.18827v2,
Theorem 2.4.  They are not claimed as new arithmetic results.
-/

noncomputable section

open IntermediateField

namespace NTCThird

universe u

/-- Conjugate distance zero and cofinal approximation below zero imply the
actual degree-sensitive approximation criterion, provided residues of all
nonnegative-valued algebraic elements lift to the base.  The equality case
at zero is resolved explicitly by a base translation of the competitor. -/
theorem baseApproximation_of_zero_conjugate_distance
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    [Algebra.IsAlgebraic K E] [IsGalois K E]
    (vK : AddValuation K (WithTop ℚ)) (vE : AddValuation E (WithTop ℚ))
    (hext : ∀ a : K, vE (algebraMap K E a) = vK a)
    (hK : RationalValuedHenselian vK)
    (hresidue : ∀ z : E, 0 ≤ vE z →
      ∃ a : K, 0 < vE (z - algebraMap K E a))
    (θ : E)
    (hconjugates : ∀ σ : E ≃ₐ[K] E, σ θ ≠ θ → vE (θ - σ θ) = 0)
    (hcofinal : ∀ q : ℚ, q < 0 →
      ∃ a : K, (q : WithTop ℚ) < vE (θ - algebraMap K E a)) :
    BaseApproximation K vE θ := by
  intro b hb
  have hnegative : vE (θ - b) < 0 := by
    by_contra hnonnegative
    obtain ⟨a, ha⟩ := hresidue (θ - b) (le_of_not_gt hnonnegative)
    have hpositive : 0 < vE (θ - (b + algebraMap K E a)) := by
      simpa only [sub_add_eq_sub_sub] using ha
    have hmem : θ ∈ K⟮b + algebraMap K E a⟯ :=
      krasner_mem_of_rationalValuedHenselian vK vE hext hK θ
        (b + algebraMap K E a) (by
          intro σ hσ
          rw [hconjugates σ hσ]
          exact hpositive)
    have htranslate : K⟮b + algebraMap K E a⟯ ≤ K⟮b⟯ := by
      apply IntermediateField.adjoin_simple_le_iff.mpr
      exact (K⟮b⟯).add_mem (IntermediateField.mem_adjoin_simple_self K b)
        ((K⟮b⟯).algebraMap_mem a)
    have hsub : K⟮θ⟯ ≤ K⟮b⟯ :=
      IntermediateField.adjoin_simple_le_iff.mpr (htranslate hmem)
    have hθint : IsIntegral K θ :=
      (Algebra.IsAlgebraic.isAlgebraic (R := K) θ).isIntegral
    have hbint : IsIntegral K b :=
      (Algebra.IsAlgebraic.isAlgebraic (R := K) b).isIntegral
    letI : FiniteDimensional K K⟮b⟯ :=
      IntermediateField.adjoin.finiteDimensional hbint
    have hrank : Module.finrank K K⟮b⟯ < Module.finrank K K⟮θ⟯ := by
      rwa [finrank_adjoin_eq_elementDegree K b hbint,
        finrank_adjoin_eq_elementDegree K θ hθint]
    have heq : K⟮θ⟯ = K⟮b⟯ :=
      IntermediateField.eq_of_le_of_finrank_le hsub hrank.le
    rw [heq] at hrank
    exact lt_irrefl _ hrank
  obtain ⟨q, hq, hqnegative⟩ := WithTop.lt_iff_exists_coe.mp hnegative
  obtain ⟨a, ha⟩ := hcofinal q (by exact_mod_cast hqnegative)
  refine ⟨a, ?_⟩
  rw [hq]
  exact ha.le

/-- The preceding criterion gives minimum genuine Okutsu length one over
all primitive generators of the specified nontrivial intermediate field. -/
theorem minimum_okutsuLength_one_of_zero_conjugate_distance
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    [Algebra.IsAlgebraic K E] [IsGalois K E]
    (vK : AddValuation K (WithTop ℚ)) (vE : AddValuation E (WithTop ℚ))
    (hext : ∀ a : K, vE (algebraMap K E a) = vK a)
    (hK : RationalValuedHenselian vK)
    (hresidue : ∀ z : E, 0 ≤ vE z →
      ∃ a : K, 0 < vE (z - algebraMap K E a))
    (L : IntermediateField K E) (hL : L ≠ ⊥) (θ : E)
    (hgen : K⟮θ⟯ = L)
    (hconjugates : ∀ σ : E ≃ₐ[K] E, σ θ ≠ θ → vE (θ - σ θ) = 0)
    (hcofinal : ∀ q : ℚ, q < 0 →
      ∃ a : K, (q : WithTop ℚ) < vE (θ - algebraMap K E a)) :
    IsLeast (realizedOkutsuLengths K vE L) 1 := by
  apply (minimum_okutsuLength_one_iff_algebraic K vE L hL).mpr
  exact ⟨θ, hgen, baseApproximation_of_zero_conjugate_distance
    vK vE hext hK hresidue θ hconjugates hcofinal⟩

end NTCThird
