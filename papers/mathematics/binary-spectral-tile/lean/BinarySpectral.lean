import BinaryWalsh
import BinaryTiling
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
open scoped BigOperators
namespace BinaryFuglede

def characterVector (i : Fin 64) : Fin 64 → ℂ := fun k => character (freq i) (point k)

lemma character_gram (i j : Fin 64) :
    (∑ k : Fin 64, characterVector i k * characterVector j k) =
      if i = j then (64 : ℂ) else 0 := by
  by_cases hij : i = j
  · subst j
    simp [characterVector, character_sq]
  · rw [if_neg hij]
    have h := congrArg (fun z : ℤ => (z : ℂ)) (int_character_orthogonality i j hij)
    simpa [characterVector, character] using h

lemma character_vectors_linearIndependent : LinearIndependent ℂ characterVector := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have hs := congrArg (fun v : Fin 64 → ℂ => ∑ k, characterVector i k * v k) hf
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero] at hs
  have he : (∑ k, characterVector i k * (∑ j, f j * characterVector j k)) =
      64 * f i := by
    calc
      _ = ∑ k, ∑ j, f j * (characterVector i k * characterVector j k) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j, ∑ k, f j * (characterVector i k * characterVector j k) :=
        Finset.sum_comm
      _ = ∑ j, f j * (if i = j then (64 : ℂ) else 0) := by
        simp_rw [← Finset.mul_sum, character_gram]
      _ = 64 * f i := by simp [mul_comm]
  rw [he] at hs
  exact (mul_eq_zero.mp hs).resolve_left (by norm_num)

noncomputable def enumeratedCharacterBasis : Basis (Fin 64) ℂ (Fin 64 → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank character_vectors_linearIndependent
    (Module.finrank_fintype_fun_eq_card ℂ).symm

lemma enumeratedCharacterBasis_apply (i k : Fin 64) :
    enumeratedCharacterBasis i k = character (freq i) (point k) := by
  have h : ⇑enumeratedCharacterBasis = characterVector :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  exact congrFun (congrFun h i) k

noncomputable def restrictToEnumeration : (Eset → ℂ) ≃ₗ[ℂ] (Fin 64 → ℂ) where
  toFun := fun f i => f (pointEquiv i)
  invFun := fun f x => f (pointEquiv.symm x)
  left_inv := fun f => by funext x; simp
  right_inv := fun f => by funext i; simp
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

noncomputable def actualCharacterBasis : Basis (Fin 64) ℂ (Eset → ℂ) :=
  enumeratedCharacterBasis.map restrictToEnumeration.symm

lemma actualCharacterBasis_apply (i : Fin 64) (x : Eset) :
    actualCharacterBasis i x = character (freq i) x := by
  change enumeratedCharacterBasis i (pointEquiv.symm x) = _
  rw [enumeratedCharacterBasis_apply]
  have hx : point (pointEquiv.symm x) = (x : V) :=
    congrArg Subtype.val (pointEquiv.apply_symm_apply x)
  rw [hx]

lemma freq_injective : Function.Injective freq := by
  intro i j hij
  apply actualCharacterBasis.injective
  funext x
  simp only [actualCharacterBasis_apply, hij]

noncomputable def freqEquiv : Fin 64 ≃ Lset :=
  Equiv.ofBijective (fun i => ⟨freq i, ⟨i,rfl⟩⟩)
    ⟨fun _ _ h => freq_injective (congrArg Subtype.val h),
      fun x => by obtain ⟨i, hi⟩ := x.property; exact ⟨i, Subtype.ext hi⟩⟩

lemma card_Lset [Fintype Lset] : Fintype.card Lset = 64 := by
  rw [← Fintype.card_congr freqEquiv]
  rfl

noncomputable def spectrumBasis : Basis Lset ℂ (Eset → ℂ) :=
  actualCharacterBasis.reindex freqEquiv

lemma spectrumBasis_apply (l : Lset) (x : Eset) :
    spectrumBasis l x = character l x := by
  simp only [spectrumBasis, Basis.reindex_apply]
  rw [actualCharacterBasis_apply]
  have hl : freq (freqEquiv.symm l) = (l : V) :=
    congrArg Subtype.val (freqEquiv.apply_symm_apply l)
  rw [hl]

lemma actual_character_orthogonality [Fintype Eset] (i j : Fin 64) (hij : i ≠ j) :
    (∑ x : Eset, character (freq i) x * star (character (freq j) x)) = 0 := by
  rw [← Equiv.sum_comp pointEquiv]
  simp only [character_conj]
  change (∑ k : Fin 64, characterVector i k * characterVector j k) = 0
  rw [character_gram, if_neg hij]

/-- Spectrality means a basis of ALL complex functions on the actual set,
consisting of restricted additive characters and pairwise orthogonal for
counting measure. Frequencies are elements of an actual subset of V. -/
def IsSpectral (A : Set V) [Fintype A] : Prop :=
  ∃ L : Set V, ∃ b : Basis L ℂ (A → ℂ),
    (∀ l : L, ∀ x : A, b l x = character l x) ∧
    ∀ l m : L, l ≠ m → (∑ x : A, character l x * star (character m x)) = 0

lemma Eset_isSpectral [Fintype Eset] : IsSpectral Eset := by
  refine ⟨Lset, spectrumBasis, spectrumBasis_apply, ?_⟩
  intro l m hlm
  obtain ⟨i,rfl⟩ := freqEquiv.surjective l
  obtain ⟨j,rfl⟩ := freqEquiv.surjective m
  have hij : i ≠ j := fun h => hlm (congrArg freqEquiv h)
  exact actual_character_orthogonality i j hij

end BinaryFuglede
