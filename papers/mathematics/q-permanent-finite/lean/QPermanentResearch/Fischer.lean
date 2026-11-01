import QPermanentResearch.Basic
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Arbitrary-rank real Gram permanents as factorial-weighted coefficient squares.
The fiber-matching argument extends the two-color argument in Kenta Kitamura's
Apache-2.0 proof package, revision 4200da4fc1a132d69c23fb877795b5b72089544b.
All identities below are kernel proofs, for the actual permutation sum.
-/

open scoped BigOperators
namespace QPermanentResearch
noncomputable section

def colorCount {n d : ℕ} (f : Fin n → Fin d) (c : Fin d) : ℕ :=
  Fintype.card {i // f i = c}

theorem colorCount_comp {n d : ℕ} (f : Fin n → Fin d)
    (σ : Equiv.Perm (Fin n)) (c : Fin d) :
    colorCount (f ∘ σ) c = colorCount f c := by
  classical
  exact Fintype.card_congr (Equiv.subtypeEquiv σ (fun _ => Iff.rfl))

theorem exists_colorMatching {n d : ℕ} (f g : Fin n → Fin d)
    (h : colorCount f = colorCount g) :
    ∃ σ : Equiv.Perm (Fin n), f ∘ σ = g := by
  classical
  let e (c : Fin d) : {i // g i = c} ≃ {i // f i = c} :=
    Fintype.equivOfCardEq (congrFun h c).symm
  let σ : Equiv.Perm (Fin n) :=
    (Equiv.sigmaFiberEquiv g).symm.trans
      ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv f))
  refine ⟨σ, funext fun i => ?_⟩
  exact (e (g i) ⟨i, rfl⟩).property

def colorMatchingEquiv {n : ℕ} {ι : Type*} (f g : Fin n → ι)
    (σ₀ : Equiv.Perm (Fin n)) (h₀ : f ∘ σ₀ = g) :
    {σ : Equiv.Perm (Fin n) // f ∘ σ = g} ≃
      {τ : Equiv.Perm (Fin n) // f ∘ τ = f} where
  toFun σ := ⟨σ.val * σ₀.symm, by
    funext i
    change f (σ.val (σ₀.symm i)) = f i
    calc
      _ = g (σ₀.symm i) := congrFun σ.property _
      _ = f i := by rw [← h₀]; simp⟩
  invFun τ := ⟨τ.val * σ₀, by
    funext i
    change f (τ.val (σ₀ i)) = g i
    calc
      _ = f (σ₀ i) := congrFun τ.property _
      _ = g i := congrFun h₀ _⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    simp [Equiv.Perm.mul_apply]
  right_inv τ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    simp [Equiv.Perm.mul_apply]

theorem colorMatching_card {n d : ℕ} (f g : Fin n → Fin d)
    (h : colorCount f = colorCount g) :
    Fintype.card {σ : Equiv.Perm (Fin n) // f ∘ σ = g} =
      ∏ c : Fin d, (colorCount f c).factorial := by
  classical
  obtain ⟨σ₀, h₀⟩ := exists_colorMatching f g h
  rw [Fintype.card_congr (colorMatchingEquiv f g σ₀ h₀),
    DomMulAct.stabilizer_card]
  rfl

theorem colorMatching_card_ite {n d : ℕ} (f g : Fin n → Fin d) :
    Fintype.card {σ : Equiv.Perm (Fin n) // f ∘ σ = g} =
      if colorCount f = colorCount g then
        ∏ c : Fin d, (colorCount f c).factorial else 0 := by
  classical
  by_cases h : colorCount f = colorCount g
  · simpa [h] using colorMatching_card f g h
  · have hempty : IsEmpty {σ : Equiv.Perm (Fin n) // f ∘ σ = g} := ⟨fun σ => by
      apply h
      funext c
      have heq := colorCount_comp f σ.val c
      rw [σ.property] at heq
      exact heq.symm⟩
    simp [h]

def colorMonomial {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ)
    (f : Fin n → Fin d) : ℝ := ∏ i, V i (f i)

theorem sum_color_permutations {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ)
    (f : Fin n → Fin d) :
    (∑ σ : Equiv.Perm (Fin n), colorMonomial V (f ∘ σ)) =
      ∑ g : Fin n → Fin d,
        (if colorCount f = colorCount g then
          ∏ c : Fin d, (colorCount f c).factorial else 0 : ℕ) *
            colorMonomial V g := by
  classical
  have h := Fintype.sum_fiberwise' (fun σ : Equiv.Perm (Fin n) => f ∘ σ)
    (colorMonomial V)
  simpa [colorMatching_card_ite, nsmul_eq_mul] using h.symm

theorem colorMonomial_permute {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ)
    (f : Fin n → Fin d) (σ : Equiv.Perm (Fin n)) :
    (∏ i, V (σ i) (f i)) = colorMonomial V (f ∘ σ.symm) := by
  classical
  exact Fintype.prod_equiv σ _ _ (fun i => by simp)

theorem gram_permanent_colorSum {n d : ℕ} (U W : Matrix (Fin n) (Fin d) ℝ) :
    qPermanent (U * W.transpose) 1 =
      ∑ f : Fin n → Fin d,
        (∑ g : Fin n → Fin d,
          (if colorCount f = colorCount g then
            ∏ c : Fin d, (colorCount f c).factorial else 0 : ℕ) *
              colorMonomial W g) * colorMonomial U f := by
  classical
  rw [qPermanent_one]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Fintype.prod_sum, Finset.prod_mul_distrib,
    colorMonomial_permute]
  change (∑ σ : Equiv.Perm (Fin n), ∑ f : Fin n → Fin d,
    colorMonomial U f * colorMonomial W (f ∘ σ.symm)) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [← Finset.mul_sum]
  have hinv : (∑ σ : Equiv.Perm (Fin n), colorMonomial W (f ∘ σ.symm)) =
      ∑ σ : Equiv.Perm (Fin n), colorMonomial W (f ∘ σ) :=
    (show Function.Involutive (fun σ : Equiv.Perm (Fin n) => σ.symm) from
      fun σ => σ.symm_symm).bijective.sum_comp (fun σ => colorMonomial W (f ∘ σ))
  rw [hinv, sum_color_permutations, mul_comm]

theorem colorCount_le {n d : ℕ} (f : Fin n → Fin d) (c : Fin d) :
    colorCount f c ≤ n := by
  classical
  simpa [colorCount] using Fintype.card_subtype_le (fun i : Fin n => f i = c)

def colorIndex {n d : ℕ} (f : Fin n → Fin d) : Fin d → Fin (n + 1) :=
  fun c => ⟨colorCount f c, Nat.lt_succ_of_le (colorCount_le f c)⟩

theorem colorIndex_eq_iff {n d : ℕ} (f g : Fin n → Fin d) :
    colorIndex f = colorIndex g ↔ colorCount f = colorCount g := by
  constructor
  · intro h
    funext c
    exact congrArg Fin.val (congrFun h c)
  · intro h
    funext c
    apply Fin.ext
    exact congrFun h c

def colorCoefficient {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ)
    (α : Fin d → Fin (n + 1)) : ℝ :=
  ∑ f : Fin n → Fin d, if colorIndex f = α then colorMonomial V f else 0

def colorWeight {n d : ℕ} (α : Fin d → Fin (n + 1)) : ℝ :=
  ∏ c : Fin d, ((α c).val.factorial : ℝ)

theorem colorWeight_index {n d : ℕ} (f : Fin n → Fin d) :
    colorWeight (colorIndex f) =
      ((∏ c : Fin d, (colorCount f c).factorial : ℕ) : ℝ) := by
  simp [colorWeight, colorIndex]

theorem gram_permanent_coefficients {n d : ℕ}
    (U W : Matrix (Fin n) (Fin d) ℝ) :
    qPermanent (U * W.transpose) 1 =
      ∑ α : Fin d → Fin (n + 1),
        colorWeight α * colorCoefficient W α * colorCoefficient U α := by
  classical
  rw [gram_permanent_colorSum]
  have hinner : ∀ f : Fin n → Fin d,
      (∑ g : Fin n → Fin d,
        (if colorCount f = colorCount g then
          ∏ c : Fin d, (colorCount f c).factorial else 0 : ℕ) *
            colorMonomial W g) =
        colorWeight (colorIndex f) * colorCoefficient W (colorIndex f) := by
    intro f
    rw [colorWeight_index]
    simp [colorCoefficient, colorIndex_eq_iff, Finset.mul_sum, mul_ite, eq_comm]
  simp_rw [hinner]
  rw [← Finset.sum_fiberwise Finset.univ colorIndex]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_filter]
  conv_rhs =>
    arg 2
    rw [colorCoefficient]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  by_cases hf : colorIndex f = α
  · simp [hf]
  · simp [hf]

/-- The Fischer coefficient-square identity for every finite real Gram family. -/
theorem gram_permanent_squares {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) :
    qPermanent (V * V.transpose) 1 =
      ∑ α : Fin d → Fin (n + 1),
        colorWeight α * (colorCoefficient V α) ^ 2 := by
  rw [gram_permanent_coefficients]
  apply Finset.sum_congr rfl
  intro α _
  ring

#print axioms gram_permanent_squares

end
end QPermanentResearch
