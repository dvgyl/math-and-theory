module

public import SecondCoefficient
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Tactic.FunProp

@[expose] public section

open scoped BigOperators
open Polynomial

namespace MathAndTheory.Gyires.RankTwo

noncomputable def lawCoefficient (n : ℕ) (θ : ℝ) (k : ℕ) :
    (Fin (n+1) → ℝ) →ₗ[ℝ] ℝ where
  toFun P := ∑ j, P j * (((1-C θ*X)^(n-j.val) * (1+C (1-θ)*X)^j.val : ℝ[X]).coeff k)
  map_add' P Q := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

noncomputable def varianceLaw (n : ℕ) (θ σ : ℝ) : (Fin (n+1) → ℝ) →ₗ[ℝ] ℝ :=
  (-2 / ((n : ℝ) * σ)) • lawCoefficient n θ 2

noncomputable def rankTwoWeight (n : ℕ) (σ : ℝ) (k : ℕ) : ℝ :=
  ((k.factorial : ℝ) * ((n-k).factorial : ℝ)) / ((n.factorial : ℝ) * σ ^ k)

noncomputable def lawDeficit (n : ℕ) (θ σ : ℝ) (P Q : Fin (n+1) → ℝ) : ℝ :=
  ∑ k : Fin (n+1), rankTwoWeight n σ k.val *
    ((lawCoefficient n θ k.val P) ^ 2 * (varianceLaw n θ σ Q) ^ k.val -
      lawCoefficient n θ k.val P * lawCoefficient n θ k.val Q)

lemma rankTwoWeight_nonneg (n : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) (k : ℕ) :
    0 ≤ rankTwoWeight n σ k := by
  unfold rankTwoWeight
  positivity

theorem lawDeficit_convex_left (n : ℕ) (θ σ : ℝ) (hσ : 0 ≤ σ)
    (D : Set (Fin (n+1) → ℝ)) (hD : Convex ℝ D)
    (Q : Fin (n+1) → ℝ) (hQ : 0 ≤ varianceLaw n θ σ Q) :
    ConvexOn ℝ D (fun P => lawDeficit n θ σ P Q) := by
  refine ⟨hD, ?_⟩
  intro P _ R _ α β hα hβ hsum
  simp only [lawDeficit, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  simp only [map_add, map_smul, smul_eq_mul]
  have hsq : (α * lawCoefficient n θ k.val P + β * lawCoefficient n θ k.val R) ^ 2 ≤
      α * (lawCoefficient n θ k.val P) ^ 2 + β * (lawCoefficient n θ k.val R) ^ 2 := by
    have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
      (show Even (2 : ℕ) from ⟨1, rfl⟩).convexOn_pow
    exact hconv.2 (Set.mem_univ _) (Set.mem_univ _) hα hβ hsum
  have hweight : 0 ≤ rankTwoWeight n σ k.val * (varianceLaw n θ σ Q) ^ k.val :=
    mul_nonneg (rankTwoWeight_nonneg n σ hσ k.val) (pow_nonneg hQ _)
  have hbound := mul_le_mul_of_nonneg_left hsq hweight
  nlinarith

theorem lawDeficit_convex_right (n : ℕ) (θ σ : ℝ) (hσ : 0 ≤ σ)
    (D : Set (Fin (n+1) → ℝ)) (hD : Convex ℝ D)
    (hvariance : ∀ Q ∈ D, 0 ≤ varianceLaw n θ σ Q)
    (P : Fin (n+1) → ℝ) :
    ConvexOn ℝ D (fun Q => lawDeficit n θ σ P Q) := by
  refine ⟨hD, ?_⟩
  intro Q hQ R hR α β hα hβ hsum
  simp only [lawDeficit, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  simp only [map_add, map_smul, smul_eq_mul]
  have hpow : (α * varianceLaw n θ σ Q + β * varianceLaw n θ σ R) ^ k.val ≤
      α * (varianceLaw n θ σ Q) ^ k.val + β * (varianceLaw n θ σ R) ^ k.val :=
    (convexOn_pow k.val).2 (hvariance Q hQ) (hvariance R hR) hα hβ hsum
  have hweight : 0 ≤ rankTwoWeight n σ k.val * (lawCoefficient n θ k.val P) ^ 2 :=
    mul_nonneg (rankTwoWeight_nonneg n σ hσ k.val) (sq_nonneg _)
  have hbound := mul_le_mul_of_nonneg_left hpow hweight
  nlinarith

lemma continuous_lawCoefficient (n : ℕ) (θ : ℝ) (k : ℕ) :
    Continuous (lawCoefficient n θ k) := by
  change Continuous (fun P : Fin (n+1) → ℝ =>
    ∑ j, P j * (((1-C θ*X)^(n-j.val) * (1+C (1-θ)*X)^j.val : ℝ[X]).coeff k))
  fun_prop

lemma continuous_varianceLaw (n : ℕ) (θ σ : ℝ) : Continuous (varianceLaw n θ σ) := by
  exact continuous_const.mul (continuous_lawCoefficient n θ 2)

theorem continuous_lawDeficit_left (n : ℕ) (θ σ : ℝ) (Q : Fin (n+1) → ℝ) :
    Continuous (fun P => lawDeficit n θ σ P Q) := by
  unfold lawDeficit
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul ((((continuous_lawCoefficient n θ k.val).pow 2).mul
    continuous_const).sub ((continuous_lawCoefficient n θ k.val).mul continuous_const))

theorem continuous_lawDeficit_right (n : ℕ) (θ σ : ℝ) (P : Fin (n+1) → ℝ) :
    Continuous (fun Q => lawDeficit n θ σ P Q) := by
  unfold lawDeficit
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul ((continuous_const.mul
    ((continuous_varianceLaw n θ σ).pow k.val)).sub
      (continuous_const.mul (continuous_lawCoefficient n θ k.val)))

end MathAndTheory.Gyires.RankTwo
