module

public import DeficitConvexity
public import PairInterpolation
public import NormalizedPermanent

@[expose] public section

open scoped BigOperators
open Polynomial

namespace MathAndTheory.Gyires.RankTwo

open Bernoulli

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma lawCoefficient_law (p : ι → ℝ) (θ : ℝ) (k : ℕ) (hk : k ≤ Fintype.card ι) :
    lawCoefficient (Fintype.card ι) θ k (law p) = elementary (fun i => p i-θ) k := by
  change (∑ j : Fin (Fintype.card ι+1), probability p j.val *
    (((1-C θ*X)^(Fintype.card ι-j.val) * (1+C (1-θ)*X)^j.val : ℝ[X]).coeff k)) = _
  rw [Fin.sum_univ_eq_sum_range (fun j => probability p j *
    (((1-C θ*X)^(Fintype.card ι-j) * (1+C (1-θ)*X)^j : ℝ[X]).coeff k))]
  exact (centered_elementary_eq_law p θ k hk).symm

lemma varianceLaw_law (p : ι → ℝ) (θ σ : ℝ)
    (hn : 2 ≤ Fintype.card ι) (hp : ∑ i, (p i-θ) = 0) :
    varianceLaw (Fintype.card ι) θ σ (law p) =
      (∑ i, (p i-θ) ^ 2) / ((Fintype.card ι : ℝ) * σ) := by
  change (-2 / ((Fintype.card ι : ℝ) * σ)) *
    lawCoefficient (Fintype.card ι) θ 2 (law p) = _
  rw [lawCoefficient_law p θ 2 hn, variance_eq_neg_two_elementary _ hp]
  ring

omit [DecidableEq ι] in
lemma parameter_center_sum {μ θ : ℝ} {p : ι → ℝ}
    (hp : p ∈ parameters μ) (hmean : μ = (Fintype.card ι : ℝ) * θ) :
    ∑ i, (p i-θ) = 0 := by
  rw [Finset.sum_sub_distrib, hp.2]
  simp [hmean]

theorem varianceLaw_nonneg_on_hull (hn : 2 ≤ Fintype.card ι) (μ θ σ : ℝ)
    (hmean : μ = (Fintype.card ι : ℝ) * θ) (hσ : 0 ≤ σ) :
    ∀ P ∈ convexHull ℝ (law '' parameters (ι := ι) μ),
      0 ≤ varianceLaw (Fintype.card ι) θ σ P := by
  have hactual : law '' parameters (ι := ι) μ ⊆
      {P | 0 ≤ varianceLaw (Fintype.card ι) θ σ P} := by
    rintro _ ⟨p, hp, rfl⟩
    change 0 ≤ varianceLaw (Fintype.card ι) θ σ (law p)
    rw [varianceLaw_law p θ σ hn (parameter_center_sum hp hmean)]
    exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) hσ)
  have hhalf : Convex ℝ {P | 0 ≤ varianceLaw (Fintype.card ι) θ σ P} :=
    (convex_Ici (0 : ℝ)).linear_preimage (varianceLaw (Fintype.card ι) θ σ)
  exact convexHull_min hactual hhalf

theorem lawDeficit_eq_actual (hn : 2 ≤ Fintype.card ι)
    (θ σ : ℝ) (hσ : σ ≠ 0) (p q : ι → ℝ)
    (hq : ∑ i, (q i-θ) = 0) :
    let A := centered (1 / ((Fintype.card ι : ℝ) * σ))
      (fun i => p i-θ) (fun i => q i-θ)
    let c := ((Fintype.card ι).factorial : ℝ) / (Fintype.card ι : ℝ) ^ Fintype.card ι
    lawDeficit (Fintype.card ι) θ σ (law p) (law q) =
      (A * A.transpose).permanent / c - A.permanent / c := by
  have hn0 : Fintype.card ι ≠ 0 := by omega
  dsimp only
  rw [permanent_centered_gram_left_normalized hn0 σ hσ _ _ hq,
    permanent_centered_normalized hn0 σ hσ, ← Finset.sum_sub_distrib]
  unfold lawDeficit
  rw [Fin.sum_univ_eq_sum_range (fun k => rankTwoWeight (Fintype.card ι) σ k *
    ((lawCoefficient (Fintype.card ι) θ k (law p))^2 *
      (varianceLaw (Fintype.card ι) θ σ (law q))^k -
      lawCoefficient (Fintype.card ι) θ k (law p) * lawCoefficient (Fintype.card ι) θ k (law q)))]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ Fintype.card ι := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  rw [lawCoefficient_law p θ k hk', lawCoefficient_law q θ k hk',
    varianceLaw_law q θ σ hn hq]
  unfold rankTwoWeight
  ring

end MathAndTheory.Gyires.RankTwo
