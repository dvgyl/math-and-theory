import SidonRenyi.Optimization
import SidonRenyi.Entropy
import SidonRenyi.Binary
import SidonRenyi.Threshold

/-!
# Sharp universal Rényi-entropy threshold for iid sums on finite Sidon sets

The main theorem is `universalUniformOptimal_iff_criticalOrder`. The positive
direction applies to every finite strong Sidon support in any commutative
additive semigroup. The negative direction uses the actual support `{0,1}`.
All entropies use natural logarithms, and the theorem is stated for `1 < a`.
-/

open scoped BigOperators

namespace SidonRenyi

/-- The full entropy inequality for arbitrary finite Sidon supports and laws. -/
theorem renyiSumEntropy_le_uniform {ι A : Type*} [Fintype ι] [LinearOrder ι]
    [Nonempty ι] [AddCommSemigroup A] [DecidableEq A]
    {a : ℝ} (ha : 1 < a) (hcrit : (2 : ℝ) ^ (a - 1) ≤ 2 * a - 1)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (v : ι → A) (hv : IsSidonMap v) :
    renyiSumEntropy a p v ≤ renyiSumEntropy a (uniformProbability ι) v := by
  apply entropy_le_of_powerMoment_le a ha (uniformProbability ι) p
    (fun i => (uniformProbability_pos ι i).le) hp
    (sum_uniformProbability ι) hsum v hv
  exact powerMoment_uniform_le ha hcrit hp hsum

/-- Above the threshold a genuine two-point Sidon law strictly beats uniform input. -/
theorem exists_binary_entropy_counterexample {a : ℝ} (ha : 1 < a)
    (hcrit : 2 * a - 1 < (2 : ℝ) ^ (a - 1)) :
    ∃ p : Fin 2 → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      renyiSumEntropy a (uniformProbability (Fin 2)) binaryValues <
        renyiSumEntropy a p binaryValues := by
  obtain ⟨p, hp, hsum, hlt⟩ := exists_binary_powerMoment_counterexample ha hcrit
  refine ⟨p, hp, hsum, ?_⟩
  apply entropy_lt_of_powerMoment_lt a ha p (uniformProbability (Fin 2)) hp
    (fun i => (uniformProbability_pos (Fin 2) i).le) hsum
    (sum_uniformProbability (Fin 2)) binaryValues binaryValues_isSidon
  simpa [uniformProbability] using hlt

/-- Universal optimality over all nonempty finite Sidon supports in abelian groups.
Finite supports may be enumerated in an arbitrary linear order. -/
def UniversalUniformOptimal (a : ℝ) : Prop :=
  ∀ (ι A : Type) [Fintype ι] [LinearOrder ι] [Nonempty ι]
    [AddCommGroup A] [DecidableEq A]
    (v : ι → A), IsSidonMap v →
    ∀ (p : ι → ℝ), (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
      renyiSumEntropy a p v ≤ renyiSumEntropy a (uniformProbability ι) v

/-- Exact necessary and sufficient scalar condition for universal optimality. -/
theorem universalUniformOptimal_iff {a : ℝ} (ha : 1 < a) :
    UniversalUniformOptimal a ↔ (2 : ℝ) ^ (a - 1) ≤ 2 * a - 1 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨p, hp, hsum, hlt⟩ := exists_binary_entropy_counterexample ha (lt_of_not_ge hn)
    have hle := h (Fin 2) ℤ binaryValues binaryValues_isSidon p hp hsum
    exact (not_lt_of_ge hle) hlt
  · intro hcrit ι A _ _ _ _ _ v hv p hp hsum
    exact renyiSumEntropy_le_uniform ha hcrit p hp hsum v hv

/-- Complete classification of every order above one, including the critical endpoint. -/
theorem universalUniformOptimal_iff_criticalOrder {a : ℝ} (ha : 1 < a) :
    UniversalUniformOptimal a ↔ a ≤ criticalOrder := by
  rw [universalUniformOptimal_iff ha, criticalOrder_condition_iff ha]

/-- Sharp maximum value, in nats, throughout the valid range. -/
theorem renyiSumEntropy_uniform_value {ι A : Type*} [Fintype ι] [LinearOrder ι]
    [Nonempty ι] [AddCommSemigroup A] [DecidableEq A]
    (a : ℝ) (v : ι → A) (hv : IsSidonMap v) :
    renyiSumEntropy a (uniformProbability ι) v =
      Real.log (((Fintype.card ι : ℝ) + (2 : ℝ) ^ (a - 1) *
        (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)) *
        (1 / (Fintype.card ι : ℝ)) ^ (2 * a)) / (1 - a) := by
  rw [renyiSumEntropy_eq_log_powerMoment (uniformProbability ι)
    (fun i => (uniformProbability_pos ι i).le) v hv a]
  have h := uniform_powerMoment (ι := ι) a
  simpa only [uniformProbability, one_div] using congrArg
    (fun x : ℝ => Real.log x / (1 - a)) h

end SidonRenyi
