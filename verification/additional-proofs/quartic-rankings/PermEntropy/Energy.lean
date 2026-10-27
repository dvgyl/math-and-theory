import PermEntropy.Comparison
import PermEntropy.Cut

/-! # Mean comparison energy gives a large normalized cut

Every ranking contributes its signed comparisons to the same skew matrix.
Averaging the ordering score therefore gives one half of its squared energy.
-/

noncomputable section
open scoped BigOperators

namespace PermEntropy

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem twice_orderSum_eq_sum_comparison (B : V → V → ℝ)
    (hskew : ∀ u v, B v u = -B u v) (r : Ranking V) :
    2 * orderSum B r.order = ∑ u, ∑ v, B u v * compareSign r u v := by
  have hchange : (∑ u, ∑ v, B u v * compareSign r u v) =
      ∑ i : Fin (Fintype.card V), ∑ j : Fin (Fintype.card V),
        B (r.enum i) (r.enum j) * compareSign r (r.enum i) (r.enum j) := by
    rw [← r.sum_enum (fun u => ∑ v, B u v * compareSign r u v)]
    apply Finset.sum_congr rfl
    intro i _
    exact (r.sum_enum (fun v => B (r.enum i) v * compareSign r (r.enum i) v)).symm
  rw [hchange, ← r.ofFn_enum, orderSum_ofFn]
  have hterm (i j : Fin (Fintype.card V)) :
      B (r.enum i) (r.enum j) * compareSign r (r.enum i) (r.enum j) =
        (if i < j then B (r.enum i) (r.enum j) else 0) +
        (if j < i then -B (r.enum i) (r.enum j) else 0) := by
    by_cases h : i < j
    · have hh : ¬ j < i := fun h' => lt_asymm h h'
      simp [compareSign, h, hh]
    · by_cases hh : j < i <;> simp [compareSign, h, hh]
  have hback : (∑ i : Fin (Fintype.card V), ∑ j : Fin (Fintype.card V),
      if j < i then -B (r.enum i) (r.enum j) else 0) =
      ∑ i : Fin (Fintype.card V), ∑ j : Fin (Fintype.card V),
        if i < j then B (r.enum i) (r.enum j) else 0 := by
    calc
      _ = ∑ i : Fin (Fintype.card V), ∑ j : Fin (Fintype.card V),
          if i < j then -B (r.enum j) (r.enum i) else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hskew (r.enum i) (r.enum j), neg_neg]
  simp_rw [hterm, Finset.sum_add_distrib]
  rw [hback]
  ring

namespace FinDist

theorem twice_expect_orderSum_eq_energy (p : FinDist (Ranking V)) :
    2 * p.expect (fun r => orderSum p.meanComparison r.order) =
      ∑ u, ∑ v, (p.meanComparison u v)^2 := by
  have hh := p.expect_congr (fun r =>
    twice_orderSum_eq_sum_comparison p.meanComparison p.meanComparison_skew r)
  rw [p.expect_const_mul] at hh
  simp_rw [expect_sum, expect_const_mul] at hh
  simpa only [meanComparison, pow_two] using hh

theorem meanComparison_energy_lower (p : FinDist (Ranking V)) (b : ℝ) (hb : 0 < b)
    (hbias : ∀ u v : V, u ≠ v → b ≤ |p.meanComparison u v|) :
    b^2 * ((Fintype.card V : ℝ)^2 - (Fintype.card V : ℝ)) ≤
      ∑ u, ∑ v, (p.meanComparison u v)^2 := by
  classical
  have hrow (u : V) : ((Fintype.card V : ℝ) - 1) * b^2 ≤
      ∑ v, (p.meanComparison u v)^2 := by
    have hh : (∑ v : V, (b^2 - (if v = u then b^2 else 0))) ≤
        ∑ v, (p.meanComparison u v)^2 := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : v = u
      · subst v
        simp
      · have huv : u ≠ v := Ne.symm hv
        have hs := (sq_le_sq₀ (le_of_lt hb) (abs_nonneg (p.meanComparison u v))).mpr
          (hbias u v huv)
        simpa only [if_neg hv, sub_zero, sq_abs] using hs
    simpa [Finset.sum_sub_distrib, sub_mul] using hh
  have hh := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset V)) => hrow u)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  convert hh using 1
  ring

theorem expect_orderSum_ge (p : FinDist (Ranking V)) (b : ℝ) (hb : 0 < b)
    (hm : 2 ≤ Fintype.card V)
    (hbias : ∀ u v : V, u ≠ v → b ≤ |p.meanComparison u v|) :
    b^2 * (Fintype.card V : ℝ)^2 / 4 ≤
      p.expect (fun r => orderSum p.meanComparison r.order) := by
  have henergy := p.meanComparison_energy_lower b hb hbias
  have he := p.twice_expect_orderSum_eq_energy
  have hm' : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hm
  have hprod : 0 ≤ b^2 * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 2)) :=
    mul_nonneg (sq_nonneg b) (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  nlinarith

theorem exists_orderSum_ge (p : FinDist (Ranking V)) (b : ℝ) (hb : 0 < b)
    (hm : 2 ≤ Fintype.card V)
    (hbias : ∀ u v : V, u ≠ v → b ≤ |p.meanComparison u v|) :
    ∃ r : Ranking V, b^2 * (Fintype.card V : ℝ)^2 / 4 ≤
      orderSum p.meanComparison r.order := by
  obtain ⟨r, hr⟩ := p.exists_expect_le (fun r => orderSum p.meanComparison r.order)
  exact ⟨r, (p.expect_orderSum_ge b hb hm hbias).trans hr⟩

theorem exists_meanComparison_cut (p : FinDist (Ranking V)) (b : ℝ) (hb : 0 < b)
    (hm : 2 ≤ Fintype.card V)
    (hbias : ∀ u v : V, u ≠ v → b ≤ |p.meanComparison u v|) :
    ∃ L R : Finset V, Disjoint L R ∧ L.Nonempty ∧ R.Nonempty ∧
      (b^4 * (Fintype.card V : ℝ) / 576) *
        (((L.card + R.card : ℕ) : ℝ)^3) ≤ (cutSum p.meanComparison L R)^2 := by
  obtain ⟨r, hr⟩ := p.exists_orderSum_ge b hb hm hbias
  exact exists_normalized_cut p.meanComparison b hb hm r.order r.nodup r.length_eq hr

end FinDist
end PermEntropy
