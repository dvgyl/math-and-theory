module
public import SingleComponent

@[expose] public section

noncomputable section
open Polynomial
namespace PowerRank

/-- The operator powers use the literal forward index n+k. -/
theorem shift_pow_apply (u : Seq) (k n : ℕ) : (shift ^ k) u n = u (n + k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change (shift ^ k) u (n + 1) = _
    rw [ih]
    congr 1
    omega

/-- This is the coefficient-sum recurrence specified in the manuscript. -/
theorem polyAction_apply (q : ℂ[X]) (u : Seq) (n : ℕ) :
    polyAction q u n =
      ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k * u (n + k) := by
  simp [polyAction, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.sum_apply, shift_pow_apply]

/-- Applying any finite recurrence operator preserves vanishing on a tail. -/
theorem polyAction_preserves_tail_zero (q : ℂ[X]) (u : Seq)
    (hu : ∃ N, ∀ n ≥ N, u n = 0) : EventuallyAnnihilates q u := by
  obtain ⟨N, hN⟩ := hu
  refine ⟨N, fun n hn => ?_⟩
  rw [polyAction_apply]
  apply Finset.sum_eq_zero
  intro k hk
  rw [hN (n + k) (by omega), mul_zero]

/-- Distinct complex exponential-polynomial components are independent on a tail. -/
theorem expPoly_sum_eventually_zero_iff {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (hlam : ∀ i, lam i ≠ 0) (hinj : Function.Injective lam)
    (P : ι → ℂ[X]) :
    (∃ N, ∀ n ≥ N, (∑ i, expPoly (lam i) (P i)) n = 0) ↔ ∀ i, P i = 0 := by
  classical
  constructor
  · intro hsum i
    by_contra hPi
    let q : ℂ[X] := ∏ j ∈ Finset.univ.erase i, (X - C (lam j)) ^ ((P j).natDegree + 1)
    have hqeval : q.eval (lam i) ≠ 0 := by
      dsimp [q]
      rw [eval_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      rw [eval_pow, eval_sub, eval_X, eval_C]
      exact pow_ne_zero _ (sub_ne_zero.mpr (hinj.ne (Finset.mem_erase.mp hj).1.symm))
    have hother : ∀ j, j ≠ i → polyAction q (expPoly (lam j) (P j)) = 0 := by
      intro j hji
      by_cases hPj : P j = 0
      · rw [polyAction_expPoly, hPj, map_zero]
        ext n
        simp [expPoly]
      have hdvd : (X - C (lam j)) ^ ((P j).natDegree + 1) ∣ q :=
        Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
      have hann := (eventual_annihilator_expPoly_iff_dvd (lam j) (hlam j) (P j) hPj q).mpr hdvd
      have hker := (eventual_annihilator_iff_coeff_kernel (lam j) (hlam j) q (P j)).mp hann
      rw [polyAction_expPoly, hker]
      ext n
      simp [expPoly]
    have haction : polyAction q (∑ j, expPoly (lam j) (P j)) =
        expPoly (lam i) ((aeval (coeffShift (lam i)) q) (P i)) := by
      rw [map_sum]
      rw [Finset.sum_eq_single i]
      · exact polyAction_expPoly _ _ _
      · intro j hj hji
        exact hother j hji
      · simp
    have htail := polyAction_preserves_tail_zero q _ hsum
    unfold EventuallyAnnihilates at htail
    rw [haction] at htail
    have hker := (expPoly_eventually_zero_iff (lam i) (hlam i) _).mp htail
    exact coeffAction_ne_zero (lam i) q (P i) hqeval hPi hker
  · intro hP
    refine ⟨0, fun n hn => ?_⟩
    simp [hP, expPoly]

/-- Tail annihilation splits into exactly the original distinct components. -/
theorem eventual_annihilator_sum_iff {ι : Type*} [Fintype ι]
    (lam : ι → ℂ) (hlam : ∀ i, lam i ≠ 0) (hinj : Function.Injective lam)
    (P : ι → ℂ[X]) (q : ℂ[X]) :
    EventuallyAnnihilates q (∑ i, expPoly (lam i) (P i)) ↔
      ∀ i, EventuallyAnnihilates q (expPoly (lam i) (P i)) := by
  unfold EventuallyAnnihilates
  simp_rw [map_sum, polyAction_expPoly]
  rw [expPoly_sum_eventually_zero_iff lam hlam hinj]
  simp_rw [expPoly_eventually_zero_iff _ (hlam _)]

end PowerRank
