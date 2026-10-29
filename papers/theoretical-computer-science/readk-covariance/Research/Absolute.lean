import Research.DecisionTree

/-!
# Absolute tree covariance

The complement identity extends the signed covariance estimate to its absolute
value.  The logarithmic potential then controls the sum of absolute node
covariances, with the usual depth weights.
-/

open scoped BigOperators

namespace ReadK

@[simp] theorem val_not (b : Bool) : val (!b) = -val b := by
  cases b <;> norm_num [val]

theorem influence_not {n : ℕ} (g : BFun n) (i : Fin n) :
    influence (fun x => !(g x)) i = influence g i := by
  unfold influence
  apply avg_congr
  intro x
  cases h0 : g x <;> cases h1 : g (flip x i) <;> simp [h0, h1]

theorem mean_not {n : ℕ} (g : BFun n) :
    mean (fun x => !(g x)) = -mean g := by
  unfold mean
  calc
    avg (fun x => val (!(g x))) = avg (fun x => (-1 : ℝ) * val (g x)) := by
      apply avg_congr
      intro x
      rw [val_not]
      ring
    _ = (-1 : ℝ) * avg (fun x => val (g x)) := avg_const_mul _ _
    _ = -avg (fun x => val (g x)) := by ring

theorem cov_not_right {n : ℕ} (f g : BFun n) :
    cov f (fun x => !(g x)) = -cov f g := by
  unfold cov
  rw [mean_not]
  have havg :
      avg (fun x => val (f x) * val (!(g x))) =
        -avg (fun x => val (f x) * val (g x)) := by
    calc
      avg (fun x => val (f x) * val (!(g x))) =
          avg (fun x => (-1 : ℝ) * (val (f x) * val (g x))) := by
            apply avg_congr
            intro x
            rw [val_not]
            ring
      _ = (-1 : ℝ) * avg (fun x => val (f x) * val (g x)) := avg_const_mul _ _
      _ = -avg (fun x => val (f x) * val (g x)) := by ring
  rw [havg]
  ring

/-- The Boolean covariance estimate with an absolute value. -/
theorem abs_cov_le_sum_min {n : ℕ} (f g : BFun n) :
    |cov f g| ≤ ∑ i, min (influence f i) (influence g i) := by
  apply abs_le.mpr
  constructor
  · have h := cov_le_sum_min f (fun x => !(g x))
    rw [cov_not_right] at h
    simp only [influence_not] at h
    linarith
  · exact cov_le_sum_min f g

namespace Tree

noncomputable def absoluteCovariance {n : ℕ} : Tree n → ℝ
  | .leaf _ => 0
  | .node _ l r => |cov l.eval r.eval| +
      (l.absoluteCovariance + r.absoluteCovariance) / 2

theorem covariance_le_absoluteCovariance {n : ℕ} (t : Tree n) :
    t.covariance ≤ t.absoluteCovariance := by
  induction t with
  | leaf b => simp [covariance, absoluteCovariance]
  | node j l r ihl ihr =>
      simp only [covariance, absoluteCovariance]
      have hc := le_abs_self (cov l.eval r.eval)
      linarith

/-- The logarithmic potential controls absolute node covariances. -/
theorem absoluteCovariance_le_potential {n : ℕ} (t : Tree n) (ht : t.Regular) :
    t.absoluteCovariance ≤ t.potential := by
  induction t with
  | leaf b =>
      simp [absoluteCovariance, potential, count, logCount]
  | node j l r ihl ihr =>
      rcases ht with ⟨hl, hr, hlj, hrj⟩
      have hli := independent_of_count_zero l j hlj
      have hri := independent_of_count_zero r j hrj
      calc
        (node j l r).absoluteCovariance = |cov l.eval r.eval| +
            (l.absoluteCovariance + r.absoluteCovariance) / 2 := rfl
        _ ≤ (∑ i, min (influence l.eval i) (influence r.eval i)) +
            (l.potential + r.potential) / 2 := by
              have hc := abs_cov_le_sum_min l.eval r.eval
              have hpl := ihl hl
              have hpr := ihr hr
              linarith
        _ = ∑ i, (min (influence l.eval i) (influence r.eval i) +
            (influence l.eval i * logCount (l.count i) +
              influence r.eval i * logCount (r.count i)) / 2) := by
              simp only [potential, ← Finset.sum_div, Finset.sum_add_distrib]
        _ ≤ (node j l r).potential := by
              unfold potential
              apply Finset.sum_le_sum
              intro i hi
              by_cases hij : i = j
              · subst i
                have hil := influence_zero_of_count_zero l j hlj
                have hir := influence_zero_of_count_zero r j hrj
                simp [count, hlj, hrj, hil, hir, logCount]
              · have hif := influence_mux l.eval r.eval j i hij hli hri
                simpa only [eval, count, if_neg hij, zero_add, hif] using
                  logCount_potential (l.count i) (r.count i)
                    (influence l.eval i) (influence r.eval i)
                    (influence_nonneg l.eval i) (influence_nonneg r.eval i)
                    (fun h => influence_zero_of_count_zero l i h)
                    (fun h => influence_zero_of_count_zero r i h)

/-- Uniform read-k form for absolute tree covariance. -/
theorem absoluteCovariance_le_log_read_mul_influence {n : ℕ}
    (t : Tree n) (ht : t.Regular) (k : ℕ) (hk : ∀ i, t.count i ≤ k) :
    t.absoluteCovariance ≤ logCount k * t.totalInfluence := by
  calc
    t.absoluteCovariance ≤ t.potential := absoluteCovariance_le_potential t ht
    _ ≤ ∑ i, influence t.eval i * logCount k := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (logCount_mono (hk i)) (influence_nonneg t.eval i)
    _ = logCount k * t.totalInfluence := by
      simp only [totalInfluence, ← Finset.sum_mul]
      rw [mul_comm]

end Tree
end ReadK
