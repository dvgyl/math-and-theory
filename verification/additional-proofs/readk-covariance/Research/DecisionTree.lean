import Research.Cube
import Research.LogPotential
import Lean.Elab.Tactic.Omega

/-!
# A logarithmic covariance bound for Boolean decision trees

The Boolean cube, uniform influences, and covariance are defined in `Research.Cube`.
A tree is regular when a variable is never queried twice on a root-to-leaf path.
-/

open scoped BigOperators

namespace ReadK

inductive Tree (n : ℕ) where
  | leaf : Bool → Tree n
  | node : Fin n → Tree n → Tree n → Tree n
deriving DecidableEq

namespace Tree

def eval {n : ℕ} : Tree n → BFun n
  | .leaf b => fun _ => b
  | .node j l r => fun x => if x j then r.eval x else l.eval x

def count {n : ℕ} : Tree n → Fin n → ℕ
  | .leaf _, _ => 0
  | .node j l r, i => (if i = j then 1 else 0) + l.count i + r.count i

def Regular {n : ℕ} : Tree n → Prop
  | .leaf _ => True
  | .node j l r => l.Regular ∧ r.Regular ∧ l.count j = 0 ∧ r.count j = 0

noncomputable def covariance {n : ℕ} : Tree n → ℝ
  | .leaf _ => 0
  | .node _ l r => cov l.eval r.eval + (l.covariance + r.covariance) / 2

noncomputable def potential {n : ℕ} (t : Tree n) : ℝ :=
  ∑ i, influence t.eval i * logCount (t.count i)

noncomputable def totalInfluence {n : ℕ} (t : Tree n) : ℝ :=
  ∑ i, influence t.eval i

theorem independent_of_count_zero {n : ℕ} (t : Tree n) (i : Fin n)
    (ht : t.count i = 0) : independent t.eval i := by
  induction t with
  | leaf b =>
      intro x
      rfl
  | node j l r ihl ihr =>
      have hij : i ≠ j := by
        intro heq
        subst i
        simp [count] at ht
      have hl : l.count i = 0 := by
        simp [count, hij] at ht
        omega
      have hr : r.count i = 0 := by
        simp [count, hij] at ht
        omega
      intro x
      have he : flip x i j = x j := by
        simp [flip, Function.update_of_ne (Ne.symm hij)]
      simp only [eval, he]
      split <;> first | exact ihr hr x | exact ihl hl x

theorem influence_zero_of_count_zero {n : ℕ} (t : Tree n) (i : Fin n)
    (ht : t.count i = 0) : influence t.eval i = 0 :=
  influence_zero_of_independent (independent_of_count_zero t i ht)

/-- The variable-weighted logarithmic covariance inequality. -/
theorem covariance_le_potential {n : ℕ} (t : Tree n) (ht : t.Regular) :
    t.covariance ≤ t.potential := by
  induction t with
  | leaf b =>
      simp [covariance, potential, count, logCount]
  | node j l r ihl ihr =>
      rcases ht with ⟨hl, hr, hlj, hrj⟩
      have hli := independent_of_count_zero l j hlj
      have hri := independent_of_count_zero r j hrj
      calc
        (node j l r).covariance =
            cov l.eval r.eval + (l.covariance + r.covariance) / 2 := rfl
        _ ≤ (∑ i, min (influence l.eval i) (influence r.eval i)) +
            (l.potential + r.potential) / 2 := by
              have hc := cov_le_sum_min l.eval r.eval
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

/-- Uniform read-k version, including the harmless zero-count convention. -/
theorem covariance_le_log_read_mul_influence {n : ℕ} (t : Tree n) (ht : t.Regular)
    (k : ℕ) (hk : ∀ i, t.count i ≤ k) :
    t.covariance ≤ logCount k * t.totalInfluence := by
  calc
    t.covariance ≤ t.potential := covariance_le_potential t ht
    _ ≤ ∑ i, influence t.eval i * logCount k := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (logCount_mono (hk i)) (influence_nonneg t.eval i)
    _ = logCount k * t.totalInfluence := by
      simp only [totalInfluence, ← Finset.sum_mul]
      rw [mul_comm]

end Tree
end ReadK
