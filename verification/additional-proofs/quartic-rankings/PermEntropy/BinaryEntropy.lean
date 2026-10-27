import PermEntropy.FiniteEntropy
import PermEntropy.Slice

/-!
# Entropy loss for an interleaving word

No uniformity assumption is imposed on the word distribution. The fixed
cardinality slice supplies the reference partition function in Gibbs'
variational inequality.
-/

open scoped BigOperators

namespace PermEntropy
namespace FinDist

theorem binaryWord_entropy_le_log_choose {q r : ℕ}
    (p : FinDist (Fin q → Bool))
    (hcount : ∀ w, p.mass w ≠ 0 → wordCount w = r) :
    p.entropy ≤ Real.log (q.choose r : ℝ) -
      (p.expect wordCrossing)^2 / (2 * (q : ℝ)^3) := by
  classical
  by_cases hq : q = 0
  · subst q
    rw [p.entropy_of_subsingleton]
    cases r <;> simp
  let S : Finset (Fin q → Bool) := Finset.univ.filter (fun w => wordCount w = r)
  have hsupp : ∀ w, w ∉ S → p.mass w = 0 := by
    intro w hw
    by_contra hp
    exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hcount w hp⟩)
  obtain ⟨w, hw⟩ := p.support_nonempty S hsupp
  have hrq : r ≤ q := by
    have heq : wordCount w = r := (Finset.mem_filter.mp hw).2
    simpa [heq] using wordCount_le w
  have hN : 0 < (q.choose r : ℝ) := by exact_mod_cast Nat.choose_pos hrq
  have hK : 0 < (q : ℝ)^3 := by
    have hqp : 0 < q := Nat.pos_of_ne_zero hq
    positivity
  apply p.entropy_le_log_card_sub_mean_sq_of_partition_bound S hsupp
    wordCrossing (q.choose r) ((q : ℝ)^3) hN hK
  intro t
  simpa [S, fixedWordPartition, Finset.sum_filter] using fixedWordPartition_le q r t

theorem binaryWord_entropy_le_log_choose_map {α : Type*} [Fintype α]
    (p : FinDist α) {q : ℕ} (Y : α → Fin q → Bool) (r : ℕ)
    (hcount : ∀ a, wordCount (Y a) = r) :
    (p.map Y).entropy ≤ Real.log (q.choose r : ℝ) -
      (p.expect (fun a => wordCrossing (Y a)))^2 / (2 * (q : ℝ)^3) := by
  have hsupp : ∀ w, (p.map Y).mass w ≠ 0 → wordCount w = r := by
    intro w hw
    by_contra hn
    apply hw
    rw [map_mass]
    apply Finset.sum_eq_zero
    intro a ha
    split_ifs with h
    · exact False.elim (hn (h ▸ hcount a))
    · rfl
  simpa only [map_expect] using (p.map Y).binaryWord_entropy_le_log_choose hsupp

end FinDist
end PermEntropy
