import CriticalHardcore.AdaptiveTrials
import CriticalHardcore.FirstDanger

/-! Finite word processes as actual adaptive trial trees. -/

set_option autoImplicit false

namespace CriticalHardcore
namespace WordTrials

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def continuations (live : List A → Prop) (p : List A) (n : ℕ) :
    Finset (List A) := by
  classical
  exact (words n).filter (fun w => live (p ++ w))

@[simp] theorem mem_continuations (live : List A → Prop) (p : List A) (n : ℕ) (w : List A) :
    w ∈ continuations live p n ↔ w.length = n ∧ live (p ++ w) := by
  classical
  simp [continuations]

noncomputable def blockWeight (B : ℕ) : ℝ := 1 / (Fintype.card A : ℝ) ^ B

noncomputable def build (live good : List A → Prop) (B : ℕ) : List A → ℕ → TrialTree
  | _, 0 => .leaf
  | p, r + 1 => by
      classical
      exact .node (decide (good p))
        ((continuations live p B).toList.map
          (fun b => (blockWeight (A := A) B, build live good B (p ++ b) r)))

theorem build_valid (live good : List A → Prop) (B : ℕ) (q : ℝ)
    (hgood : ∀ p, live p → good p →
      ((continuations live p B).card : ℝ) / (Fintype.card A : ℝ) ^ B ≤ 1)
    (hbad : ∀ p, live p → ¬ good p →
      ((continuations live p B).card : ℝ) / (Fintype.card A : ℝ) ^ B ≤ q)
    (p : List A) (hp : live p) (r : ℕ) :
    TrialTree.Valid q (build live good B p r) := by
  classical
  induction r generalizing p with
  | zero => exact TrialTree.Valid.leaf
  | succ r ih =>
      apply TrialTree.Valid.node
      · intro wc hwc
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hwc
        exact div_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) B)
      · by_cases hg : good p
        · simpa [blockWeight, List.map_map, Function.comp_def, nsmul_eq_mul,
            div_eq_mul_inv, hg] using hgood p hp hg
        · simpa [blockWeight, List.map_map, Function.comp_def, nsmul_eq_mul,
            div_eq_mul_inv, hg] using hbad p hp hg
      · intro wc hwc
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hwc
        exact ih (p ++ b) ((mem_continuations live p B b).mp (Finset.mem_toList.mp hb)).2

/-- A finite actual history and distinct good trial-start positions certify a count. -/
def GoodWitness (live : List A → Prop) (positions : List A → Finset ℕ)
    (p : List A) (n : ℕ) : Prop :=
  ∃ z : List A, p <+: z ∧ live z ∧ ∃ F : Finset ℕ,
    F.card = n ∧ F ⊆ positions z ∧ ∀ i ∈ F, p.length ≤ i

theorem build_goodWitness (live good : List A → Prop) (B : ℕ) (hB : 1 ≤ B)
    (positions : List A → Finset ℕ)
    (hgood : ∀ p z, p <+: z → live z → good p → p.length ∈ positions z)
    (p : List A) (hp : live p) (r n : ℕ)
    (hc : TrialTree.GoodCount (build live good B p r) n) :
    GoodWitness live positions p n := by
  classical
  induction r generalizing p n with
  | zero =>
      simp only [build] at hc
      cases hc
      exact ⟨p, List.prefix_refl _, hp, ∅, by simp, by simp, by simp⟩
  | succ r ih =>
      simp only [build] at hc
      cases hc with
      | root =>
          exact ⟨p, List.prefix_refl _, hp, ∅, by simp, by simp, by simp⟩
      | @step _ _ wc n hw ht =>
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
          have hb' := (mem_continuations live p B b).mp (Finset.mem_toList.mp hb)
          obtain ⟨z, hpz, hz, F, hFn, hFP, hFlow⟩ := ih (p ++ b) hb'.2 n ht
          have hprefix : p <+: z := (List.prefix_append p b).trans hpz
          by_cases hg : good p
          · have hnot : p.length ∉ F := by
              intro hm
              have hlow := hFlow p.length hm
              simp only [List.length_append, hb'.1] at hlow
              omega
            refine ⟨z, hprefix, hz, insert p.length F, ?_, ?_, ?_⟩
            · simp [hg, Finset.card_insert_of_not_mem hnot, hFn, Nat.add_comm]
            · intro i hi
              rcases Finset.mem_insert.mp hi with rfl | hi
              · exact hgood p z hprefix hz hg
              · exact hFP hi
            · intro i hi
              rcases Finset.mem_insert.mp hi with rfl | hi
              · exact le_rfl
              · have := hFlow i hi
                simp only [List.length_append] at this
                omega
          · refine ⟨z, hprefix, hz, F, ?_, hFP, ?_⟩
            · simpa [hg] using hFn
            · intro i hi
              have := hFlow i hi
              simp only [List.length_append] at this
              omega

theorem build_goodBudget (live good : List A → Prop) (B : ℕ) (hB : 1 ≤ B)
    (positions : List A → Finset ℕ) (K : ℕ)
    (hgood : ∀ p z, p <+: z → live z → good p → p.length ∈ positions z)
    (hbudget : ∀ z, live z → (positions z).card ≤ K)
    (p : List A) (hp : live p) (r : ℕ) :
    TrialTree.GoodBudget K (build live good B p r) := by
  intro n hc
  obtain ⟨z, _, hz, F, hFn, hFP, _⟩ :=
    build_goodWitness live good B hB positions hgood p hp r n hc
  rw [← hFn]
  exact (Finset.card_le_card hFP).trans (hbudget z hz)

end WordTrials
end CriticalHardcore
