import CriticalHardcore.WeightedTree

set_option autoImplicit false

namespace CriticalHardcore
namespace WeightedTree

variable {V : Type*}

/-- Total influence majorant through `k` edges below the starting root. -/
def truncatedTotal (t : WeightedTree V) (k : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range k, forestMass t.children j

@[simp] theorem truncatedTotal_zero (t : WeightedTree V) : truncatedTotal t 0 = 1 := by
  simp [truncatedTotal]

private theorem sum_range_list {A : Type*} (l : List A) (f : A → ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range k, (l.map (fun a => f a j)).sum) =
      (l.map (fun a => ∑ j ∈ Finset.range k, f a j)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

theorem truncatedTotal_succ (t : WeightedTree V) (k : ℕ) :
    truncatedTotal t (k + 1) =
      1 + (t.children.map (fun c => c.message * truncatedTotal c k)).sum := by
  unfold truncatedTotal
  rw [Finset.sum_range_succ']
  simp only [forestMass, mass]
  rw [sum_range_list]
  simp_rw [← Finset.mul_sum]
  simp only [mul_add, mul_one, List.sum_map_add]
  ring

theorem truncatedTotal_nonneg {d pmax : ℝ} {t : WeightedTree V}
    (h : ∀ c ∈ t.children, Good d pmax c) (k : ℕ) :
    0 ≤ truncatedTotal t k := by
  unfold truncatedTotal
  apply add_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro j _
  unfold forestMass
  apply List.sum_nonneg
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact mass_nonneg (h c hc) j

end WeightedTree
end CriticalHardcore
