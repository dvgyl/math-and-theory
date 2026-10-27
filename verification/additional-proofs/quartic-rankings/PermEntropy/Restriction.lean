import PermEntropy.Ranking
import PermEntropy.Cut
import PermEntropy.Comparison

noncomputable section
open scoped BigOperators
namespace PermEntropy
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A subset viewed inside a larger finite set. -/
def inside (Q S : Finset V) : Finset Q := Finset.univ.filter (fun x => x.val ∈ S)

omit [Fintype V] in
@[simp] theorem mem_inside (Q S : Finset V) (x : Q) : x ∈ inside Q S ↔ x.val ∈ S := by
  simp [inside]

omit [Fintype V] in
theorem card_inside (Q S : Finset V) (h : S ⊆ Q) : (inside Q S).card = S.card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact (mem_inside Q S x).mp hx
  · intro x hx y hy heq
    exact Subtype.ext heq
  · intro x hx
    exact ⟨⟨x,h hx⟩, (mem_inside Q S _).mpr hx, rfl⟩

omit [Fintype V] in
theorem sum_inside {M : Type*} [AddCommMonoid M] (Q S : Finset V) (h : S ⊆ Q) (f : V → M) :
    ∑ x ∈ inside Q S, f x.val = ∑ x ∈ S, f x := by
  apply Finset.sum_bij (fun x _ => x.val)
  · intro x hx
    exact (mem_inside Q S x).mp hx
  · intro x hx y hy heq
    exact Subtype.ext heq
  · intro x hx
    exact ⟨⟨x,h hx⟩, (mem_inside Q S _).mpr hx, rfl⟩
  · intro x hx
    rfl

omit [Fintype V] in
theorem inside_union_compl (L R : Finset V) (h : Disjoint L R) :
    (inside (L ∪ R) R)ᶜ = inside (L ∪ R) L := by
  ext x
  simp only [Finset.mem_compl, mem_inside]
  have hx := x.property
  simp only [Finset.mem_union] at hx
  constructor
  · intro hn
    exact hx.resolve_right hn
  · intro hl hr
    exact Finset.disjoint_left.mp h hl hr

omit [Fintype V] in
theorem cutSum_inside_union (B : V → V → ℝ) (L R : Finset V) (h : Disjoint L R) :
    cutSum (fun u v : ↑(L ∪ R) => B u.val v.val)
      (inside (L ∪ R) R)ᶜ (inside (L ∪ R) R) = cutSum B L R := by
  rw [inside_union_compl L R h]
  unfold cutSum
  calc
    _ = ∑ u ∈ inside (L ∪ R) L, ∑ v ∈ R, B u.val v := by
      apply Finset.sum_congr rfl
      intro u hu
      exact sum_inside (L ∪ R) R Finset.subset_union_right (fun v => B u.val v)
    _ = _ := sum_inside (L ∪ R) L Finset.subset_union_left (fun u => ∑ v ∈ R, B u v)

namespace FinDist

/-- Unconditional restriction preserves every pairwise comparison bias. -/
theorem biased_restrict (p : FinDist (Ranking V)) (b : ℝ)
    (hbias : ∀ u v : V, u ≠ v → b ≤ |p.meanComparison u v|) (s : Finset V) :
    ∀ u v : s, u ≠ v →
      b ≤ |(p.map (fun r => r.restrict s)).meanComparison u v| := by
  intro u v huv
  rw [meanComparison_restrict]
  exact hbias u.val v.val (fun h => huv (Subtype.ext h))

/-- The comparison cut computed inside the induced ranking on a disjoint
union is exactly the corresponding cut in the original comparison matrix. -/
theorem meanComparison_cut_restrict_union (p : FinDist (Ranking V))
    (L R : Finset V) (hd : Disjoint L R) :
    cutSum (p.map (fun r => r.restrict (L ∪ R))).meanComparison
      (inside (L ∪ R) R)ᶜ (inside (L ∪ R) R) = cutSum p.meanComparison L R := by
  simpa only [cutSum, meanComparison_restrict] using
    cutSum_inside_union p.meanComparison L R hd

end FinDist

end PermEntropy
