import RootGapCore
import HypersimplexSharp

/-!
An actual high-gap signed core obeys majority on every sign layer. Pair
deletion proves the sign assertion; no majority rule is assumed. This gives
the precise centered half-slice inequality needed by the sharp inverse.
-/

noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.GapMajoritySlice
open Breakthrough.GapFibers Breakthrough.GapCore Breakthrough.GapLayerRigidity
open Breakthrough.HypersimplexSharp

set_option maxHeartbeats 3000000

lemma signed_subset_sum {ι : Type*} [DecidableEq ι]
    (s A : Finset ι) (c : ι → ℝ) (hAs : A ⊆ s) :
    (∑ i ∈ s, c i * rademacherSign (if i ∈ A then false else true)) =
      (∑ i ∈ s, c i) - 2*(∑ i ∈ A, c i) := by
  have he : ∀ i, c i * rademacherSign (if i ∈ A then false else true) =
      c i - 2*(if i ∈ A then c i else 0) := by
    intro i
    by_cases hi : i ∈ A <;> simp [hi, rademacherSign] <;> ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  congr 1
  calc
    (∑ i ∈ s, if i ∈ A then c i else 0) = ∑ i ∈ s.filter (fun i => i ∈ A), c i := by
      rw [Finset.sum_filter]
    _ = ∑ i ∈ A, c i := by
      congr 1
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hAs h, h⟩⟩

/-- Every positive-majority assignment has the positive core margin. -/
theorem majority_subset_lower {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {x y a : ℝ} (hx : 0 < x) (hxy : x ≤ y) (ha : a < 2*x) :
    (∀ i ∈ s, x ≤ c i ∧ c i ≤ a) →
    (∀ ω : ι → Bool, y ≤ |∑ i ∈ s, c i*rademacherSign (ω i)|) →
    ∀ A : Finset ι, A ⊆ s → 2*A.card < s.card →
      y ≤ (∑ i ∈ s, c i) - 2*(∑ i ∈ A, c i) := by
  classical
  induction' s using Finset.strongInductionOn with s ih
  intro hc hg A hAs hmajor
  have hy : 0 < y := hx.trans_le hxy
  by_cases hA : A = ∅
  · have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hi⟩ := hsne
    have hpos : 0 < ∑ j ∈ s, c j := by
      apply Finset.sum_pos'
      · intro j hj
        exact (hx.trans_le (hc j hj).1).le
      · exact ⟨i, hi, hx.trans_le (hc i hi).1⟩
    have h := hg (fun _ => true)
    simp [rademacherSign] at h
    rw [abs_of_pos hpos] at h
    simpa only [hA, Finset.sum_empty, mul_zero, sub_zero] using h
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hA
    obtain ⟨i, hi, hiA⟩ := Finset.exists_mem_not_mem_of_card_lt_card
      (show A.card < s.card by omega)
    have hjS := hAs hj
    have hij : i ≠ j := by intro e; exact hiA (e.symm ▸ hj)
    have hjE : j ∈ s.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hjS⟩
    let s' := (s.erase i).erase j
    let A' := A.erase j
    have hsmall : s' ⊂ s :=
      Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset j (s.erase i))
        (Finset.erase_ssubset hi)
    have hAc : A'.card+1 = A.card := Finset.card_erase_add_one hj
    have hsc : s'.card+2 = s.card := by
      have h1 := Finset.card_erase_add_one hi
      have h2 := Finset.card_erase_add_one hjE
      dsimp [s']
      omega
    have hAs' : A' ⊆ s' := by
      intro q hq
      have hqj := (Finset.mem_erase.mp hq).1
      have hqA := (Finset.mem_erase.mp hq).2
      have hqi : q ≠ i := by intro e; exact hiA (e ▸ hqA)
      exact Finset.mem_erase.mpr ⟨hqj, Finset.mem_erase.mpr ⟨hqi, hAs hqA⟩⟩
    have hct : ∀ q ∈ s', x ≤ c q ∧ c q ≤ a := by
      intro q hq
      exact hc q (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq))
    have hgt := erase_pair_preserves_gap s c hxy ha hc hg hi hjS hij
    have hrec := ih s' hsmall hct hgt A' hAs' (by omega)
    have hSi := Finset.add_sum_erase s c hi
    have hSj := Finset.add_sum_erase (s.erase i) c hjE
    have hAj := Finset.add_sum_erase A c hj
    have he : (∑ q ∈ s, c q) - 2*(∑ q ∈ A, c q) =
        ((∑ q ∈ s', c q) - 2*(∑ q ∈ A', c q)) + (c i-c j) := by
      dsimp [s', A']
      linarith only [hSi, hSj, hAj]
    have hci := hc i hi
    have hcj := hc j hjS
    have hdiff : -y < c i-c j := by linarith only [hci.1, hcj.2, ha, hxy]
    have hpos : 0 < (∑ q ∈ s, c q) - 2*(∑ q ∈ A, c q) := by
      rw [he]
      linarith only [hrec, hdiff]
    have h := hg (fun q => if q ∈ A then false else true)
    rw [signed_subset_sum s A c hAs, abs_of_pos hpos] at h
    exact h

/-- The centered nearest positive slice has the exact subset-sum bound.
It is derived from the actual high-gap core, including its tail margin. -/
theorem centered_core_subset_bound {k h : ℕ} (c : Fin k → ℝ)
    {x y a : ℝ} (hx : 0 < x) (hxy : x ≤ y) (ha : a < 2*x)
    (hc : ∀ i, x ≤ c i ∧ c i ≤ a)
    (hg : ∀ ω : BoolCube k, y ≤ |rademacherSum c ω|)
    (hk : k = 2*h+1) (β : ℝ) (hmean : ∑ i, c i = (k : ℝ)*β) :
    ∀ A : Finset (Fin k), A.card = h →
      ∑ i ∈ A, (c i-β) ≤ (β-y)/2 := by
  intro A hA
  have hs := majority_subset_lower Finset.univ c hx hxy ha
    (fun i _ => hc i) hg A (Finset.subset_univ _)
    (by simpa only [Finset.card_univ, Fintype.card_fin, hA, hk] using
      (show 2*h < 2*h+1 by omega))
  rw [hmean] at hs
  have hkR : (k : ℝ) = 2*(h : ℝ)+1 := by exact_mod_cast hk
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hA]
  nlinarith only [hs, congrArg (fun t : ℝ => t*β) hkR]

#print axioms signed_subset_sum
#print axioms majority_subset_lower
#print axioms centered_core_subset_bound

end Breakthrough.GapMajoritySlice
