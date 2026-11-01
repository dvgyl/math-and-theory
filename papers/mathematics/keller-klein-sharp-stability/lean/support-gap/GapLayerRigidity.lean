import RootGapFibers

/-!
Concrete high-gap rigidity for a finite core. The proof deletes pairs with
opposite signs; it does not assume a majority rule, layer connectivity, or
any moment formula. It proves the stronger conclusion that the gap is at
most every individual core coefficient.
-/

open scoped BigOperators
open KellerKlein Breakthrough.AdversarialCentralGap Breakthrough.GapFibers

set_option maxHeartbeats 3000000

namespace Breakthrough.GapLayerRigidity
noncomputable section

lemma scalar_pair_gap {z d y : ℝ} (hd : |d| < y)
    (hm : y ≤ |z-d|) (hp : y ≤ |z+d|) : y ≤ |z| := by
  by_cases hd0 : 0 ≤ d
  · have h := scalar_fiber_radius hd0 (by simpa [abs_of_nonneg hd0] using hd) hm hp
    linarith only [h, hd0]
  · have hd0' : 0 ≤ -d := by linarith
    have h := scalar_fiber_radius hd0'
      (by simpa [abs_of_neg (lt_of_not_ge hd0)] using hd)
      (by simpa using hp) (by simpa using hm)
    linarith only [h, hd0']

lemma signed_sum_pair {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c : ι → ℝ) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (ω : ι → Bool) (bi bj : Bool) :
    (∑ k ∈ s, c k * rademacherSign
      (if k = i then bi else if k = j then bj else ω k)) =
      c i * rademacherSign bi + c j * rademacherSign bj +
        ∑ k ∈ (s.erase i).erase j, c k * rademacherSign (ω k) := by
  have hji : j ∈ s.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  calc
    _ = c i * rademacherSign bi +
        ∑ k ∈ s.erase i, c k * rademacherSign (if k = j then bj else ω k) := by
      conv_lhs => rw [← Finset.insert_erase hi]
      exact sum_insert_sign (s.erase i) i (Finset.not_mem_erase i s) c
        (fun k => if k = j then bj else ω k) bi
    _ = c i * rademacherSign bi + (c j * rademacherSign bj +
        ∑ k ∈ (s.erase i).erase j, c k * rademacherSign (ω k)) := by
      congr 1
      conv_lhs => rw [← Finset.insert_erase hji]
      exact sum_insert_sign ((s.erase i).erase j) j
        (Finset.not_mem_erase j (s.erase i)) c ω bj
    _ = _ := by ring

/-- Deleting any two coefficients preserves a support gap when the width of
the coefficient interval is strictly smaller than that gap. -/
theorem erase_pair_preserves_gap {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℝ) {x y a : ℝ}
    (hxy : x ≤ y) (ha : a < 2*x)
    (hc : ∀ i ∈ s, x ≤ c i ∧ c i ≤ a)
    (hgap : ∀ ω : ι → Bool, y ≤ |∑ k ∈ s, c k * rademacherSign (ω k)|)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    ∀ ω : ι → Bool,
      y ≤ |∑ k ∈ (s.erase i).erase j, c k * rademacherSign (ω k)| := by
  intro ω
  have hci := hc i hi
  have hcj := hc j hj
  have hd : |c i-c j| < y := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hp := hgap (fun k => if k = i then true else if k = j then false else ω k)
  have hm := hgap (fun k => if k = i then false else if k = j then true else ω k)
  rw [signed_sum_pair s c hi hj hij ω true false] at hp
  rw [signed_sum_pair s c hi hj hij ω false true] at hm
  simp only [sign_true, sign_false, mul_one, mul_neg_one] at hp hm
  apply scalar_pair_gap hd
  · convert hm using 1
    congr 1
    ring
  · convert hp using 1
    congr 1
    ring

/-- A high-gap core has odd cardinality, and every coefficient is at least
the full core gap. This is a statement about all actual sign outcomes. -/
theorem finset_high_gap_odd_and_coeff {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) {x y a : ℝ} (hx : 0 < x) (hxy : x ≤ y) (ha : a < 2*x)
    (hc : ∀ i ∈ s, x ≤ c i ∧ c i ≤ a)
    (hgap : ∀ ω : ι → Bool, y ≤ |∑ k ∈ s, c k * rademacherSign (ω k)|) :
    Odd s.card ∧ ∀ i ∈ s, y ≤ c i := by
  classical
  revert hc hgap
  induction' s using Finset.strongInductionOn with s ih
  intro hc hgap
  have hy : 0 < y := hx.trans_le hxy
  have hne : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hg := hgap (fun _ => true)
    simp [he] at hg
    linarith
  obtain ⟨i, hi⟩ := hne
  by_cases hcard : s.card = 1
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
    have hcj := hc j (by simp)
    have hg := hgap (fun _ => true)
    simp only [Finset.sum_singleton, sign_true, mul_one] at hg
    rw [abs_of_pos (hx.trans_le hcj.1)] at hg
    refine ⟨by simp, ?_⟩
    intro k hk
    have he : k = j := Finset.mem_singleton.mp hk
    simpa only [he] using hg
  · have hcgt : 1 < s.card := by
      have hp := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne hcgt i
    have hj' : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
    have hsmall : (s.erase i).erase j ⊂ s :=
      Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset j (s.erase i))
        (Finset.erase_ssubset hi)
    have hct : ∀ k ∈ (s.erase i).erase j, x ≤ c k ∧ c k ≤ a := by
      intro k hk
      exact hc k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk))
    have hgt := erase_pair_preserves_gap s c hxy ha hc hgap hi hj (Ne.symm hji)
    have hoddT := (ih ((s.erase i).erase j) hsmall hct hgt).1
    have hcardT : ((s.erase i).erase j).card + 2 = s.card := by
      have h1 := Finset.card_erase_add_one hi
      have h2 := Finset.card_erase_add_one hj'
      omega
    have hodd : Odd s.card := by
      obtain ⟨m, hm⟩ := hoddT
      exact ⟨m+1, by omega⟩
    refine ⟨hodd, ?_⟩
    intro q hq
    have hc3 : 3 ≤ s.card := by
      obtain ⟨m, hm⟩ := hodd
      omega
    obtain ⟨u, hu, huq⟩ := Finset.exists_mem_ne hcgt q
    have herase : 1 < (s.erase u).card := by
      have he := Finset.card_erase_add_one hu
      omega
    obtain ⟨v, hv, hvq⟩ := Finset.exists_mem_ne herase q
    have hvu := (Finset.mem_erase.mp hv).1
    have hvs := Finset.mem_of_mem_erase hv
    have hqT : q ∈ (s.erase u).erase v := by
      exact Finset.mem_erase.mpr ⟨Ne.symm hvq,
        Finset.mem_erase.mpr ⟨Ne.symm huq, hq⟩⟩
    have hsmall' : (s.erase u).erase v ⊂ s :=
      Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset v (s.erase u))
        (Finset.erase_ssubset hu)
    have hct' : ∀ k ∈ (s.erase u).erase v, x ≤ c k ∧ c k ≤ a := by
      intro k hk
      exact hc k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk))
    have hgt' := erase_pair_preserves_gap s c hxy ha hc hgap hu hvs (Ne.symm hvu)
    exact (ih ((s.erase u).erase v) hsmall' hct' hgt').2 q hqT

/-- The requested actual finite-cube interface, with the stronger individual
coefficient lower bound retained. -/
theorem high_gap_odd_and_coeff {k : ℕ} (c : Fin k → ℝ) {x y a : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (ha : a < 2*x)
    (hc : ∀ i, x ≤ c i ∧ c i ≤ a)
    (hgap : ∀ ω : BoolCube k, y ≤ |rademacherSum c ω|) :
    Odd k ∧ ∀ i, y ≤ c i := by
  simpa only [Finset.card_univ, Fintype.card_fin, Finset.mem_univ,
    forall_const, rademacherSum] using
    finset_high_gap_odd_and_coeff Finset.univ c hx hxy ha
      (fun i _ => hc i) hgap

theorem high_gap_odd_and_mean {k : ℕ} (c : Fin k → ℝ) {x y a : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (ha : a < 2*x)
    (hc : ∀ i, x ≤ c i ∧ c i ≤ a)
    (hgap : ∀ ω : BoolCube k, y ≤ |rademacherSum c ω|) :
    Odd k ∧ (k : ℝ)*y ≤ ∑ i, c i := by
  have h := high_gap_odd_and_coeff c hx hxy ha hc hgap
  refine ⟨h.1, ?_⟩
  simpa [nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ)
    (f := fun _ : Fin k => y) (g := c) (fun i _ => h.2 i)

theorem high_gap_odd_and_variance {k : ℕ} (c : Fin k → ℝ) {x y a : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (ha : a < 2*x)
    (hc : ∀ i, x ≤ c i ∧ c i ≤ a)
    (hgap : ∀ ω : BoolCube k, y ≤ |rademacherSum c ω|) :
    Odd k ∧ (k : ℝ)*y^2 ≤ ∑ i, c i^2 := by
  have h := high_gap_odd_and_coeff c hx hxy ha hc hgap
  refine ⟨h.1, ?_⟩
  have hy : 0 ≤ y := (hx.trans_le hxy).le
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (f := fun _ : Fin k => y^2) (g := fun i => c i^2)
    (fun i _ => sq_le_sq₀ hy (hx.trans_le (hc i).1).le |>.mpr (h.2 i))
  simpa [nsmul_eq_mul] using hs

#print axioms erase_pair_preserves_gap
#print axioms finset_high_gap_odd_and_coeff
#print axioms high_gap_odd_and_coeff
#print axioms high_gap_odd_and_mean
#print axioms high_gap_odd_and_variance

end
end Breakthrough.GapLayerRigidity
