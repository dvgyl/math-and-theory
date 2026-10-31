/-
Adapted from the same project's published continuation by autonomous agents,
reviewed and extended with Opus 5.5 (authorship disclosure in the source repo).
Source: dvgyl/math-and-theory, commit d43158abbe80c4899814061d1f3665cf12992452
(2026-10-30 19:48:54 UTC), papers/mathematics/artin-schreier-depth/lean/HahnClosureForward.lean,
theorem finiteDimensional_asTower. Apache-2.0 license; copy supplied in
third_party/LICENSE-APACHE-2.0.txt. This reused theorem is prior formal work.
Modifications: new module and theorem name to avoid namespace collisions;
modern mathlib port uses Set.image_mono for image monotonicity.
-/
import SupportAssembly

noncomputable section
attribute [local instance 2000] HahnSeries.instAlgebra
open HahnSeries IntermediateField Set Polynomial
namespace NTCThird
variable {k : Type*} [Field k]

theorem finiteDimensional_actual_asTower (p : ℕ) [Fact p.Prime]
    (K : IntermediateField k (HahnSeries ℚ k))
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (x : ℕ → HahnSeries ℚ k)
    (hF0 : F 0 = K.toSubfield)
    (hstep : ∀ i < N, ∃ a ∈ F i, x i ^ p - x i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {x i}).toSubfield)
    (M : IntermediateField K (HahnSeries ℚ k)) (hFN : F N = M.toSubfield) :
    FiniteDimensional K M := by
  classical
  let S : ℕ → IntermediateField K (HahnSeries ℚ k) :=
    fun n => IntermediateField.adjoin K (x '' Iio n)
  have hmono : ∀ n, F n ≤ F (n+1) ∨ N ≤ n := by
    intro n
    by_cases hn : n < N
    · left
      obtain ⟨a, _, _, hF⟩ := hstep n hn
      rw [hF]
      intro f hf
      exact IntermediateField.algebraMap_mem (IntermediateField.adjoin (F n) {x n}) ⟨f, hf⟩
    · right
      omega
  have hFS : ∀ n ≤ N, F n ≤ (S n).toSubfield := by
    intro n
    induction n with
    | zero =>
      intro _ f hf
      rw [hF0] at hf
      exact (S 0).algebraMap_mem ⟨f, hf⟩
    | succ n ih =>
      intro hn
      have hle : F n ≤ (S n).toSubfield := ih (Nat.le_trans (Nat.le_succ n) hn)
      have hSS : S n ≤ S (n+1) :=
        IntermediateField.adjoin.mono K _ _ (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ n)))
      obtain ⟨a, _, _, hF⟩ := hstep n (Nat.lt_of_succ_le hn)
      rw [hF]
      apply IntermediateField.adjoin_le_subfield
      · rintro f ⟨b, rfl⟩
        exact hSS (hle b.property)
      · intro f hf
        rw [Set.mem_singleton_iff.mp hf]
        exact IntermediateField.subset_adjoin K _ ⟨n, Nat.lt_succ_self n, rfl⟩
  have hmem : ∀ i < N, x i ∈ F N := by
    intro i hi
    have hxi : x i ∈ F (i+1) := by
      obtain ⟨a, _, _, hF⟩ := hstep i hi
      rw [hF]
      exact IntermediateField.subset_adjoin (F i) _ (Set.mem_singleton _)
    have hchain : ∀ m, i + 1 ≤ m → m ≤ N → x i ∈ F m := by
      intro m
      induction m with
      | zero => intro h; omega
      | succ m ih =>
        intro h1 h2
        rcases Nat.lt_or_ge i m with him | him
        · have hprev := ih (by omega) (by omega)
          rcases hmono m with h | h
          · exact h hprev
          · omega
        · have : m = i := by omega
          subst this
          exact hxi
    exact hchain N (by omega) le_rfl
  have hint : ∀ y ∈ x '' Iio N, IsIntegral K y := by
    rintro y ⟨i, hi, rfl⟩
    have h := isIntegral_actual_asTower p N F x hstep (x i) (hmem i hi)
    rw [hF0] at h
    exact h
  haveI : Finite (x '' Iio N) := ((Set.finite_Iio N).image x).to_subtype
  haveI : FiniteDimensional K (S N) := IntermediateField.finiteDimensional_adjoin hint
  have hMS : M ≤ S N := by
    intro y hy
    have : y ∈ F N := by rw [hFN]; exact hy
    exact hFS N le_rfl this
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hMS).toLinearMap
    (IntermediateField.inclusion hMS).injective

end NTCThird
