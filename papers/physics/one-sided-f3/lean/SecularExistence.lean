import SecularBranches
import Mathlib.Topology.Order.IntermediateValue

/-! Existence and uniqueness of the secular solution. These results prove that
the branches in SecularBranches exhaust every finite real diagonal quadratic. -/

noncomputable section
open scoped BigOperators
namespace FilteredF3
variable {ι : Type*} [Fintype ι]

theorem radiusSq_nonneg (g : ι → ℝ) : 0 ≤ radiusSq g :=
  Finset.sum_nonneg fun i _ => sq_nonneg (g i)

theorem secular_nonneg (h g : ι → ℝ) (μ : ℝ) : 0 ≤ secular h g μ :=
  Finset.sum_nonneg fun i _ => sq_nonneg (g i / (μ - h i))

/-- An explicit finite upper bracket, requiring no limiting argument. -/
theorem secular_large_bound (h g : ι → ℝ) (a : ℝ)
    (ha : ∀ i, h i ≤ a) :
    secular h g (a + radiusSq g + 1) < 1 := by
  have hR : 0 ≤ radiusSq g := radiusSq_nonneg g
  have hd : 0 < (radiusSq g + 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hterm : ∀ i, (g i / (a + radiusSq g + 1 - h i)) ^ 2 ≤
      (g i) ^ 2 / (radiusSq g + 1) ^ 2 := by
    intro i
    have hden : radiusSq g + 1 ≤ a + radiusSq g + 1 - h i := by linarith [ha i]
    have hsq : (radiusSq g + 1) ^ 2 ≤ (a + radiusSq g + 1 - h i) ^ 2 := by
      apply (sq_le_sq₀ (by linarith) (by linarith)).mpr hden
    rw [div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hd hsq
  have hsum : secular h g (a + radiusSq g + 1) ≤ radiusSq g / (radiusSq g + 1) ^ 2 := by
    unfold secular radiusSq at *
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i _ => hterm i
  have hlt : radiusSq g / (radiusSq g + 1) ^ 2 < 1 := by
    apply (div_lt_one hd).mpr
    nlinarith [sq_nonneg (radiusSq g)]
  exact lt_of_le_of_lt hsum hlt

/-- The secular function is continuous at an endpoint even if its denominator
vanishes, provided the corresponding numerator is identically zero. -/
theorem secular_continuousOn (h g : ι → ℝ) (a b : ℝ)
    (ha : ∀ i, g i = 0 ∨ h i < a) :
    ContinuousOn (secular h g) (Set.Icc a b) := by
  unfold secular
  apply continuousOn_finset_sum
  intro i hi
  rcases ha i with hg | hh
  · simp only [hg, zero_div, zero_pow (by norm_num : 2 ≠ 0)]
    exact continuousOn_const
  · apply ContinuousOn.pow
    apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
    intro x hx
    exact ne_of_gt (sub_pos.mpr (lt_of_lt_of_le hh hx.1))

/-- If the secular value exceeds one at an admissible lower endpoint, there
is a root strictly to its right, with an explicit finite upper bracket. -/
theorem exists_secular_root (h g : ι → ℝ) (a : ℝ)
    (ha : ∀ i, h i ≤ a) (hcompat : ∀ i, g i = 0 ∨ h i < a)
    (hhigh : 1 < secular h g a) :
    ∃ μ : ℝ, a < μ ∧ μ ≤ a + radiusSq g + 1 ∧ secular h g μ = 1 := by
  have hR := radiusSq_nonneg g
  have hab : a ≤ a + radiusSq g + 1 := by linarith
  have hc := secular_continuousOn h g a (a + radiusSq g + 1) hcompat
  have hlow := secular_large_bound h g a ha
  have hmem : (1 : ℝ) ∈ Set.Icc (secular h g (a + radiusSq g + 1)) (secular h g a) :=
    ⟨hlow.le, hhigh.le⟩
  obtain ⟨μ, hμ, heq⟩ := intermediate_value_Icc' hab hc hmem
  refine ⟨μ, ?_, hμ.2, heq⟩
  exact lt_of_le_of_ne hμ.1 (by intro he; subst μ; linarith)

/-- A nonzero component on the top eigenspace supplies an explicit point
where the secular function is at least four. -/
theorem secular_top_component (h g : ι → ℝ) (a : ℝ) (k : ι)
    (hk : h k = a) (hg : g k ≠ 0) :
    1 < secular h g (a + |g k| / 2) := by
  have habs : 0 < |g k| := abs_pos.mpr hg
  have hterm : (g k / (a + |g k| / 2 - h k)) ^ 2 = 4 := by
    rw [hk]
    have hden : a + |g k| / 2 - a = |g k| / 2 := by ring
    rw [hden, div_pow]
    have habs2 := sq_abs (g k)
    field_simp
    nlinarith [habs2]
  have hs : (g k / (a + |g k| / 2 - h k)) ^ 2 ≤ secular h g (a + |g k| / 2) :=
    by
      unfold secular
      exact Finset.single_le_sum (f := fun i => (g i / (a + |g k| / 2 - h i)) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ k)
  linarith

/-- The complete regular/hard/interior branch dichotomy. No spectral value,
root, stationary point, or extremizer is assumed to exist. -/
theorem exhaustive_branches (h g : ι → ℝ) (l : ℝ)
    (hdiag : ∀ i, h i ≤ l) :
    ((∀ i, h i = l → g i = 0) ∧ secular h g l ≤ 1) ∨
      ∃ μ, l < μ ∧ secular h g μ = 1 := by
  by_cases hc : ∀ i, h i = l → g i = 0
  · by_cases hs : secular h g l ≤ 1
    · exact Or.inl ⟨hc, hs⟩
    · right
      have hcompat : ∀ i, g i = 0 ∨ h i < l := by
        intro i
        by_cases hi : h i = l
        · exact Or.inl (hc i hi)
        · exact Or.inr (lt_of_le_of_ne (hdiag i) hi)
      obtain ⟨μ, hμ, _, hs'⟩ := exists_secular_root h g l hdiag hcompat (lt_of_not_ge hs)
      exact ⟨μ, hμ, hs'⟩
  · push_neg at hc
    obtain ⟨k, hk, hg⟩ := hc
    have ha : l < l + |g k| / 2 := by have := abs_pos.mpr hg; linarith
    have hdiag' : ∀ i, h i ≤ l + |g k| / 2 := fun i => le_trans (hdiag i) ha.le
    have hcompat : ∀ i, g i = 0 ∨ h i < l + |g k| / 2 :=
      fun i => Or.inr (lt_of_le_of_lt (hdiag i) ha)
    obtain ⟨μ, hμ, _, hs⟩ := exists_secular_root h g (l + |g k| / 2) hdiag' hcompat
      (secular_top_component h g l k hk hg)
    exact Or.inr ⟨μ, lt_trans ha hμ, hs⟩

/-- A sharp value always exists, and one of the explicit branches computes it.
The threshold hypotheses are exactly l=max(0,max_i h_i). -/
theorem exact_value_exists [DecidableEq ι] (τ : ℝ) (h g : ι → ℝ) (l : ℝ)
    (hl : 0 ≤ l) (hdiag : ∀ i, h i ≤ l)
    (hendpoint : l = 0 ∨ ∃ k, h k = l) :
    ∃ μ, l ≤ μ ∧
      ((μ = l ∧ (∀ i, h i = l → g i = 0) ∧ secular h g l ≤ 1) ∨
        (l < μ ∧ secular h g μ = 1)) ∧
      IsGreatest {v : ℝ | ∃ x : ι → ℝ, radiusSq x ≤ 1 ∧ diagObjective τ h g x = v}
        (secularValue τ h g μ) := by
  rcases exhaustive_branches h g l hdiag with ⟨hc, hs⟩ | ⟨μ, hμ, hs⟩
  · refine ⟨l, le_rfl, Or.inl ⟨rfl, hc, hs⟩, ?_⟩
    rcases hendpoint with hzero | ⟨k, hk⟩
    · subst l
      exact (zero_branch τ h g hdiag hc hs).1
    · exact hard_case_attained τ l h g hl hdiag hc hs k hk
  · refine ⟨μ, hμ.le, Or.inr ⟨hμ, hs⟩, ?_⟩
    exact (regular_branch τ μ h g (le_trans hl hμ.le)
      (fun i => lt_of_le_of_lt (hdiag i) hμ) hs).1

section Threshold
variable [Nonempty ι]

def spectralThreshold (h : ι → ℝ) : ℝ :=
  max 0 (Finset.univ.sup' Finset.univ_nonempty h)

theorem spectralThreshold_nonneg (h : ι → ℝ) : 0 ≤ spectralThreshold h :=
  le_max_left _ _

theorem le_spectralThreshold (h : ι → ℝ) (i : ι) : h i ≤ spectralThreshold h := by
  exact le_trans (Finset.le_sup' h (Finset.mem_univ i)) (le_max_right _ _)

theorem spectralThreshold_endpoint (h : ι → ℝ) :
    spectralThreshold h = 0 ∨ ∃ k, h k = spectralThreshold h := by
  unfold spectralThreshold
  by_cases hs : Finset.univ.sup' Finset.univ_nonempty h ≤ 0
  · exact Or.inl (max_eq_left hs)
  · right
    obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty h
    exact ⟨k, by rw [max_eq_right (le_of_not_ge hs), heq]⟩

/-- Unconditional exact solution of every nonempty finite diagonal quadratic.
All degenerate, zero, and repeated-eigenvalue cases are included. -/
theorem exact_diagonal_solution [DecidableEq ι] (τ : ℝ) (h g : ι → ℝ) :
    ∃ μ, spectralThreshold h ≤ μ ∧
      ((μ = spectralThreshold h ∧
          (∀ i, h i = spectralThreshold h → g i = 0) ∧
          secular h g (spectralThreshold h) ≤ 1) ∨
        (spectralThreshold h < μ ∧ secular h g μ = 1)) ∧
      IsGreatest {v : ℝ | ∃ x : ι → ℝ, radiusSq x ≤ 1 ∧ diagObjective τ h g x = v}
        (secularValue τ h g μ) :=
  exact_value_exists τ h g (spectralThreshold h) (spectralThreshold_nonneg h)
    (le_spectralThreshold h) (spectralThreshold_endpoint h)

end Threshold
end FilteredF3
