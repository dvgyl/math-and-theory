import SecularExistence

/-! Eliminating the secular search by a largest-real-root expression.
For three coordinates, the polynomial is the degree-six expression in the report.
No root, optimizer, or certificate existence is assumed in `closed_form_diagonal`.
-/

noncomputable section
open scoped BigOperators
namespace FilteredF3
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The polynomial obtained by clearing the squared secular denominators. -/
def secularPolynomial (h g : ι → ℝ) (z : ℝ) : ℝ :=
  (∏ i, (z - h i) ^ 2) -
    ∑ i, (g i) ^ 2 * ∏ j ∈ Finset.univ.erase i, (z - h j) ^ 2

theorem secularPolynomial_factor (h g : ι → ℝ) (z : ℝ)
    (hne : ∀ i, z - h i ≠ 0) :
    secularPolynomial h g z = (∏ i, (z - h i) ^ 2) * (1 - secular h g z) := by
  unfold secularPolynomial secular
  rw [mul_sub, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (z - h j) ^ 2) (Finset.mem_univ i)]
  field_simp [hne i]
  ring

theorem secularPolynomial_root_iff (h g : ι → ℝ) (z : ℝ)
    (hz : ∀ i, h i < z) :
    secularPolynomial h g z = 0 ↔ secular h g z = 1 := by
  have hne : ∀ i, z - h i ≠ 0 := fun i => ne_of_gt (sub_pos.mpr (hz i))
  have hp : 0 < ∏ i, (z - h i) ^ 2 :=
    Finset.prod_pos fun i _ => sq_pos_of_pos (sub_pos.mpr (hz i))
  rw [secularPolynomial_factor h g z hne, mul_eq_zero]
  simp only [ne_of_gt hp, false_or, sub_eq_zero, eq_comm (a := (1 : ℝ))]

/-- A compatible singular eigenvalue is a polynomial root, including repeated
eigenvalues and zero coupling components. -/
theorem singular_polynomial_root (h g : ι → ℝ) (z : ℝ) (k : ι)
    (hk : h k = z) (hg : g k = 0) : secularPolynomial h g z = 0 := by
  have hp : (∏ i, (z - h i) ^ 2) = 0 :=
    Finset.prod_eq_zero_iff.mpr ⟨k, Finset.mem_univ k, by simp [hk]⟩
  have hs : (∑ i, (g i) ^ 2 * ∏ j ∈ Finset.univ.erase i, (z - h j) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hik : i = k
    · subst i
      simp [hg]
    · have hk_mem : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ k⟩
      have hp' : (∏ j ∈ Finset.univ.erase i, (z - h j) ^ 2) = 0 :=
        Finset.prod_eq_zero_iff.mpr ⟨k, hk_mem, by simp [hk]⟩
      rw [hp', mul_zero]
  unfold secularPolynomial
  rw [hp, hs, sub_self]

/-- Strict decrease from every compatible endpoint whenever g is nonzero. -/
theorem secular_strict_decrease (h g : ι → ℝ) (a b : ℝ)
    (ha : ∀ i, h i ≤ a) (hc : ∀ i, h i = a → g i = 0)
    (hab : a < b) (hg : ∃ k, g k ≠ 0) :
    secular h g b < secular h g a := by
  have hterm : ∀ i, (g i / (b - h i)) ^ 2 ≤ (g i / (a - h i)) ^ 2 := by
    intro i
    by_cases hgi : g i = 0
    · simp [hgi]
    · have hia : h i < a := lt_of_le_of_ne (ha i) (by intro he; exact hgi (hc i he))
      have hpos : 0 < (a - h i) ^ 2 := sq_pos_of_pos (sub_pos.mpr hia)
      have hs : (a - h i) ^ 2 ≤ (b - h i) ^ 2 :=
        (sq_le_sq₀ (sub_pos.mpr hia).le (by linarith)).mpr (by linarith)
      rw [div_pow, div_pow]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hpos hs
  obtain ⟨k, hk⟩ := hg
  have hka : h k < a := lt_of_le_of_ne (ha k) (by intro he; exact hk (hc k he))
  have hpos : 0 < (a - h k) ^ 2 := sq_pos_of_pos (sub_pos.mpr hka)
  have hs : (a - h k) ^ 2 < (b - h k) ^ 2 :=
    (sq_lt_sq₀ (sub_pos.mpr hka).le (by linarith)).mpr (by linarith)
  have hstrict : (g k / (b - h k)) ^ 2 < (g k / (a - h k)) ^ 2 := by
    rw [div_pow, div_pow]
    exact div_lt_div_of_pos_left (sq_pos_of_ne_zero hk) hpos hs
  exact Finset.sum_lt_sum (fun i _ => hterm i) ⟨k, Finset.mem_univ k, hstrict⟩

/-- Once a compatible point has secular value at most one, the polynomial has
no roots to its right. This includes μ=0 and every hard case. -/
theorem no_roots_above (h g : ι → ℝ) (a : ℝ)
    (ha : ∀ i, h i ≤ a) (hc : ∀ i, h i = a → g i = 0)
    (hs : secular h g a ≤ 1) (b : ℝ) (hab : a < b) :
    secularPolynomial h g b ≠ 0 := by
  have hb : ∀ i, h i < b := fun i => lt_of_le_of_lt (ha i) hab
  change ¬ secularPolynomial h g b = 0
  rw [secularPolynomial_root_iff h g b hb]
  by_cases hg : ∃ k, g k ≠ 0
  · exact ne_of_lt (lt_of_lt_of_le (secular_strict_decrease h g a b ha hc hab hg) hs)
  · push_neg at hg
    simp [secular, hg]

theorem secular_root_unique (h g : ι → ℝ) (a b : ℝ)
    (ha : ∀ i, h i < a) (hb : ∀ i, h i < b)
    (hsa : secular h g a = 1) (hsb : secular h g b = 1) : a = b := by
  have hca : ∀ i, h i = a → g i = 0 := by intro i hi; exact False.elim ((ne_of_lt (ha i)) hi)
  have hcb : ∀ i, h i = b → g i = 0 := by intro i hi; exact False.elim ((ne_of_lt (hb i)) hi)
  apply le_antisymm
  · by_contra hnot
    have hlt : b < a := lt_of_not_ge hnot
    exact no_roots_above h g b (fun i => (hb i).le) hcb hsb.le a hlt
      ((secularPolynomial_root_iff h g a ha).mpr hsa)
  · by_contra hnot
    have hlt : a < b := lt_of_not_ge hnot
    exact no_roots_above h g a (fun i => (ha i).le) hca hsa.le b hlt
      ((secularPolynomial_root_iff h g b hb).mpr hsb)

section Nonempty
variable [Nonempty ι]

/-- The polynomial always has a greatest real root, even though many of its
other roots can be complex. -/
theorem greatest_real_root_exists (h g : ι → ℝ) :
    ∃ ν : ℝ, IsGreatest {z : ℝ | secularPolynomial h g z = 0} ν := by
  let a := Finset.univ.sup' Finset.univ_nonempty h
  have ha : ∀ i, h i ≤ a := fun i => Finset.le_sup' h (Finset.mem_univ i)
  obtain ⟨k, hk, hka⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty h
  have hka' : h k = a := hka.symm
  rcases exhaustive_branches h g a ha with ⟨hc, hs⟩ | ⟨μ, hμ, hs⟩
  · refine ⟨a, singular_polynomial_root h g a k hka' (hc k hka'), ?_⟩
    intro b hb
    by_contra hlt
    exact no_roots_above h g a ha hc hs b (lt_of_not_ge hlt) hb
  · have hstrict : ∀ i, h i < μ := fun i => lt_of_le_of_lt (ha i) hμ
    have hc : ∀ i, h i = μ → g i = 0 := by
      intro i hi
      exact False.elim ((ne_of_lt (hstrict i)) hi)
    refine ⟨μ, (secularPolynomial_root_iff h g μ hstrict).mpr hs, ?_⟩
    intro b hb
    by_contra hlt
    exact no_roots_above h g μ (fun i => (hstrict i).le) hc hs.le b (lt_of_not_ge hlt) hb

/-- Exact root selector, not a filter optimization. -/
def largestRealRoot (h g : ι → ℝ) : ℝ := Classical.choose (greatest_real_root_exists h g)

theorem largestRealRoot_spec (h g : ι → ℝ) :
    IsGreatest {z : ℝ | secularPolynomial h g z = 0} (largestRealRoot h g) :=
  Classical.choose_spec (greatest_real_root_exists h g)

/-- The unique multiplier selected by the branch theorem is max(0,ν), where ν
is the greatest real root of the explicit secular polynomial. -/
theorem branch_multiplier_is_root_formula (h g : ι → ℝ) (μ : ℝ)
    (hbranch :
      (μ = spectralThreshold h ∧ (∀ i, h i = spectralThreshold h → g i = 0) ∧
        secular h g (spectralThreshold h) ≤ 1) ∨
      (spectralThreshold h < μ ∧ secular h g μ = 1)) :
    μ = max 0 (largestRealRoot h g) := by
  have hroot := largestRealRoot_spec h g
  rcases hbranch with ⟨heq, hc, hs⟩ | ⟨hμ, hs⟩
  · subst μ
    have hnobig := no_roots_above h g (spectralThreshold h) (le_spectralThreshold h) hc hs
    have hle : largestRealRoot h g ≤ spectralThreshold h := by
      by_contra hlt
      exact hnobig (largestRealRoot h g) (lt_of_not_ge hlt) hroot.1
    rcases spectralThreshold_endpoint h with hz | ⟨k, hk⟩
    · rw [hz] at hle ⊢
      exact (max_eq_left hle).symm
    · have hr : secularPolynomial h g (spectralThreshold h) = 0 :=
        singular_polynomial_root h g (spectralThreshold h) k hk (hc k hk)
      have heq : spectralThreshold h = largestRealRoot h g := le_antisymm (hroot.2 hr) hle
      rw [← heq, max_eq_right (spectralThreshold_nonneg h)]
  · have hstrict : ∀ i, h i < μ := fun i => lt_of_le_of_lt (le_spectralThreshold h i) hμ
    have hc : ∀ i, h i = μ → g i = 0 := by intro i hi; exact False.elim ((ne_of_lt (hstrict i)) hi)
    have hr := (secularPolynomial_root_iff h g μ hstrict).mpr hs
    have hle : largestRealRoot h g ≤ μ := by
      by_contra hlt
      exact no_roots_above h g μ (fun i => (hstrict i).le) hc hs.le
        (largestRealRoot h g) (lt_of_not_ge hlt) hroot.1
    have heq : μ = largestRealRoot h g := le_antisymm (hroot.2 hr) hle
    rw [← heq, max_eq_right (le_trans (spectralThreshold_nonneg h) hμ.le)]

/-- Complete largest-real-root formula for a finite real diagonal quadratic
on the Euclidean unit ball. This is an unconditional maximum theorem. -/
theorem closed_form_diagonal (τ : ℝ) (h g : ι → ℝ) :
    IsGreatest {v : ℝ | ∃ x : ι → ℝ, radiusSq x ≤ 1 ∧ diagObjective τ h g x = v}
      (secularValue τ h g (max 0 (largestRealRoot h g))) := by
  obtain ⟨μ, _, hb, hm⟩ := exact_diagonal_solution τ h g
  rw [← branch_multiplier_is_root_formula h g μ hb]
  exact hm

end Nonempty
end FilteredF3
