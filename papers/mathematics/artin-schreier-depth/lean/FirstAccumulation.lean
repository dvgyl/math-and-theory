import HahnSupport

/-!
# The first finite accumulation cut of actual Hahn support

A Hahn series that is not left-finite has a first real cutoff with infinite
strict lower support. The proof uses an infimum of actual infinite-prefix
bounds and the well ordering of Hahn support to exclude accumulation from the
right. A real support-closure invariant in the image of a rational subgroup
then proves that this cutoff is rational and belongs to that subgroup.
-/

noncomputable section
open Set HahnSeries
namespace NTCThird
variable {k : Type*} [Field k]

/-- The actual rational exponents below a real bound. -/
def realPrefix (f : HahnSeries ℚ k) (r : ℝ) : Set ℚ :=
  {q | q ∈ f.support ∧ (q : ℝ) < r}

@[simp] theorem realPrefix_rat (f : HahnSeries ℚ k) (r : ℚ) :
    realPrefix f (r : ℝ) = f.support ∩ Iio r := by
  ext q
  simp [realPrefix, Rat.cast_lt]

/-- Well-ordered rational Hahn support has a gap immediately to the right of
any real point. The real point itself may be irrational or absent from support. -/
theorem exists_right_gap_of_hahn_support (f : HahnSeries ℚ k) (δ : ℝ) :
    ∃ ε : ℝ, δ < ε ∧ ∀ q ∈ f.support, δ < (q : ℝ) → ε ≤ (q : ℝ) := by
  classical
  let S : Set ℚ := {q | q ∈ f.support ∧ δ < (q : ℝ)}
  by_cases hS : S.Nonempty
  · have hWF : S.IsWF := f.isWF_support.mono (fun q hq => hq.1)
    let q₀ : ℚ := hWF.min hS
    have hq₀ : q₀ ∈ S := hWF.min_mem hS
    refine ⟨(q₀ : ℝ), hq₀.2, ?_⟩
    intro q hq hδq
    have hmin : q₀ ≤ q := hWF.min_le hS ⟨hq, hδq⟩
    exact_mod_cast hmin
  · refine ⟨δ+1, by linarith, ?_⟩
    intro q hq hδq
    exact False.elim (hS ⟨q, hq, hδq⟩)

/-- Infinitely many exponents below δ, and finite prefixes below every smaller
bound, force δ into the real closure of the actual support. -/
theorem mem_closure_of_first_real_cut (f : HahnSeries ℚ k) (δ : ℝ)
    (hinf : (realPrefix f δ).Infinite)
    (hfinite : ∀ r < δ, (realPrefix f r).Finite) :
    δ ∈ closure (realSupport f) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨r, hlow, hrδ⟩ := exists_between (show δ-ε < δ by linarith)
  obtain ⟨q, hq, hqnot⟩ := hinf.exists_not_mem_finite (hfinite r hrδ)
  have hrq : r ≤ (q : ℝ) := le_of_not_gt (fun h => hqnot ⟨hq.1, h⟩)
  refine ⟨(q : ℝ), ⟨q, hq.1, rfl⟩, ?_⟩
  rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hq.2)]
  linarith

/-- Existence of the actual first real accumulation cutoff. No rationality or
algebraicity of that cutoff is assumed. -/
theorem exists_first_real_support_cut (f : HahnSeries ℚ k) (hf : ¬ LeftFinite f) :
    ∃ δ : ℝ, (realPrefix f δ).Infinite ∧
      (∀ r < δ, (realPrefix f r).Finite) ∧ δ ∈ closure (realSupport f) := by
  classical
  let A : Set ℝ := {r | (realPrefix f r).Infinite}
  have hAne : A.Nonempty := by
    obtain ⟨B, hB⟩ := not_forall.mp
      (show ¬ ∀ B : ℚ, (f.support ∩ Iio B).Finite from hf)
    refine ⟨(B : ℝ), ?_⟩
    change (realPrefix f (B : ℝ)).Infinite
    simpa only [realPrefix_rat] using hB
  have hAbdd : BddBelow A := by
    refine ⟨(f.order : ℝ), ?_⟩
    intro r hr
    change (realPrefix f r).Infinite at hr
    apply le_of_not_gt
    intro hrlt
    apply hr
    apply Set.finite_empty.subset
    rintro q ⟨hq, hqr⟩
    have horder : (f.order : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast HahnSeries.order_le_of_coeff_ne_zero hq
    exact False.elim (by linarith)
  let δ : ℝ := sInf A
  have hfinite : ∀ r < δ, (realPrefix f r).Finite := by
    intro r hr
    by_contra hnot
    have hrA : r ∈ A := hnot
    exact (not_le_of_gt hr) (csInf_le hAbdd hrA)
  have hupper : ∀ r > δ, (realPrefix f r).Infinite := by
    intro r hr
    obtain ⟨a, ha, har⟩ := exists_lt_of_csInf_lt hAne hr
    change (realPrefix f a).Infinite at ha
    apply ha.mono
    rintro q ⟨hq, hqa⟩
    exact ⟨hq, lt_trans hqa har⟩
  have hinf : (realPrefix f δ).Infinite := by
    intro hδfinite
    obtain ⟨ε, hδε, hgap⟩ := exists_right_gap_of_hahn_support f δ
    have hboundary : {q : ℚ | (q : ℝ) = δ}.Finite :=
      (Set.finite_singleton δ).preimage
        (show Function.Injective (fun q : ℚ => (q : ℝ)) from Rat.cast_injective).injOn
    apply hupper ε hδε
    apply (hδfinite.union hboundary).subset
    rintro q ⟨hq, hqε⟩
    by_cases hqδ : (q : ℝ) < δ
    · exact Or.inl ⟨hq, hqδ⟩
    · apply Or.inr
      change (q : ℝ) = δ
      apply le_antisymm
      · by_contra hn
        have hδq : δ < (q : ℝ) := lt_of_not_ge hn
        exact (not_lt_of_ge (hgap q hq hδq)) hqε
      · exact le_of_not_gt hqδ
  exact ⟨δ, hinf, hfinite, mem_closure_of_first_real_cut f δ hinf hfinite⟩

/-- The real image of a rational additive subgroup. -/
def rationalSubgroupReal (Γ : AddSubgroup ℚ) : AddSubgroup ℝ :=
  Γ.map (Rat.castHom ℝ).toAddMonoidHom

/-- The first real cutoff is rational and belongs to Γ when all real support
closure points lie in the real image of Γ. This is the actual first-block
existence statement needed by the Ore extraction. -/
theorem exists_first_rational_support_cut (Γ : AddSubgroup ℚ)
    (f : HahnSeries ℚ k) (hf : ¬ LeftFinite f)
    (hΓ : SupportClosureIn (rationalSubgroupReal Γ) f) :
    ∃ δ : ℚ, δ ∈ Γ ∧ (f.support ∩ Iio δ).Infinite ∧
      ∀ r < δ, (f.support ∩ Iio r).Finite := by
  obtain ⟨δ, hinf, hfinite, hclosure⟩ := exists_first_real_support_cut f hf
  have hmem := hΓ hclosure
  obtain ⟨q, hqΓ, hqδ⟩ := AddSubgroup.mem_map.mp hmem
  change (q : ℝ) = δ at hqδ
  subst δ
  refine ⟨q, hqΓ, ?_, ?_⟩
  · simpa only [realPrefix_rat] using hinf
  · intro r hr
    have h := hfinite (r : ℝ) (by exact_mod_cast hr)
    simpa only [realPrefix_rat] using h


/-- Real support closure inside the image of Γ implies literal rational
support containment in Γ. Rational injectivity is used explicitly. -/
theorem support_subset_of_supportClosureIn_rational (Γ : AddSubgroup ℚ)
    (f : HahnSeries ℚ k) (hΓ : SupportClosureIn (rationalSubgroupReal Γ) f) :
    f.support ⊆ (Γ : Set ℚ) := by
  intro q hq
  have hreal : (q : ℝ) ∈ rationalSubgroupReal Γ :=
    hΓ (subset_closure ⟨q, hq, rfl⟩)
  obtain ⟨r, hr, hrq⟩ := AddSubgroup.mem_map.mp hreal
  have hrq' : r = q := Rat.cast_injective hrq
  simpa only [hrq'] using hr

/-- The base-field support hypothesis enters the real invariant through
left-finiteness, which makes the actual real support closed. -/
theorem supportClosureIn_rational_of_leftFinite (Γ : AddSubgroup ℚ)
    (f : HahnSeries ℚ k) (hf : LeftFinite f) (hΓ : f.support ⊆ (Γ : Set ℚ)) :
    SupportClosureIn (rationalSubgroupReal Γ) f := by
  apply supportClosureIn_of_leftFinite (rationalSubgroupReal Γ) f hf
  rintro x ⟨q, hq, rfl⟩
  exact AddSubgroup.mem_map.mpr ⟨q, hΓ hq, rfl⟩

/-- Rational p-divisibility transfers to the real image subgroup used in the
AS root and tower support-closure theorem. -/
theorem rationalSubgroupReal_div (Γ : AddSubgroup ℚ) (p : ℕ)
    (hdiv : ∀ q : ℚ, q ∈ Γ → q / (p : ℚ) ∈ Γ) :
    ∀ x : ℝ, x ∈ rationalSubgroupReal Γ → x / (p : ℝ) ∈ rationalSubgroupReal Γ := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := AddSubgroup.mem_map.mp hx
  refine AddSubgroup.mem_map.mpr ⟨q / (p : ℚ), hdiv q hq, ?_⟩
  change ((q / (p : ℚ) : ℚ) : ℝ) = (q : ℝ) / (p : ℝ)
  simp only [Rat.cast_div, Rat.cast_natCast]

end NTCThird
