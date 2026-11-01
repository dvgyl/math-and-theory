import AllCapGapStability

/-! End-to-end all-cap stability for the actual signed-sum minimum. -/
noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.ActualGlobalGapStability
open Breakthrough.GapFibers Breakthrough.GapCore Breakthrough.ExactSupportGap
open Breakthrough.GlobalGapRigidity Breakthrough.GapPhaseStability
open Breakthrough.GapFlatStability Breakthrough.AllCapGapStability

set_option maxHeartbeats 5000000

/-- The two concrete phase shapes, together with the gap obstruction for
selecting that phase. -/
def PhaseShape {N : ℕ} (v : Fin N → ℝ) (n : ℕ) (x a : ℝ) : Prop :=
  (IsSaturatedAt v n a ∧ x ≤ a-Real.sqrt (1-(n : ℝ)*a^2)) ∨
  (IsFlatAt v (n+2) (1/Real.sqrt ((n : ℝ)+2)) ∧ x ≤ 1/Real.sqrt ((n : ℝ)+2))

lemma phase_shape_optimal_of_separation {N n : ℕ} (v : Fin N → ℝ)
    (hn : Odd n) {x a : ℝ} (ha : 0 < a) (hna : (n : ℝ)*a^2 ≤ 1)
    (hc : ∀ i, 0 ≤ v i) (hcap : ∀ i, v i ≤ a)
    (hv : ∑ i, (v i)^2 = 1) (hphase : PhaseShape v n x a)
    (hsep : (1/Real.sqrt ((n : ℝ)+2) = a-Real.sqrt (1-(n : ℝ)*a^2)) ∨
      capGapFormula n a-x < |1/Real.sqrt ((n : ℝ)+2)-(a-Real.sqrt (1-(n : ℝ)*a^2))|) :
    supportGap v = capGapFormula n a := by
  apply (supportGap_equality_iff_nonnegative v hn ha hna hc hcap hv).mpr
  rcases hphase with ⟨hs, hx⟩ | ⟨hf, hx⟩
  · right
    refine ⟨?_, hs⟩
    rcases hsep with he | he
    · exact he.le
    · by_contra h
      have hlt := lt_of_not_ge h
      rw [abs_of_pos (sub_pos.mpr hlt), capGapFormula, max_eq_left hlt.le] at he
      linarith only [he, hx]
  · left
    refine ⟨?_, hf⟩
    rcases hsep with he | he
    · exact he.ge
    · by_contra h
      have hlt := lt_of_not_ge h
      rw [abs_of_neg (sub_neg.mpr hlt), capGapFormula, max_eq_right hlt.le] at he
      linarith only [he, hx]

/-- Actual finite normalized input, derived core, constructed normalized
comparison, and sharp global distance. A tail coordinate is only needed to
place the saturated residual; the final signed theorem supplies it by zero
padding. -/
theorem actual_nonnegative_phase_stability {N n : ℕ} (coeff : Fin N → ℝ)
    (hn : Odd n) {x a : ℝ} (ha : 0 < a) (hna : (n : ℝ)*a^2 ≤ 1)
    (hn2a : 1 ≤ ((n : ℝ)+2)*a^2)
    (hhalf : a < 2*x) (hnext : 1/Real.sqrt ((n : ℝ)+4) < x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1)
    (hg : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (htail : (gapTail coeff x).Nonempty) :
    ∃ v : Fin N → ℝ,
      (∀ i, 0 ≤ v i) ∧ (∀ i, v i ≤ a) ∧ (∑ i, (v i)^2 = 1) ∧
      PhaseShape v n x a ∧
      (∑ i, (coeff i-v i)^2) ≤ (2+Real.sqrt 2)*(capGapFormula n a-x)^2 ∧
      (((1/Real.sqrt ((n : ℝ)+2) = a-Real.sqrt (1-(n : ℝ)*a^2)) ∨
        capGapFormula n a-x < |1/Real.sqrt ((n : ℝ)+2)-(a-Real.sqrt (1-(n : ℝ)*a^2))|) →
        supportGap v = capGapFormula n a) := by
  classical
  have hx : 0 < x := by linarith only [ha, hhalf]
  have hcount := actual_core_two_phases coeff hn ha hna hhalf hnext hc hcap hv hg
  have hcoef : 0 ≤ 2+Real.sqrt (2 : ℝ) := by positivity
  have hG : x ≤ capGapFormula n a :=
    signed_gap_le_formula_nonnegative coeff hn ha hna hc hcap hv hg
  rcases hcount with hk | hk
  · let r := Real.sqrt (1-(n : ℝ)*a^2)
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (gapTail coeff x) coeff htail
    let v := saturatedComparison coeff x a r j
    have hka : ((gapCore coeff x).card : ℝ)*a^2 ≤ 1 := by simpa only [hk] using hna
    have hstab := actual_saturated_stability coeff hx ha hhalf hc hcap hv hg hka hj hmax
    simp only [hk] at hstab
    change 0 ≤ a-r-x ∧ (∑ i, (coeff i-v i)^2) ≤ (2+Real.sqrt 2)*(a-r-x)^2 at hstab
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hra : r ≤ a := by linarith only [hstab.1, hx]
    have hv0 : ∀ i, 0 ≤ v i := by
      intro i
      dsimp [v, saturatedComparison]
      split_ifs <;> positivity
    have hvA : ∀ i, v i ≤ a := by
      intro i
      dsimp [v, saturatedComparison]
      split_ifs <;> first | exact le_rfl | exact hra | exact ha.le
    have hvnorm : ∑ i, (v i)^2 = 1 := by
      apply saturatedComparison_normalized coeff x a r hj
      rw [hk]
      exact Real.sq_sqrt (by linarith only [hna])
    have hvshape : IsSaturatedAt v n a := by
      simpa only [hk] using saturatedComparison_shape coeff x a r j
    have hphase : PhaseShape v n x a := Or.inl ⟨hvshape, by linarith only [hstab.1]⟩
    have hbranch : a-r ≤ capGapFormula n a := le_max_right _ _
    have hsq : (a-r-x)^2 ≤ (capGapFormula n a-x)^2 :=
      (sq_le_sq₀ hstab.1 (sub_nonneg.mpr hG)).mpr (by linarith only [hbranch])
    refine ⟨v, hv0, hvA, hvnorm, hphase, hstab.2.trans (mul_le_mul_of_nonneg_left hsq hcoef), ?_⟩
    exact phase_shape_optimal_of_separation v hn ha hna hv0 hvA hvnorm hphase
  · let v := flatComparison coeff x
    have hnpos : 0 < n := by have hm := Nat.odd_iff.mp hn; omega
    have hk3 : 3 ≤ (gapCore coeff x).card := by omega
    have hstab := actual_flat_squared_stability coeff hx ha.le hhalf hc hcap hv hg hk3
    have hcast : ((gapCore coeff x).card : ℝ) = (n : ℝ)+2 := by
      rw [hk]
      norm_cast
    rw [hcast] at hstab
    have hflatcap : 1/Real.sqrt ((gapCore coeff x).card : ℝ) ≤ a :=
      flat_coefficient_le_cap (by omega) ha.le (by simpa only [hcast] using hn2a)
    have hv0 : ∀ i, 0 ≤ v i := by
      intro i
      dsimp [v, flatComparison]
      split_ifs <;> positivity
    have hvA : ∀ i, v i ≤ a := by
      intro i
      dsimp [v, flatComparison]
      split_ifs <;> first | exact hflatcap | exact ha.le
    have hvnorm : ∑ i, (v i)^2 = 1 := flatComparison_normalized coeff x (by omega)
    have hvshape : IsFlatAt v (n+2) (1/Real.sqrt ((n : ℝ)+2)) := by
      have h := flatComparison_shape coeff x
      rw [hcast, hk] at h
      exact h
    have hphase : PhaseShape v n x a := Or.inr ⟨hvshape, by linarith only [hstab.1]⟩
    have hbranch : 1/Real.sqrt ((n : ℝ)+2) ≤ capGapFormula n a := le_max_left _ _
    have hsq : (1/Real.sqrt ((n : ℝ)+2)-x)^2 ≤ (capGapFormula n a-x)^2 :=
      (sq_le_sq₀ hstab.1 (sub_nonneg.mpr hG)).mpr (by linarith only [hbranch])
    refine ⟨v, hv0, hvA, hvnorm, hphase, hstab.2.trans (mul_le_mul_of_nonneg_left hsq hcoef), ?_⟩
    exact phase_shape_optimal_of_separation v hn ha hna hv0 hvA hvnorm hphase

/-- A harmless zero coordinate permits a residual comparison in every
finite dimension, including inputs with no original tail coordinate. -/
def zeroPaddedAbs {N : ℕ} (coeff : Fin N → ℝ) : Fin (N+1) → ℝ :=
  Fin.cons 0 (fun i => |coeff i|)

lemma zeroPaddedAbs_sum {N : ℕ} (coeff : Fin N → ℝ) (ω : BoolCube (N+1)) :
    rademacherSum (zeroPaddedAbs coeff) ω =
      rademacherSum (fun i => |coeff i|) (fun i => ω i.succ) := by
  simp [rademacherSum, zeroPaddedAbs, Fin.sum_univ_succ]

lemma zeroPaddedAbs_supportGap {N : ℕ} (coeff : Fin N → ℝ) :
    supportGap (zeroPaddedAbs coeff) = supportGap coeff := by
  have hg : ∀ ω : BoolCube N,
      supportGap coeff ≤ |rademacherSum (fun i => |coeff i|) ω| := by
    apply (le_supportGap_iff (fun i => |coeff i|) (supportGap coeff)).mp
    rw [supportGap_abs]
  apply supportGap_eq_of_gap_and_outcome
  · intro ω
    rw [zeroPaddedAbs_sum]
    exact hg _
  · obtain ⟨ω, hω, _⟩ := supportGap_attained (fun i => |coeff i|)
    refine ⟨Fin.cons true ω, ?_⟩
    rw [zeroPaddedAbs_sum]
    simpa only [Fin.cons_succ, supportGap_abs] using hω.symm

/-- All coefficient signs and dimensions: the actual signed-sum minimum
selects a normalized comparison in one of the two surviving phases. The
sharp constant is independent of the cap and the dimension. -/
theorem signed_supportGap_phase_stability {N n : ℕ} (coeff : Fin N → ℝ)
    (hn : Odd n) {a : ℝ} (ha : 0 < a) (hna : (n : ℝ)*a^2 ≤ 1)
    (hn2a : 1 ≤ ((n : ℝ)+2)*a^2)
    (hcap : ∀ i, |coeff i| ≤ a) (hv : ∑ i, (coeff i)^2 = 1)
    (htrigger : max (a/2) (1/Real.sqrt ((n : ℝ)+4)) < supportGap coeff) :
    ∃ v : Fin (N+1) → ℝ,
      (∀ i, 0 ≤ v i) ∧ (∀ i, v i ≤ a) ∧ (∑ i, (v i)^2 = 1) ∧
      PhaseShape v n (supportGap coeff) a ∧
      Real.sqrt (∑ i, (zeroPaddedAbs coeff i-v i)^2) ≤
        Real.sqrt (2+Real.sqrt 2)*(capGapFormula n a-supportGap coeff) ∧
      (((1/Real.sqrt ((n : ℝ)+2) = a-Real.sqrt (1-(n : ℝ)*a^2)) ∨
        capGapFormula n a-supportGap coeff <
          |1/Real.sqrt ((n : ℝ)+2)-(a-Real.sqrt (1-(n : ℝ)*a^2))|) →
        supportGap v = capGapFormula n a) := by
  classical
  let x := supportGap coeff
  have hhalf : a < 2*x := by
    have h := (le_max_left (a/2) (1/Real.sqrt ((n : ℝ)+4))).trans_lt htrigger
    linarith only [h]
  have hnext : 1/Real.sqrt ((n : ℝ)+4) < x :=
    (le_max_right _ _).trans_lt htrigger
  have hx : 0 < x := by linarith only [ha, hhalf]
  have hc' : ∀ i, 0 ≤ zeroPaddedAbs coeff i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [zeroPaddedAbs]
    · simpa [zeroPaddedAbs] using abs_nonneg (coeff j)
  have hcap' : ∀ i, zeroPaddedAbs coeff i ≤ a := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [zeroPaddedAbs] using ha.le
    · simpa [zeroPaddedAbs] using hcap j
  have hv' : ∑ i, (zeroPaddedAbs coeff i)^2 = 1 := by
    simpa [zeroPaddedAbs, Fin.sum_univ_succ, sq_abs] using hv
  have hg' : ∀ ω : BoolCube (N+1), x ≤ |rademacherSum (zeroPaddedAbs coeff) ω| := by
    apply (le_supportGap_iff (zeroPaddedAbs coeff) x).mp
    rw [zeroPaddedAbs_supportGap]
  have htail : (gapTail (zeroPaddedAbs coeff) x).Nonempty := by
    refine ⟨0, ?_⟩
    simp [gapTail, gapCore, zeroPaddedAbs, not_le.mpr hx]
  obtain ⟨v, hv0, hvA, hvnorm, hvphase, hd, hopt⟩ :=
    actual_nonnegative_phase_stability (zeroPaddedAbs coeff) hn ha hna hn2a
      hhalf hnext hc' hcap' hv' hg' htail
  refine ⟨v, hv0, hvA, hvnorm, hvphase, ?_, hopt⟩
  have hG : x ≤ capGapFormula n a := supportGap_le_formula coeff hn ha hna hcap hv
  calc
    Real.sqrt (∑ i, (zeroPaddedAbs coeff i-v i)^2) ≤
        Real.sqrt ((2+Real.sqrt 2)*(capGapFormula n a-x)^2) := Real.sqrt_le_sqrt hd
    _ = Real.sqrt (2+Real.sqrt 2)*(capGapFormula n a-x) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2+Real.sqrt (2 : ℝ)),
        Real.sqrt_sq (sub_nonneg.mpr hG)]

/-- No supplied odd phase index is required: every cap in `(0,1]` has the
canonical band derived by `oddBandIndex`. -/
theorem all_caps_supportGap_stability {N : ℕ} (coeff : Fin N → ℝ) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hcap : ∀ i, |coeff i| ≤ a) (hv : ∑ i, (coeff i)^2 = 1)
    (htrigger : max (a/2) (1/Real.sqrt ((oddBandIndex a : ℝ)+4)) < supportGap coeff) :
    ∃ v : Fin (N+1) → ℝ,
      (∀ i, 0 ≤ v i) ∧ (∀ i, v i ≤ a) ∧ (∑ i, (v i)^2 = 1) ∧
      PhaseShape v (oddBandIndex a) (supportGap coeff) a ∧
      Real.sqrt (∑ i, (zeroPaddedAbs coeff i-v i)^2) ≤
        Real.sqrt (2+Real.sqrt 2)*(capGapFormula (oddBandIndex a) a-supportGap coeff) ∧
      (((1/Real.sqrt ((oddBandIndex a : ℝ)+2) =
          a-Real.sqrt (1-(oddBandIndex a : ℝ)*a^2)) ∨
        capGapFormula (oddBandIndex a) a-supportGap coeff <
          |1/Real.sqrt ((oddBandIndex a : ℝ)+2)-
            (a-Real.sqrt (1-(oddBandIndex a : ℝ)*a^2))|) →
        supportGap v = capGapFormula (oddBandIndex a) a) := by
  obtain ⟨hn, hna, hn2a⟩ := oddBandIndex_spec ha ha1
  exact signed_supportGap_phase_stability coeff hn ha hna hn2a hcap hv htrigger

#print axioms phase_shape_optimal_of_separation
#print axioms actual_nonnegative_phase_stability
#print axioms zeroPaddedAbs_supportGap
#print axioms signed_supportGap_phase_stability
#print axioms all_caps_supportGap_stability

end Breakthrough.ActualGlobalGapStability
