import ExactSaturatedModulus

/-! Arbitrary signed input and its actual support gap in the exact
nonlinear saturated stability theorem. -/
noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.ActualSaturatedModulus
open Breakthrough.GapFibers Breakthrough.GapCore Breakthrough.ExactSupportGap
open Breakthrough.GlobalGapRigidity Breakthrough.GapPhaseStability
open Breakthrough.AllCapGapStability Breakthrough.ActualGlobalGapStability
open Breakthrough.SharpTail Breakthrough.ExactSaturatedModulus

set_option maxHeartbeats 5000000

lemma zeroPaddedAbs_core_card {N : ℕ} (coeff : Fin N → ℝ) {x : ℝ} (hx : 0 < x) :
    (gapCore (zeroPaddedAbs coeff) x).card = (gapCore (fun i => |coeff i|) x).card := by
  classical
  have he : gapCore (zeroPaddedAbs coeff) x =
      (gapCore (fun i => |coeff i|) x).map (Fin.succEmb N) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [gapCore, zeroPaddedAbs, not_le.mpr hx, Finset.mem_map]
    · simp [gapCore, zeroPaddedAbs, Finset.mem_map]
  rw [he, Finset.card_map]

/-- Exact local nonlinear coefficient stability for arbitrary signed
finite input. All structural data use the actual gap and actual core;
no abstract core, tail variance, or signed law is supplied. -/
theorem signed_supportGap_saturated_modulus {N : ℕ} (coeff : Fin N → ℝ) {a : ℝ}
    (ha : 0 < a) (hcap : ∀ i, |coeff i| ≤ a)
    (hv : ∑ i, (coeff i)^2 = 1) (hhalf : a < 2*supportGap coeff)
    (hka : ((gapCore (fun i => |coeff i|) (supportGap coeff)).card : ℝ)*a^2 < 1)
    (hlocal : a-Real.sqrt (1-((gapCore (fun i => |coeff i|) (supportGap coeff)).card : ℝ)*a^2)-
        supportGap coeff ≤ (Real.sqrt 2-1)*
          Real.sqrt (1-((gapCore (fun i => |coeff i|) (supportGap coeff)).card : ℝ)*a^2)) :
    let k := (gapCore (fun i => |coeff i|) (supportGap coeff)).card
    let r := Real.sqrt (1-(k : ℝ)*a^2)
    let e := a-r-supportGap coeff
    Odd k ∧ 0 < k ∧ 0 < r ∧ r < a/2 ∧ 0 ≤ e ∧
      ∃ v : Fin (N+1) → ℝ,
        (∀ i, 0 ≤ v i) ∧ (∀ i, v i ≤ a) ∧ (∑ i, (v i)^2 = 1) ∧
        IsSaturatedAt v k a ∧
        Real.sqrt (∑ i, (zeroPaddedAbs coeff i-v i)^2) ≤ gapModulus r e := by
  classical
  let x := supportGap coeff
  let k := (gapCore (fun i => |coeff i|) x).card
  let r := Real.sqrt (1-(k : ℝ)*a^2)
  let e := a-r-x
  have hx : 0 < x := by linarith only [ha, hhalf]
  have hk : (gapCore (zeroPaddedAbs coeff) x).card = k := zeroPaddedAbs_core_card coeff hx
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
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (gapTail (zeroPaddedAbs coeff) x)
    (zeroPaddedAbs coeff) htail
  have hka' : ((gapCore (zeroPaddedAbs coeff) x).card : ℝ)*a^2 < 1 := by
    rw [hk]
    exact hka
  have hlocal' : a-Real.sqrt (1-((gapCore (zeroPaddedAbs coeff) x).card : ℝ)*a^2)-x ≤
      (Real.sqrt 2-1)*Real.sqrt (1-((gapCore (zeroPaddedAbs coeff) x).card : ℝ)*a^2) := by
    rw [hk]
    exact hlocal
  have hbound := actual_saturated_modulus (zeroPaddedAbs coeff) hx ha hhalf hc'
    hcap' hv' hg' hka' hlocal' hj hmax
  simp only [hk] at hbound
  let v := saturatedComparison (zeroPaddedAbs coeff) x a r j
  change 0 ≤ e ∧ Real.sqrt (∑ i, (zeroPaddedAbs coeff i-v i)^2) ≤ gapModulus r e at hbound
  have hs := actual_core_spread_bound (zeroPaddedAbs coeff) hx ha.le hhalf hc' hcap' hv' hg'
  have hodd : Odd k := by simpa only [hk] using hs.1
  have hkpos : 0 < k := by simpa only [hk] using hs.2.1
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by linarith only [hka])
  have hrhalf : r < a/2 := by
    have he : 0 ≤ a-r-x := hbound.1
    linarith only [he, hhalf]
  have hv0 : ∀ i, 0 ≤ v i := by
    intro i
    dsimp [v, saturatedComparison]
    split_ifs <;> positivity
  have hvA : ∀ i, v i ≤ a := by
    intro i
    dsimp [v, saturatedComparison]
    split_ifs <;> first | exact le_rfl | linarith only [hrhalf, ha]
  have hvnorm : ∑ i, (v i)^2 = 1 := by
    apply saturatedComparison_normalized (zeroPaddedAbs coeff) x a r hj
    rw [hk]
    exact Real.sq_sqrt (by linarith only [hka])
  have hvshape : IsSaturatedAt v k a := by
    simpa only [hk] using saturatedComparison_shape (zeroPaddedAbs coeff) x a r j
  exact ⟨hodd, hkpos, hrpos, hrhalf, hbound.1, v, hv0, hvA, hvnorm, hvshape, hbound.2⟩

/-- Above the competing flat value, the exact local modulus measures
distance to a genuine global cap optimizer. The core size is derived from
the actual minimum and is not an input assumption. -/
theorem signed_global_saturated_modulus {N n : ℕ} (coeff : Fin N → ℝ)
    (hn : Odd n) {a : ℝ} (ha : 0 < a) (hna : (n : ℝ)*a^2 < 1)
    (hcap : ∀ i, |coeff i| ≤ a) (hv : ∑ i, (coeff i)^2 = 1)
    (habove : 1/Real.sqrt ((n : ℝ)+2) < supportGap coeff)
    (hlocal : a-Real.sqrt (1-(n : ℝ)*a^2)-supportGap coeff ≤
      (Real.sqrt 2-1)*Real.sqrt (1-(n : ℝ)*a^2)) :
    (gapCore (fun i => |coeff i|) (supportGap coeff)).card = n ∧
      ∃ v : Fin (N+1) → ℝ,
        (∀ i, 0 ≤ v i) ∧ (∀ i, v i ≤ a) ∧ (∑ i, (v i)^2 = 1) ∧
        IsSaturatedAt v n a ∧ supportGap v = capGapFormula n a ∧
        Real.sqrt (∑ i, (zeroPaddedAbs coeff i-v i)^2) ≤
          gapModulus (Real.sqrt (1-(n : ℝ)*a^2))
            (capGapFormula n a-supportGap coeff) := by
  have hhalf := cap_lt_twice_of_above_step hn ha.le hna.le habove
  have hx : 0 < supportGap coeff := by linarith only [ha, hhalf]
  have hnext : 1/Real.sqrt ((n : ℝ)+4) < supportGap coeff := by
    apply lt_trans ?_ habove
    apply one_div_lt_one_div_of_lt (by positivity)
    exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hv' : ∑ i, |coeff i|^2 = 1 := by simpa only [sq_abs] using hv
  have hg : ∀ ω : BoolCube N,
      supportGap coeff ≤ |rademacherSum (fun i => |coeff i|) ω| := by
    apply (le_supportGap_iff (fun i => |coeff i|) (supportGap coeff)).mp
    rw [supportGap_abs]
  have hcount := actual_core_two_phases (fun i => |coeff i|) hn ha hna.le
    hhalf hnext (fun i => abs_nonneg _) hcap hv' hg
  have hd := actual_core_variance_data (fun i => |coeff i|) hx.le ha.le
    (fun i => abs_nonneg _) hcap hv'
  have hs := actual_core_spread_bound (fun i => |coeff i|) hx ha.le hhalf
    (fun i => abs_nonneg _) hcap hv' hg
  have hupper := odd_core_count_le hs.1 hn habove hd.2.2.2.2.1
  have hk : (gapCore (fun i => |coeff i|) (supportGap coeff)).card = n := by
    rcases hcount with h | h
    · exact h
    · omega
  have hka : ((gapCore (fun i => |coeff i|) (supportGap coeff)).card : ℝ)*a^2 < 1 := by
    rw [hk]
    exact hna
  have hlocal' : a-Real.sqrt (1-((gapCore (fun i => |coeff i|) (supportGap coeff)).card : ℝ)*a^2)-
      supportGap coeff ≤ (Real.sqrt 2-1)*
        Real.sqrt (1-((gapCore (fun i => |coeff i|) (supportGap coeff)).card : ℝ)*a^2) := by
    rw [hk]
    exact hlocal
  have h := signed_supportGap_saturated_modulus coeff ha hcap hv hhalf hka hlocal'
  simp only [hk] at h
  obtain ⟨_, _, _, _, he, v, hv0, hvA, hvnorm, hvshape, hbound⟩ := h
  have hbranch : 1/Real.sqrt ((n : ℝ)+2) ≤ a-Real.sqrt (1-(n : ℝ)*a^2) := by
    linarith only [habove, he]
  have hG : capGapFormula n a = a-Real.sqrt (1-(n : ℝ)*a^2) := max_eq_right hbranch
  have hopt : supportGap v = capGapFormula n a :=
    (supportGap_equality_iff_nonnegative v hn ha hna.le hv0 hvA hvnorm).mpr
      (Or.inr ⟨hbranch, hvshape⟩)
  refine ⟨hk, v, hv0, hvA, hvnorm, hvshape, hopt, ?_⟩
  rw [hG]
  exact hbound

/-- Canonical-band version: all parameters are determined by the cap and
the actual signed-sum minimum of the input. -/
theorem all_caps_exact_saturated_modulus {N : ℕ} (coeff : Fin N → ℝ) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hinterior : (oddBandIndex a : ℝ)*a^2 < 1)
    (hcap : ∀ i, |coeff i| ≤ a) (hv : ∑ i, (coeff i)^2 = 1)
    (habove : 1/Real.sqrt ((oddBandIndex a : ℝ)+2) < supportGap coeff)
    (hlocal : a-Real.sqrt (1-(oddBandIndex a : ℝ)*a^2)-supportGap coeff ≤
      (Real.sqrt 2-1)*Real.sqrt (1-(oddBandIndex a : ℝ)*a^2)) :
    (gapCore (fun i => |coeff i|) (supportGap coeff)).card = oddBandIndex a ∧
      ∃ v : Fin (N+1) → ℝ,
        (∀ i, 0 ≤ v i) ∧ (∀ i, v i ≤ a) ∧ (∑ i, (v i)^2 = 1) ∧
        IsSaturatedAt v (oddBandIndex a) a ∧ supportGap v = capGapFormula (oddBandIndex a) a ∧
        Real.sqrt (∑ i, (zeroPaddedAbs coeff i-v i)^2) ≤
          gapModulus (Real.sqrt (1-(oddBandIndex a : ℝ)*a^2))
            (capGapFormula (oddBandIndex a) a-supportGap coeff) := by
  exact signed_global_saturated_modulus coeff (oddBandIndex_spec ha ha1).1 ha hinterior
    hcap hv habove hlocal

#print axioms zeroPaddedAbs_core_card
#print axioms signed_supportGap_saturated_modulus
#print axioms signed_global_saturated_modulus
#print axioms all_caps_exact_saturated_modulus
end Breakthrough.ActualSaturatedModulus
