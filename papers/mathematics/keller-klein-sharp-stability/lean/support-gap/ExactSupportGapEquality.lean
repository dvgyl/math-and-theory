import ExactSupportGap
import Mathlib.Algebra.Order.Floor.Semiring

/-!
Complete equality classification for the actual all-dimensional support-gap
optimum. Shapes are stated directly on the original finite coordinates.
-/

noncomputable section
open scoped BigOperators
open KellerKlein

namespace Breakthrough.ExactSupportGap
open Breakthrough.AdversarialCentralGap Breakthrough.GapFibers Breakthrough.GapCore

set_option maxHeartbeats 3000000

def IsFlatAt {N : ℕ} (coeff : Fin N → ℝ) (k : ℕ) (t : ℝ) : Prop :=
  ∃ C : Finset (Fin N), C.card = k ∧ (∀ i ∈ C, coeff i = t) ∧
    ∀ i, i ∉ C → coeff i = 0

def IsSaturatedAt {N : ℕ} (coeff : Fin N → ℝ) (k : ℕ) (a : ℝ) : Prop := by
  classical
  exact ∃ C : Finset (Fin N), C.card = k ∧ (∀ i ∈ C, coeff i = a) ∧
    ((Finset.univ \ C).filter (fun i => coeff i ≠ 0)).card ≤ 1

lemma sum_sq_eq_sq_sum_iff_single {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∑ i ∈ s, c i ^ 2) = (∑ i ∈ s, c i) ^ 2 ↔
      (s.filter (fun i => c i ≠ 0)).card ≤ 1 := by
  classical
  constructor
  · intro heq
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hiS := (Finset.mem_filter.mp hi).1
    have hjS := (Finset.mem_filter.mp hj).1
    have hi0 := (Finset.mem_filter.mp hi).2
    have hj0 := (Finset.mem_filter.mp hj).2
    by_contra hne
    have hci : 0 < c i := lt_of_le_of_ne (hc i hiS) (Ne.symm hi0)
    have hcj : 0 < c j := lt_of_le_of_ne (hc j hjS) (Ne.symm hj0)
    have hjE : j ∈ s.erase i := Finset.mem_erase.mpr ⟨Ne.symm hne, hjS⟩
    have hE : ∀ l ∈ s.erase i, 0 ≤ c l := fun l hl => hc l (Finset.mem_of_mem_erase hl)
    have hjs : c j ≤ ∑ l ∈ s.erase i, c l := Finset.single_le_sum hE hjE
    have hpos : 0 < ∑ l ∈ s.erase i, c l := hcj.trans_le hjs
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg hE
    have hs : (∑ l ∈ s, c l) = c i + ∑ l ∈ s.erase i, c l := by
      exact (Finset.add_sum_erase s c hiS).symm
    have hs2 : (∑ l ∈ s, c l ^ 2) = c i ^ 2 + ∑ l ∈ s.erase i, c l ^ 2 := by
      exact (Finset.add_sum_erase s (fun l => c l ^ 2) hiS).symm
    have hprod : c i * (∑ l ∈ s.erase i, c l) ≤ 0 := by
      rw [hs, hs2] at heq
      nlinarith only [heq, hsq]
    exact (not_le_of_gt (mul_pos hci hpos)) hprod
  · intro hcard
    by_cases hex : ∃ i ∈ s, c i ≠ 0
    · obtain ⟨i, hi, hci⟩ := hex
      have hz : ∀ j ∈ s, j ≠ i → c j = 0 := by
        intro j hj hji
        by_cases hzj : c j = 0
        · exact hzj
        · exact False.elim (hji (Finset.card_le_one.mp hcard j
            (Finset.mem_filter.mpr ⟨hj, hzj⟩) i (Finset.mem_filter.mpr ⟨hi, hci⟩)))
      have hs : (∑ j ∈ s, c j) = c i :=
        Finset.sum_eq_single i (fun j hj hji => hz j hj hji) (by simp [hi])
      have hs2 : (∑ j ∈ s, c j ^ 2) = c i ^ 2 :=
        Finset.sum_eq_single i (fun j hj hji => by rw [hz j hj hji]; norm_num) (by simp [hi])
      rw [hs, hs2]
    · have hz : ∀ i ∈ s, c i = 0 := by
        intro i hi
        by_cases hzi : c i = 0
        · exact hzi
        · exact False.elim (hex ⟨i, hi, hzi⟩)
      simp only [Finset.sum_congr rfl (fun i hi => hz i hi), Finset.sum_const_zero,
        zero_pow (by decide : 2 ≠ 0)]
      have hs2 : (∑ i ∈ s, c i ^ 2) = 0 :=
        Finset.sum_eq_zero (fun i hi => by rw [hz i hi]; norm_num)
      exact hs2

lemma constant_of_square_sum_upper {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {a : ℝ} (ha : 0 ≤ a) (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ a)
    (hs : (∑ i ∈ s, c i ^ 2) = (s.card : ℝ) * a ^ 2) :
    ∀ i ∈ s, c i = a := by
  classical
  have hd : ∀ i ∈ s, 0 ≤ a ^ 2 - c i ^ 2 := by
    intro i hi
    nlinarith [(hc i hi).1, (hc i hi).2]
  have hz : (∑ i ∈ s, (a ^ 2 - c i ^ 2)) = 0 := by
    rw [Finset.sum_sub_distrib, hs]
    simp
  intro i hi
  have he := (Finset.sum_eq_zero_iff_of_nonneg hd).mp hz i hi
  nlinarith [(hc i hi).1]

lemma constant_of_square_sum_lower {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {a : ℝ} (ha : 0 ≤ a) (hc : ∀ i ∈ s, a ≤ c i)
    (hs : (∑ i ∈ s, c i ^ 2) = (s.card : ℝ) * a ^ 2) :
    ∀ i ∈ s, c i = a := by
  classical
  have hd : ∀ i ∈ s, 0 ≤ c i ^ 2 - a ^ 2 := by
    intro i hi
    nlinarith [hc i hi]
  have hz : (∑ i ∈ s, (c i ^ 2 - a ^ 2)) = 0 := by
    rw [Finset.sum_sub_distrib, hs]
    simp
  intro i hi
  have he := (Finset.sum_eq_zero_iff_of_nonneg hd).mp hz i hi
  nlinarith [hc i hi]

lemma odd_flat_core_gap {N : ℕ} (C : Finset (Fin N)) (coeff : Fin N → ℝ)
    {a : ℝ} (ha : 0 < a) (hodd : Odd C.card) (hc : ∀ i ∈ C, coeff i = a) :
    ∀ ω : BoolCube N, a ≤ |∑ i ∈ C, coeff i * rademacherSign (ω i)| := by
  classical
  have hcount : nonzeroCount C coeff = C.card := by
    unfold nonzeroCount
    congr 1
    apply Finset.filter_eq_self.mpr
    intro i hi
    rw [hc i hi]
    exact ha.ne'
  apply (no_central_outcome_iff C coeff ha (fun i hi => by rw [hc i hi]; exact ⟨ha.le, le_rfl⟩)).mpr
  exact ⟨fun i hi => Or.inr (hc i hi), by simpa [hcount] using hodd⟩

lemma flat_shape_gap_lower {N k : ℕ} (coeff : Fin N → ℝ) {a : ℝ}
    (ha : 0 < a) (hk : Odd k) (hflat : IsFlatAt coeff k a) : a ≤ supportGap coeff := by
  classical
  obtain ⟨C, hcard, hcore, hzero⟩ := hflat
  apply (le_supportGap_iff coeff a).mpr
  intro ω
  have hodd : Odd C.card := by simpa [hcard] using hk
  have hg := odd_flat_core_gap C coeff ha hodd hcore ω
  have he : (∑ i ∈ C, coeff i * rademacherSign (ω i)) = rademacherSum coeff ω := by
    apply Finset.sum_subset (Finset.subset_univ C)
    intro i hi hiC
    rw [hzero i hiC, zero_mul]
  rw [he] at hg
  exact hg

lemma saturated_shape_gap_lower {N k : ℕ} (coeff : Fin N → ℝ) {a : ℝ}
    (ha : 0 < a) (hk : Odd k) (hc : ∀ i, 0 ≤ coeff i)
    (hvar : ∑ i, coeff i ^ 2 = 1) (hshape : IsSaturatedAt coeff k a) :
    a - Real.sqrt (1 - (k : ℝ) * a ^ 2) ≤ supportGap coeff := by
  classical
  obtain ⟨C, hcard, hcore, htail⟩ := hshape
  let T := Finset.univ \ C
  let V := ∑ i ∈ T, coeff i ^ 2
  let ell := ∑ i ∈ T, coeff i
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hell : 0 ≤ ell := Finset.sum_nonneg (fun i hi => hc i)
  have hCV : (∑ i ∈ C, coeff i ^ 2) + V = 1 := by
    have h := Finset.sum_sdiff (Finset.subset_univ C) (f := fun i => coeff i ^ 2)
    rw [hvar] at h
    linarith only [h]
  have hC : (∑ i ∈ C, coeff i ^ 2) = (k : ℝ) * a ^ 2 := by
    calc
      _ = ∑ i ∈ C, a ^ 2 := Finset.sum_congr rfl (fun i hi => by rw [hcore i hi])
      _ = _ := by simp [hcard]
  have hVe : V = 1 - (k : ℝ) * a ^ 2 := by linarith only [hC, hCV]
  have hLV : V = ell ^ 2 := (sum_sq_eq_sq_sum_iff_single T coeff (fun i hi => hc i)).mpr htail
  have hroot : ell = Real.sqrt (1 - (k : ℝ) * a ^ 2) := by
    have hsq := Real.sq_sqrt hV
    have hnon := Real.sqrt_nonneg V
    have he : ell = Real.sqrt V := by nlinarith only [hLV, hsq, hell, hnon]
    simpa [hVe] using he
  apply (le_supportGap_iff coeff _).mpr
  intro ω
  have hodd : Odd C.card := by simpa [hcard] using hk
  have hcg := odd_flat_core_gap C coeff ha hodd hcore ω
  have habs : |∑ i ∈ T, coeff i * rademacherSign (ω i)| ≤ ell := by
    calc
      _ ≤ ∑ i ∈ T, |coeff i * rademacherSign (ω i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ell := by
        apply Finset.sum_congr rfl
        intro i hi
        cases hω : ω i <;> simp [rademacherSign, abs_of_nonneg (hc i)]
  have hsum : rademacherSum coeff ω - (∑ i ∈ T, coeff i * rademacherSign (ω i)) =
      ∑ i ∈ C, coeff i * rademacherSign (ω i) := by
    have h := Finset.sum_sdiff (Finset.subset_univ C)
      (f := fun i => coeff i * rademacherSign (ω i))
    change (∑ i, coeff i * rademacherSign (ω i)) - _ = _
    linarith only [h]
  have ht := abs_sub (rademacherSum coeff ω) (∑ i ∈ T, coeff i * rademacherSign (ω i))
  rw [hsum] at ht
  rw [← hroot]
  linarith only [hcg, habs, ht]

lemma odd_step_energy (n : ℕ) :
    ((n : ℝ) + 2) * (1 / Real.sqrt ((n : ℝ) + 2)) ^ 2 = 1 := by
  have h := flat_normalized (show 0 < n + 2 by omega)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat] using h

lemma core_count_le_next {k n : ℕ} {x : ℝ}
    (hx : 1 / Real.sqrt ((n : ℝ) + 2) ≤ x)
    (henergy : (k : ℝ) * x ^ 2 ≤ 1) : k ≤ n + 2 := by
  have hlam : 0 < 1 / Real.sqrt ((n : ℝ) + 2) := by positivity
  have hx0 : 0 < x := hlam.trans_le hx
  have hs := (sq_le_sq₀ hlam.le hx0.le).mpr hx
  have hbase := mul_le_mul_of_nonneg_left hs (show 0 ≤ (n : ℝ) + 2 by positivity)
  rw [odd_step_energy n] at hbase
  by_contra h
  have hnk : n + 2 < k := Nat.lt_of_not_ge h
  have hnkR : (n : ℝ) + 2 < k := by exact_mod_cast hnk
  have hm := mul_lt_mul_of_pos_right hnkR (sq_pos_of_pos hx0)
  linarith only [hbase, hm, henergy]

lemma cap_lt_twice_step {n : ℕ} (hn : Odd n) {a : ℝ}
    (hna : (n : ℝ) * a ^ 2 ≤ 1) :
    a < 2 * (1 / Real.sqrt ((n : ℝ) + 2)) := by
  have hnpos : 0 < n := by
    have hmod := Nat.odd_iff.mp hn
    omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hmul := mul_le_mul_of_nonneg_right hnR (sq_nonneg a)
  have haSq : a ^ 2 ≤ 1 := by nlinarith
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hroot : 0 < Real.sqrt ((n : ℝ) + 2) := Real.sqrt_pos.2 hden
  have haProdSq : (a * Real.sqrt ((n : ℝ) + 2)) ^ 2 ≤ 3 := by
    rw [mul_pow, Real.sq_sqrt hden.le]
    nlinarith
  have haProd : a * Real.sqrt ((n : ℝ) + 2) < 2 := by nlinarith
  have h := (lt_div_iff₀ hroot).mpr haProd
  simpa only [mul_one_div] using h

lemma actual_core_sqrt_energy {N : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hhalf : a < 2 * x)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hvar : ∑ i, coeff i ^ 2 = 1)
    (hgap : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|) :
    ((gapCore coeff x).card : ℝ) * (x + Real.sqrt (tailVariance coeff x)) ^ 2 ≤
      1 - tailVariance coeff x := by
  have hd := actual_core_variance_data coeff hx.le ha hc hcap hvar
  have hcore := actual_high_gap_core coeff hx ha hhalf hc hcap hvar hgap
  have hroot : Real.sqrt (tailVariance coeff x) ≤ tailL1 coeff x := by
    have hs := Real.sq_sqrt hd.1
    have hn := Real.sqrt_nonneg (tailVariance coeff x)
    nlinarith only [hs, hn, hd.2.2.1, hd.2.2.2.1]
  have hs : (x + Real.sqrt (tailVariance coeff x)) ^ 2 ≤ (x + tailL1 coeff x) ^ 2 :=
    (sq_le_sq₀ (add_nonneg hx.le (Real.sqrt_nonneg _))
      (add_nonneg hx.le hd.2.2.1)).mpr (by linarith)
  exact (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)).trans hcore.2.2.2

lemma next_core_forces_flat {N n : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (ha : 0 ≤ a) (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hvar : ∑ i, coeff i ^ 2 = 1)
    (hx : 1 / Real.sqrt ((n : ℝ) + 2) ≤ x)
    (hcount : (gapCore coeff x).card = n + 2) :
    x = 1 / Real.sqrt ((n : ℝ) + 2) ∧
      IsFlatAt coeff (n + 2) (1 / Real.sqrt ((n : ℝ) + 2)) := by
  classical
  have hlam : 0 < 1 / Real.sqrt ((n : ℝ) + 2) := by positivity
  have hx0 : 0 < x := hlam.trans_le hx
  have hd := actual_core_variance_data coeff hx0.le ha hc hcap hvar
  have hkR : ((gapCore coeff x).card : ℝ) = (n : ℝ) + 2 := by exact_mod_cast hcount
  have he := hd.2.2.2.2.1
  rw [hkR] at he
  have hsq : x ^ 2 ≤ (1 / Real.sqrt ((n : ℝ) + 2)) ^ 2 := by
    apply (mul_le_mul_left (show 0 < (n : ℝ) + 2 by positivity)).mp
    exact he.trans_eq (odd_step_energy n).symm
  have hxeq : x = 1 / Real.sqrt ((n : ℝ) + 2) :=
    le_antisymm ((sq_le_sq₀ hx0.le hlam.le).mp hsq) hx
  have hbase : ((gapCore coeff x).card : ℝ) * x ^ 2 = 1 := by
    rw [hkR, hxeq, odd_step_energy]
  have hcoreLower : 1 ≤ ∑ i ∈ gapCore coeff x, coeff i ^ 2 := by
    rw [← hbase]
    calc
      _ = ∑ i ∈ gapCore coeff x, x ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => by
        have hxi := (Finset.mem_filter.mp hi).2
        exact (sq_le_sq₀ hx0.le (hc i)).mpr hxi)
  have hsum := core_tail_variance coeff x hvar
  have hVe : tailVariance coeff x = 0 := by linarith only [hcoreLower, hsum, hd.1]
  have hcoreSum : (∑ i ∈ gapCore coeff x, coeff i ^ 2) =
      ((gapCore coeff x).card : ℝ) * x ^ 2 := by linarith only [hsum, hVe, hbase]
  have hflatCore := constant_of_square_sum_lower (gapCore coeff x) coeff hx0.le
    (fun i hi => (Finset.mem_filter.mp hi).2) hcoreSum
  refine ⟨hxeq, gapCore coeff x, hcount, ?_, ?_⟩
  · intro i hi
    exact (hflatCore i hi).trans hxeq
  · intro i hi
    have hiT : i ∈ gapTail coeff x := by simp [gapTail, hi]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (hj : j ∈ gapTail coeff x) => sq_nonneg (coeff j))).mp hVe i hiT
    exact sq_eq_zero_iff.mp hz

lemma active_core_forces_saturated {N n : ℕ} (coeff : Fin N → ℝ) {x a : ℝ}
    (ha : 0 < a) (hna : (n : ℝ) * a ^ 2 ≤ 1) (hx : 0 < x)
    (hhalf : a < 2 * x) (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hvar : ∑ i, coeff i ^ 2 = 1)
    (hgap : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω|)
    (hkn : (gapCore coeff x).card ≤ n)
    (hxeq : x = a - Real.sqrt (1 - (n : ℝ) * a ^ 2)) :
    IsSaturatedAt coeff n a := by
  classical
  have hd := actual_core_variance_data coeff hx.le ha.le hc hcap hvar
  have hcore := actual_high_gap_core coeff hx ha.le hhalf hc hcap hvar hgap
  have henergy := actual_core_sqrt_energy coeff hx ha.le hhalf hc hcap hvar hgap
  obtain ⟨hcard, hVe⟩ := variance_cap_equality hcore.2.1 hkn ha hx.le hd.1 hna
    hd.2.2.2.2.2 henergy hxeq
  have hsum := core_tail_variance coeff x hvar
  have hC : (∑ i ∈ gapCore coeff x, coeff i ^ 2) =
      ((gapCore coeff x).card : ℝ) * a ^ 2 := by
    rw [hcard]
    linarith only [hsum, hVe]
  have hflatCore := constant_of_square_sum_upper (gapCore coeff x) coeff ha.le
    (fun i hi => ⟨hc i, hcap i⟩) hC
  have hroot : Real.sqrt (tailVariance coeff x) ≤ tailL1 coeff x := by
    have hs := Real.sq_sqrt hd.1
    have hn := Real.sqrt_nonneg (tailVariance coeff x)
    nlinarith only [hs, hn, hd.2.2.1, hd.2.2.2.1]
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcore.2.1
  have hci := hcore.2.2.1 i hi
  have hcapI := hcap i
  have hell : tailL1 coeff x ≤ Real.sqrt (tailVariance coeff x) := by
    rw [hVe]
    linarith only [hci, hcapI, hxeq]
  have hellEq : tailL1 coeff x = Real.sqrt (tailVariance coeff x) := le_antisymm hell hroot
  have hVell : tailVariance coeff x = (tailL1 coeff x) ^ 2 := by
    rw [hellEq, Real.sq_sqrt hd.1]
  have hsingle := (sum_sq_eq_sq_sum_iff_single (gapTail coeff x) coeff
    (fun i hi => hc i)).mp hVell
  exact ⟨gapCore coeff x, hcard, hflatCore, hsingle⟩

/-- Complete optimizer classification for nonnegative coefficient vectors,
including a zero residual at an odd flat endpoint. -/
theorem supportGap_equality_iff_nonnegative {N n : ℕ} (coeff : Fin N → ℝ)
    (hn : Odd n) {a : ℝ} (ha : 0 < a) (hna : (n : ℝ) * a ^ 2 ≤ 1)
    (hc : ∀ i, 0 ≤ coeff i) (hcap : ∀ i, coeff i ≤ a)
    (hvar : ∑ i, coeff i ^ 2 = 1) :
    supportGap coeff = capGapFormula n a ↔
      ((a - Real.sqrt (1 - (n : ℝ) * a ^ 2) ≤ 1 / Real.sqrt ((n : ℝ) + 2)) ∧
        IsFlatAt coeff (n + 2) (1 / Real.sqrt ((n : ℝ) + 2))) ∨
      ((1 / Real.sqrt ((n : ℝ) + 2) ≤ a - Real.sqrt (1 - (n : ℝ) * a ^ 2)) ∧
        IsSaturatedAt coeff n a) := by
  classical
  have hlam : 0 < 1 / Real.sqrt ((n : ℝ) + 2) := by positivity
  have hcapAbs : ∀ i, |coeff i| ≤ a := fun i => by rw [abs_of_nonneg (hc i)]; exact hcap i
  constructor
  · intro heq
    let x := supportGap coeff
    have hxbase : 1 / Real.sqrt ((n : ℝ) + 2) ≤ x := by
      rw [show x = capGapFormula n a from heq]
      exact le_max_left _ _
    have hx0 : 0 < x := hlam.trans_le hxbase
    have hhalf : a < 2 * x := (cap_lt_twice_step hn hna).trans_le
      (mul_le_mul_of_nonneg_left hxbase (by norm_num))
    have hgap : ∀ ω : BoolCube N, x ≤ |rademacherSum coeff ω| :=
      (le_supportGap_iff coeff x).mp le_rfl
    have hd := actual_core_variance_data coeff hx0.le ha.le hc hcap hvar
    have hcore := actual_high_gap_core coeff hx0 ha.le hhalf hc hcap hvar hgap
    have hcount := core_count_le_next hxbase hd.2.2.2.2.1
    by_cases hnext : (gapCore coeff x).card = n + 2
    · obtain ⟨hxeq, hflat⟩ := next_core_forces_flat coeff ha.le hc hcap hvar hxbase hnext
      refine Or.inl ⟨?_, hflat⟩
      have hright : a - Real.sqrt (1 - (n : ℝ) * a ^ 2) ≤ x := by
        rw [show x = capGapFormula n a from heq]
        exact le_max_right _ _
      simpa [hxeq] using hright
    · have hkn : (gapCore coeff x).card ≤ n := by
        have hkmod := Nat.odd_iff.mp hcore.1
        have hnmod := Nat.odd_iff.mp hn
        omega
      have henergy := actual_core_sqrt_energy coeff hx0 ha.le hhalf hc hcap hvar hgap
      have hxle := variance_cap_closure hcore.2.1 hkn ha.le hx0.le hd.1
        hd.2.2.2.2.2 henergy
      have hright : a - Real.sqrt (1 - (n : ℝ) * a ^ 2) ≤ x := by
        rw [show x = capGapFormula n a from heq]
        exact le_max_right _ _
      have hxeq : x = a - Real.sqrt (1 - (n : ℝ) * a ^ 2) := le_antisymm hxle hright
      exact Or.inr ⟨by linarith only [hxbase, hxeq],
        active_core_forces_saturated coeff ha hna hx0 hhalf hc hcap hvar hgap hkn hxeq⟩
  · rintro (⟨hbranch, hflat⟩ | ⟨hbranch, hsat⟩)
    · have hn2 : Odd (n + 2) := by
        have hm := Nat.odd_iff.mp hn
        apply Nat.odd_iff.mpr
        omega
      have hlo := flat_shape_gap_lower coeff hlam hn2 hflat
      apply le_antisymm (supportGap_le_formula coeff hn ha hna hcapAbs hvar)
      simpa only [capGapFormula, max_eq_left hbranch] using hlo
    · have hlo := saturated_shape_gap_lower coeff ha hn hc hvar hsat
      apply le_antisymm (supportGap_le_formula coeff hn ha hna hcapAbs hvar)
      simpa only [capGapFormula, max_eq_right hbranch] using hlo

/-- Complete exact optimizer iff for arbitrary signed coefficients and
zeros, expressed through their magnitudes on the original finite index set. -/
theorem supportGap_equality_iff {N n : ℕ} (coeff : Fin N → ℝ)
    (hn : Odd n) {a : ℝ} (ha : 0 < a) (hna : (n : ℝ) * a ^ 2 ≤ 1)
    (hcap : ∀ i, |coeff i| ≤ a) (hvar : ∑ i, coeff i ^ 2 = 1) :
    supportGap coeff = capGapFormula n a ↔
      ((a - Real.sqrt (1 - (n : ℝ) * a ^ 2) ≤ 1 / Real.sqrt ((n : ℝ) + 2)) ∧
        IsFlatAt (fun i => |coeff i|) (n + 2) (1 / Real.sqrt ((n : ℝ) + 2))) ∨
      ((1 / Real.sqrt ((n : ℝ) + 2) ≤ a - Real.sqrt (1 - (n : ℝ) * a ^ 2)) ∧
        IsSaturatedAt (fun i => |coeff i|) n a) := by
  have h := supportGap_equality_iff_nonnegative (fun i => |coeff i|) hn ha hna
    (fun i => abs_nonneg _) hcap (by simpa only [sq_abs] using hvar)
  simpa only [supportGap_abs] using h

/-- An explicit odd band index, removing any need to assume that a suitable
odd integer has been chosen for a given positive cap. -/
def oddBandIndex (a : ℝ) : ℕ := 2 * ⌊(1 / a ^ 2 - 1) / 2⌋₊ + 1

theorem oddBandIndex_spec {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Odd (oddBandIndex a) ∧ (oddBandIndex a : ℝ) * a ^ 2 ≤ 1 ∧
      1 ≤ ((oddBandIndex a : ℝ) + 2) * a ^ 2 := by
  have haSq : 0 < a ^ 2 := sq_pos_of_pos ha
  have haSq1 : a ^ 2 ≤ 1 := by nlinarith
  have hinv : 1 ≤ 1 / a ^ 2 := (le_div_iff₀ haSq).mpr (by simpa using haSq1)
  have hz : 0 ≤ (1 / a ^ 2 - 1) / 2 := by linarith
  have hf := Nat.floor_le hz
  have hfu := Nat.lt_floor_add_one ((1 / a ^ 2 - 1) / 2)
  have hcast : (oddBandIndex a : ℝ) =
      2 * (⌊(1 / a ^ 2 - 1) / 2⌋₊ : ℝ) + 1 := by
    simp only [oddBandIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⌊(1 / a ^ 2 - 1) / 2⌋₊, ?_⟩
    unfold oddBandIndex
    omega
  · apply (le_div_iff₀ haSq).mp
    rw [hcast]
    linarith only [hf]
  · apply (div_le_iff₀ haSq).mp
    rw [hcast]
    linarith only [hfu]

/-- Exact value for every cap in `(0,1]`, with the band index computed from
the cap itself. The supremum remains the actual all-dimensional one. -/
theorem maximalSupportGap_all_caps {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    maximalSupportGap a = capGapFormula (oddBandIndex a) a := by
  have hs := oddBandIndex_spec ha ha1
  exact maximalSupportGap_exact hs.1 ha hs.2.1 hs.2.2

/-- The complete optimizer classification, now for every cap directly and
with the actual all-dimensional supremum on the left-hand side. -/
theorem supportGap_maximal_iff_all_caps {N : ℕ} (coeff : Fin N → ℝ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hcap : ∀ i, |coeff i| ≤ a) (hvar : ∑ i, coeff i ^ 2 = 1) :
    supportGap coeff = maximalSupportGap a ↔
      ((a - Real.sqrt (1 - (oddBandIndex a : ℝ) * a ^ 2) ≤
          1 / Real.sqrt ((oddBandIndex a : ℝ) + 2)) ∧
        IsFlatAt (fun i => |coeff i|) (oddBandIndex a + 2)
          (1 / Real.sqrt ((oddBandIndex a : ℝ) + 2))) ∨
      ((1 / Real.sqrt ((oddBandIndex a : ℝ) + 2) ≤
          a - Real.sqrt (1 - (oddBandIndex a : ℝ) * a ^ 2)) ∧
        IsSaturatedAt (fun i => |coeff i|) (oddBandIndex a) a) := by
  rw [maximalSupportGap_all_caps ha ha1]
  have hs := oddBandIndex_spec ha ha1
  exact supportGap_equality_iff coeff hs.1 ha hs.2.1 hcap hvar

#print axioms sum_sq_eq_sq_sum_iff_single
#print axioms flat_shape_gap_lower
#print axioms saturated_shape_gap_lower
#print axioms next_core_forces_flat
#print axioms active_core_forces_saturated
#print axioms supportGap_equality_iff
#print axioms oddBandIndex_spec
#print axioms maximalSupportGap_all_caps
#print axioms supportGap_maximal_iff_all_caps

end Breakthrough.ExactSupportGap
