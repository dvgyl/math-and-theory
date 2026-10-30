/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the reused coefficient construction: Yijun Yuan

The inverse-Frobenius coefficient construction and the elementary `finsum` split
are adapted from ArtinSchreierNeg.lean at
https://github.com/YijunYuan/TrustworthyKedlaya/blob/f97be4372713e25a21603dec26706d8bb0cd9d24/TrustworthyKedlaya/Kedlaya/ArtinSchreierNeg.lean
The present general summability proofs and support-closure invariant are new
formalization work for this project (2026-10-30), without a novelty claim for the
classical Artin-Schreier root formula.
-/
import HahnFrobenius
import SupportClosure

/-!
# Actual Hahn-summable Artin-Schreier roots over a perfect field

These constructions use arbitrary Hahn supports and arbitrary perfect coefficient
fields. They do not assume a finite coefficient field, uniform periodicity, or a
pre-existing Artin-Schreier root. Both requirements in `SummableFamily` are proved:
well-ordered union of supports and finite coefficient co-support.
-/

noncomputable section
open HahnSeries Set
open scoped Pointwise

namespace NTCThird

/-- A union of well-ordered sets is well ordered if, below each point of the
union, only finitely many members of the family occur. -/
theorem isPWO_iUnion_of_finite_lower_indices {S : ℕ → Set ℚ}
    (hS : ∀ n, (S n).IsPWO)
    (hfin : ∀ q ∈ ⋃ n, S n, {n | ∃ r ∈ S n, r ≤ q}.Finite) :
    (⋃ n, S n).IsPWO := by
  classical
  apply Set.IsWF.isPWO
  rw [Set.isWF_iff_no_descending_seq]
  intro f hf hall
  let I : Set ℕ := {n | ∃ r ∈ S n, r ≤ f 0}
  have hI : I.Finite := hfin (f 0) (hall 0)
  have hWF : (⋃ n ∈ hI.toFinset, S n).IsWF :=
    (Finset.isWF_bUnion hI.toFinset).2 (fun n _ => (hS n).isWF)
  apply (Set.isWF_iff_no_descending_seq.mp hWF) f hf
  intro m
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hall m)
  have hnI : n ∈ I := ⟨f m, hn, hf.antitone (Nat.zero_le m)⟩
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hI.mem_toFinset.mpr hnI, hn⟩⟩

/-- Negative supports contracted by inverse powers have only finitely many
active dilation indices below any negative rational number. -/
theorem finite_lower_indices_inv_pow {S : Set ℚ} (p : ℕ) (hp : 1 < p)
    (hbelow : BddBelow S) {q : ℚ} (hq : q < 0) :
    {n : ℕ | ∃ r ∈ (fun s : ℚ => s / (p : ℚ)^n) '' S, r ≤ q}.Finite := by
  obtain ⟨m, hm⟩ := hbelow
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp
  have hqpos : (0 : ℚ) < -q := neg_pos.mpr hq
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((-m) / (-q)) hp1
  apply (Set.finite_Iio N).subset
  rintro n ⟨r, ⟨s, hs, rfl⟩, hr⟩
  have hpowpos : (0 : ℚ) < (p : ℚ)^n := pow_pos (lt_trans zero_lt_one hp1) n
  have hsle : s ≤ q * (p : ℚ)^n := (div_le_iff₀ hpowpos).mp hr
  have hbound : (p : ℚ)^n ≤ (-m) / (-q) := by
    rw [le_div_iff₀ hqpos]
    have hms := hm hs
    nlinarith
  have hnN : n < N := by
    by_contra hn
    have hpow := pow_le_pow_right₀ hp1.le (not_lt.mp hn)
    exact (not_lt_of_ge hpow) (hbound.trans_lt hN)
  exact hnN

/-- Arbitrary well-ordered negative supports remain well ordered after taking
all inverse-power contractions. -/
theorem isPWO_iUnion_inv_pow {S : Set ℚ} (p : ℕ) (hp : 1 < p)
    (hS : S.IsPWO) (hbelow : BddBelow S) (hneg : S ⊆ Iio 0) :
    (⋃ n : ℕ, (fun s : ℚ => s / (p : ℚ)^n) '' S).IsPWO := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
  apply isPWO_iUnion_of_finite_lower_indices
  · intro n
    exact hS.image_of_monotone (fun _ _ h => div_le_div_of_nonneg_right h (pow_pos hp0 n).le)
  · intro q hq
    obtain ⟨n, s, hs, rfl⟩ := Set.mem_iUnion.mp hq
    exact finite_lower_indices_inv_pow p hp hbelow (div_neg_of_neg_of_pos (hneg hs) (pow_pos hp0 n))

/-- A one-to-one reindexing selects an actual Hahn-summable subfamily. -/
noncomputable def summableFamilyComp {R α β : Type*} [AddCommMonoid R]
    (s : HahnSeries.SummableFamily ℚ R α) (f : β → α) (hf : Function.Injective f) :
    HahnSeries.SummableFamily ℚ R β where
  toFun b := s (f b)
  isPWO_iUnion_support' := s.isPWO_iUnion_support.mono (by
    intro q hq
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hq
    exact Set.mem_iUnion.mpr ⟨f b, hb⟩)
  finite_co_support' q := (s.finite_co_support q).preimage hf.injOn

/-- Splitting off the first term of a finitely supported coefficient family. -/
theorem finsum_nat_eq_zero_add {M : Type*} [AddCommMonoid M] {f : ℕ → M}
    (hf : (Function.support f).Finite) :
    ∑ᶠ n, f n = f 0 + ∑ᶠ n, f (n + 1) := by
  obtain ⟨K, hK⟩ := hf.bddAbove
  have hsub : Function.support f ⊆ ↑(Finset.range (K + 1)) := fun x hx => by
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (hK hx)
  have hsub' : Function.support (fun n => f (n + 1)) ⊆ ↑(Finset.range K) := fun x hx => by
    simp only [Finset.coe_range, Set.mem_Iio]
    have : x + 1 ≤ K := hK hx
    omega
  rw [finsum_eq_sum_of_support_subset _ hsub, finsum_eq_sum_of_support_subset _ hsub',
    Finset.sum_range_succ']
  exact add_comm _ _

section PerfectField
variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] [PerfectRing k p]

@[simp] theorem invFrobenius_iterate_zero (n : ℕ) :
    ((frobeniusEquiv k p).symm)^[n] (0 : k) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, map_zero, ih]

/-- The `n`-fold inverse Frobenius as an actual Hahn series. -/
def invFrobeniusIterHahn (y : HahnSeries ℚ k) (n : ℕ) : HahnSeries ℚ k where
  coeff q := ((frobeniusEquiv k p).symm)^[n] (y.coeff (q * (p : ℚ)^n))
  isPWO_support' := by
    have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
    apply (y.isPWO_support.image_of_monotone
      (fun a b hab => div_le_div_of_nonneg_right hab (pow_pos hp0 n).le)).mono
    intro q hq
    refine ⟨q * (p : ℚ)^n, ?_, ?_⟩
    · change y.coeff (q * (p : ℚ)^n) ≠ 0
      intro hz
      apply hq
      change ((frobeniusEquiv k p).symm)^[n] (y.coeff (q * (p : ℚ)^n)) = 0
      rw [hz, invFrobenius_iterate_zero]
    · exact mul_div_cancel_right₀ q (pow_ne_zero n hp0.ne')

@[simp] theorem coeff_invFrobeniusIterHahn (y : HahnSeries ℚ k) (n : ℕ) (q : ℚ) :
    (invFrobeniusIterHahn p y n).coeff q =
      ((frobeniusEquiv k p).symm)^[n] (y.coeff (q * (p : ℚ)^n)) := rfl

@[simp] theorem invFrobeniusIterHahn_zero (y : HahnSeries ℚ k) :
    invFrobeniusIterHahn p y 0 = y := by
  ext q
  simp [coeff_invFrobeniusIterHahn]

theorem support_invFrobeniusIterHahn (y : HahnSeries ℚ k) (n : ℕ) :
    (invFrobeniusIterHahn p y n).support =
      (fun q : ℚ => q / (p : ℚ)^n) '' y.support := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  have hpn : (p : ℚ)^n ≠ 0 := pow_ne_zero n hp0.ne'
  have hinj := (frobeniusEquiv k p).symm.injective.iterate n
  ext q
  constructor
  · intro hq
    refine ⟨q * (p : ℚ)^n, ?_, mul_div_cancel_right₀ q hpn⟩
    rw [HahnSeries.mem_support] at hq ⊢
    intro hz
    apply hq
    simp [coeff_invFrobeniusIterHahn, hz]
  · rintro ⟨r, hr, rfl⟩
    rw [HahnSeries.mem_support, coeff_invFrobeniusIterHahn, div_mul_cancel₀ _ hpn]
    intro hz
    apply hr
    apply hinj
    simpa using hz

/-- All inverse-Frobenius iterates of a negative Hahn series form a genuine
summable family, including the zeroth iterate. -/
def asNegAllFamily (y : HahnSeries ℚ k) (hneg : y.support ⊆ Iio 0) :
    HahnSeries.SummableFamily ℚ k ℕ where
  toFun n := invFrobeniusIterHahn p y n
  isPWO_iUnion_support' := by
    simp only [support_invFrobeniusIterHahn]
    exact isPWO_iUnion_inv_pow p hp.out.one_lt y.isPWO_support
      ⟨y.order, fun _ h => HahnSeries.order_le_of_coeff_ne_zero h⟩ hneg
  finite_co_support' q := by
    by_cases hq : q < 0
    · apply (finite_lower_indices_inv_pow p hp.out.one_lt
        (show BddBelow y.support from
          ⟨y.order, fun _ h => HahnSeries.order_le_of_coeff_ne_zero h⟩) hq).subset
      intro n hn
      refine ⟨q, ?_, le_rfl⟩
      rw [← support_invFrobeniusIterHahn p y n]
      exact hn
    · apply Set.finite_empty.subset
      intro n hn
      have hm : q ∈ (invFrobeniusIterHahn p y n).support := hn
      rw [support_invFrobeniusIterHahn] at hm
      obtain ⟨r, hr, rfl⟩ := hm
      have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
      exact hq (div_neg_of_neg_of_pos (hneg hr) (pow_pos hp0 n))

/-- The negative Artin-Schreier root family uses the strictly positive inverse
Frobenius iterates. -/
def asNegFamily (y : HahnSeries ℚ k) (hneg : y.support ⊆ Iio 0) :
    HahnSeries.SummableFamily ℚ k ℕ :=
  summableFamilyComp (asNegAllFamily p y hneg) (fun n : ℕ => n + 1) (by intro a b h; exact Nat.add_right_cancel h)

/-- The negative Artin-Schreier root is the formal Hahn sum. -/
def asNegRoot (y : HahnSeries ℚ k) (hneg : y.support ⊆ Iio 0) : HahnSeries ℚ k :=
  (asNegFamily p y hneg).hsum


/-- Frobenius commutes with a finitely supported sum of coefficients. -/
theorem finsum_pow_char {f : ℕ → k} (hf : (Function.support f).Finite) :
    (∑ᶠ n, f n)^p = ∑ᶠ n, (f n)^p := by
  exact (frobenius k p).toAddMonoidHom.map_finsum hf

/-- Coefficient form of cancellation of one inverse-Frobenius iterate. -/
theorem coeff_invFrobeniusIterHahn_succ_pow (y : HahnSeries ℚ k) (n : ℕ) (q : ℚ) :
    ((invFrobeniusIterHahn p y (n+1)).coeff q)^p =
      (invFrobeniusIterHahn p y n).coeff ((p : ℚ)*q) := by
  rw [coeff_invFrobeniusIterHahn, Function.iterate_succ_apply',
    frobeniusEquiv_symm_pow_p, coeff_invFrobeniusIterHahn]
  congr 2
  rw [pow_succ]
  ring

/-- The actual inverse-Frobenius iterates telescope under Hahn-series powers. -/
theorem invFrobeniusIterHahn_succ_pow (y : HahnSeries ℚ k) (n : ℕ) :
    (invFrobeniusIterHahn p y (n+1))^p = invFrobeniusIterHahn p y n := by
  ext q
  rw [coeff_pow_char, coeff_invFrobeniusIterHahn_succ_pow]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [mul_div_cancel₀ q hp0]

/-- The negative Hahn sum solves the full Artin-Schreier equation. -/
theorem asNegRoot_equation (y : HahnSeries ℚ k) (hneg : y.support ⊆ Iio 0) :
    (asNegRoot p y hneg)^p - asNegRoot p y hneg = y := by
  ext q
  rw [HahnSeries.coeff_sub, coeff_pow_char]
  change (∑ᶠ n, (invFrobeniusIterHahn p y (n+1)).coeff (q / p))^p -
    (∑ᶠ n, (invFrobeniusIterHahn p y (n+1)).coeff q) = y.coeff q
  have hfinite : (Function.support (fun n : ℕ =>
      (invFrobeniusIterHahn p y (n+1)).coeff (q / p))).Finite :=
    (asNegFamily p y hneg).finite_co_support (q / p)
  rw [finsum_pow_char p hfinite]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  simp_rw [coeff_invFrobeniusIterHahn_succ_pow, mul_div_cancel₀ q hp0]
  have hsplit := finsum_nat_eq_zero_add ((asNegAllFamily p y hneg).finite_co_support q)
  change (∑ᶠ n, (invFrobeniusIterHahn p y n).coeff q) =
    (invFrobeniusIterHahn p y 0).coeff q +
      ∑ᶠ n, (invFrobeniusIterHahn p y (n+1)).coeff q at hsplit
  rw [hsplit, invFrobeniusIterHahn_zero, add_sub_cancel_right]

/-- The negative root's real support is contained in the explicit union of
strictly positive inverse-power dilations of the original real support. -/
theorem realSupport_asNegRoot_subset (y : HahnSeries ℚ k) (hneg : y.support ⊆ Iio 0) :
    realSupport (asNegRoot p y hneg) ⊆
      ⋃ n : ℕ, ⋃ (_ : 1 ≤ n), ((p : ℝ)^n)⁻¹ • realSupport y := by
  rintro x ⟨q, hq, rfl⟩
  have hm := HahnSeries.SummableFamily.support_hsum_subset
    (s := asNegFamily p y hneg) hq
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hm
  change q ∈ (invFrobeniusIterHahn p y (n+1)).support at hn
  rw [support_invFrobeniusIterHahn] at hn
  obtain ⟨r, hr, rfl⟩ := hn
  refine Set.mem_iUnion.mpr ⟨n+1, Set.mem_iUnion.mpr ⟨by omega, ?_⟩⟩
  apply Set.mem_smul_set.mpr
  refine ⟨(r : ℝ), ⟨r, hr, rfl⟩, ?_⟩
  simp only [smul_eq_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  ring

/-- The real support-closure invariant is preserved by the negative
Artin-Schreier root. The subgroup need not be topologically closed. -/
theorem supportClosureIn_asNegRoot (Γ : AddSubgroup ℝ)
    (hdiv : ∀ x : ℝ, x ∈ Γ → x / (p : ℝ) ∈ Γ)
    (y : HahnSeries ℚ k) (hneg : y.support ⊆ Iio 0)
    (hy : SupportClosureIn Γ y) : SupportClosureIn Γ (asNegRoot p y hneg) := by
  apply (closure_mono (realSupport_asNegRoot_subset p y hneg)).trans
  apply closure_iUnion_inv_pow_smul_subset_addSubgroup Γ p hp.out.two_le
    (bddBelow_realSupport y) _ hy hdiv
  rintro x ⟨q, hq, rfl⟩
  change (q : ℝ) < 0
  exact_mod_cast hneg hq


/-- Strictly positive support gives positive Hahn valuation, including the
zero series whose valuation is top. -/
theorem zero_lt_orderTop_of_positive_support (y : HahnSeries ℚ k)
    (hpos : y.support ⊆ Ioi 0) : 0 < y.orderTop := by
  apply lt_orderTop_of_coeff_zero_le y 0
  intro q hq
  by_contra hz
  exact (not_le_of_gt (hpos hz)) hq

/-- Frobenius iterates of a positive Hahn series form a genuine summable
subfamily of all positive-valuation powers. -/
def asPosFamily (y : HahnSeries ℚ k) (hpos : y.support ⊆ Ioi 0) :
    HahnSeries.SummableFamily ℚ k ℕ :=
  summableFamilyComp (HahnSeries.SummableFamily.powers y
    (zero_lt_orderTop_of_positive_support y hpos))
    (fun n : ℕ => p^n) (Nat.pow_right_injective hp.out.two_le)

/-- The positive Artin-Schreier root is minus the Hahn sum of all Frobenius
iterates, starting with the zeroth iterate. -/
def asPosRoot (y : HahnSeries ℚ k) (hpos : y.support ⊆ Ioi 0) : HahnSeries ℚ k :=
  -(asPosFamily p y hpos).hsum

/-- Frobenius telescoping of the positive sum. -/
theorem asPosFamily_hsum_equation (y : HahnSeries ℚ k) (hpos : y.support ⊆ Ioi 0) :
    (asPosFamily p y hpos).hsum^p = (asPosFamily p y hpos).hsum - y := by
  ext q
  rw [coeff_pow_char, HahnSeries.coeff_sub]
  change (∑ᶠ n, (y^(p^n)).coeff (q/p))^p =
    (∑ᶠ n, (y^(p^n)).coeff q) - y.coeff q
  have hfinite : (Function.support (fun n : ℕ => (y^(p^n)).coeff (q/p))).Finite :=
    (asPosFamily p y hpos).finite_co_support (q/p)
  rw [finsum_pow_char p hfinite]
  have hterm : ∀ n : ℕ, ((y^(p^n)).coeff (q/p))^p = (y^(p^(n+1))).coeff q := by
    intro n
    rw [← coeff_pow_char, ← pow_mul, ← pow_succ]
  simp_rw [hterm]
  have hsplit := finsum_nat_eq_zero_add ((asPosFamily p y hpos).finite_co_support q)
  change (∑ᶠ n, (y^(p^n)).coeff q) =
    (y^(p^0)).coeff q + ∑ᶠ n, (y^(p^(n+1))).coeff q at hsplit
  rw [hsplit, pow_zero, pow_one]
  abel

/-- The positive Hahn sum solves the full Artin-Schreier equation. -/
theorem asPosRoot_equation (y : HahnSeries ℚ k) (hpos : y.support ⊆ Ioi 0) :
    (asPosRoot p y hpos)^p - asPosRoot p y hpos = y := by
  change (-(asPosFamily p y hpos).hsum)^p - (-(asPosFamily p y hpos).hsum) = y
  have hnegpow (z : HahnSeries ℚ k) : (-z)^p = -(z^p) :=
    (frobenius (HahnSeries ℚ k) p).map_neg z
  rw [hnegpow, asPosFamily_hsum_equation]
  abel

/-- The positive root support is in the explicit expanding Frobenius union. -/
theorem realSupport_asPosRoot_subset (y : HahnSeries ℚ k) (hpos : y.support ⊆ Ioi 0) :
    realSupport (asPosRoot p y hpos) ⊆
      ⋃ n : ℕ, (p : ℝ)^n • realSupport y := by
  rintro x ⟨q, hq, rfl⟩
  change q ∈ (-(asPosFamily p y hpos).hsum).support at hq
  rw [HahnSeries.support_neg] at hq
  have hm := HahnSeries.SummableFamily.support_hsum_subset hq
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hm
  change q ∈ (y^(p^n)).support at hn
  rw [support_pow_char_pow] at hn
  obtain ⟨r, hr, rfl⟩ := hn
  refine Set.mem_iUnion.mpr ⟨n, Set.mem_smul_set.mpr ?_⟩
  refine ⟨(r : ℝ), ⟨r, hr, rfl⟩, ?_⟩
  simp only [smul_eq_mul, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]

/-- Positive Hahn support is uniformly separated from zero, because its
nonempty support has an attained minimum. -/
theorem realSupport_positive_lower_bound (y : HahnSeries ℚ k)
    (hpos : y.support ⊆ Ioi 0) :
    ∃ ε : ℝ, 0 < ε ∧ realSupport y ⊆ Ici ε := by
  by_cases hy : y = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    rintro x ⟨q, hq, rfl⟩
    simp [hy] at hq
  · refine ⟨(y.order : ℝ), ?_, ?_⟩
    · exact_mod_cast hpos (HahnSeries.coeff_order_ne_zero hy)
    · rintro x ⟨q, hq, rfl⟩
      change (y.order : ℝ) ≤ (q : ℝ)
      exact_mod_cast HahnSeries.order_le_of_coeff_ne_zero hq

/-- The real support-closure invariant is preserved by the positive
Artin-Schreier root without an upper support bound. -/
theorem supportClosureIn_asPosRoot (Γ : AddSubgroup ℝ)
    (y : HahnSeries ℚ k) (hpos : y.support ⊆ Ioi 0)
    (hy : SupportClosureIn Γ y) : SupportClosureIn Γ (asPosRoot p y hpos) := by
  obtain ⟨ε, hε, hlower⟩ := realSupport_positive_lower_bound y hpos
  exact (closure_mono (realSupport_asPosRoot_subset p y hpos)).trans
    (closure_iUnion_pow_smul_subset_addSubgroup Γ p hp.out.two_le hε hlower hy)


/-- Restriction to any exponent set preserves the real support-closure
invariant. This includes both sign truncations. -/
theorem supportClosureIn_hahnRestrict (Γ : AddSubgroup ℝ) (S : Set ℚ)
    (y : HahnSeries ℚ k) (hy : SupportClosureIn Γ y) :
    SupportClosureIn Γ (hahnRestrict S y) := by
  apply (closure_mono ?_).trans hy
  rintro x ⟨q, hq, rfl⟩
  exact ⟨q, support_hahnRestrict_subset S y hq, rfl⟩

/-- Every constant Hahn series satisfies the support-closure invariant for
every additive subgroup. -/
theorem supportClosureIn_constant (Γ : AddSubgroup ℝ) (c : k) :
    SupportClosureIn Γ (HahnSeries.C (Γ := ℚ) c) := by
  have hsub : realSupport (HahnSeries.C (Γ := ℚ) c) ⊆ ({0} : Set ℝ) := by
    rintro x ⟨q, hq, rfl⟩
    have hq0 : q = 0 := HahnSeries.support_single_subset hq
    simp [hq0]
  intro x hx
  have hx0 := closure_minimal hsub isClosed_singleton hx
  have : x = 0 := Set.mem_singleton_iff.mp hx0
  simpa [this] using Γ.zero_mem

variable [IsAlgClosed k]

/-- The constant coefficient equation over the algebraically closed
coefficient field. -/
theorem exists_artinSchreier_constant (a : k) : ∃ c : k, c^p - c = a := by
  let f : Polynomial k := Polynomial.X^p - Polynomial.X - Polynomial.C a
  have hcoeff : f.coeff p = 1 := by
    simp [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, hp.out.ne_zero, hp.out.ne_one,
      Ne.symm hp.out.ne_zero, Ne.symm hp.out.ne_one]
  have hdeg : f.degree ≠ 0 := by
    intro hz
    have hle := Polynomial.le_degree_of_ne_zero
      (show f.coeff p ≠ 0 by rw [hcoeff]; exact one_ne_zero)
    rw [hz] at hle
    have hpos : (0 : WithBot ℕ) < (p : WithBot ℕ) := by exact_mod_cast hp.out.pos
    exact (not_le_of_gt hpos) hle
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root f hdeg
  refine ⟨c, ?_⟩
  have hz : c^p - c - a = 0 := by
    simpa only [f, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] using hc
  exact sub_eq_zero.mp hz

/-- An arbitrary Hahn series whose real support closure lies in a p-divisible
additive subgroup has an actual Artin-Schreier root with the same invariant. -/
theorem exists_asRoot_supportClosureIn (Γ : AddSubgroup ℝ)
    (hdiv : ∀ x : ℝ, x ∈ Γ → x / (p : ℝ) ∈ Γ)
    (y : HahnSeries ℚ k) (hy : SupportClosureIn Γ y) :
    ∃ x : HahnSeries ℚ k, x^p - x = y ∧ SupportClosureIn Γ x := by
  let yn := hahnRestrict (Iio 0) y
  let yp := hahnRestrict (Ioi 0) y
  have hn : yn.support ⊆ Iio 0 := support_hahnRestrict_subset_set (Iio 0) y
  have hpos : yp.support ⊆ Ioi 0 := support_hahnRestrict_subset_set (Ioi 0) y
  obtain ⟨c, hc⟩ := exists_artinSchreier_constant p (y.coeff 0)
  let a := asNegRoot p yn hn
  let b := asPosRoot p yp hpos
  have ha : a^p - a = yn := asNegRoot_equation p yn hn
  have hb : b^p - b = yp := asPosRoot_equation p yp hpos
  have hconst : (HahnSeries.C (Γ := ℚ) c)^p - HahnSeries.C (Γ := ℚ) c =
      HahnSeries.single 0 (y.coeff 0) := by
    simpa only [map_sub, map_pow] using congrArg (HahnSeries.C (Γ := ℚ)) hc
  refine ⟨a + HahnSeries.C c + b, ?_, ?_⟩
  · calc
      (a + HahnSeries.C c + b)^p - (a + HahnSeries.C c + b) =
          (a^p - a) + ((HahnSeries.C c)^p - HahnSeries.C c) + (b^p - b) := by
        rw [add_pow_char, add_pow_char]
        ring
      _ = yn + HahnSeries.single 0 (y.coeff 0) + yp := by rw [ha, hconst, hb]
      _ = y := (hahnRestrict_tridecomp 0 y).symm
  · apply supportClosureIn_add Γ _ _
    · apply supportClosureIn_add Γ _ _
      · exact supportClosureIn_asNegRoot p Γ hdiv yn hn
          (supportClosureIn_hahnRestrict Γ (Iio 0) y hy)
      · exact supportClosureIn_constant Γ c
    · exact supportClosureIn_asPosRoot p Γ yp hpos
        (supportClosureIn_hahnRestrict Γ (Ioi 0) y hy)

/-- Every Frobenius-fixed Hahn series over an algebraically closed coefficient
field is constant. This is proved from the actual roots of X^p-X. -/
theorem exists_constant_of_pow_eq_self (z : HahnSeries ℚ k) (hz : z^p = z) :
    ∃ c : k, z = HahnSeries.C c := by
  let f : Polynomial k := Polynomial.X^p - Polynomial.X
  have hf : f ≠ 0 := by
    intro hzero
    have hc := congrArg (fun g : Polynomial k => g.coeff p) hzero
    simpa [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, hp.out.ne_one, Ne.symm hp.out.ne_one] using hc
  have heval : f.eval₂ (HahnSeries.C (Γ := ℚ)) z = 0 := by
    simp only [f, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, hz,
      sub_self]
  have hmem := (Polynomial.mem_roots_map_of_injective
    (HahnSeries.C (Γ := ℚ) (R := k)).injective hf).mpr heval
  rw [Polynomial.roots_map (HahnSeries.C (Γ := ℚ)) (IsAlgClosed.splits f)] at hmem
  obtain ⟨c, _, hc⟩ := Multiset.mem_map.mp hmem
  exact ⟨c, hc.symm⟩

/-- Every actual Artin-Schreier root preserves the support-closure invariant.
The statement quantifies over all Hahn series roots, not just the constructed
choice; the difference from that choice is proved to be constant. -/
theorem supportClosureIn_of_as_equation (Γ : AddSubgroup ℝ)
    (hdiv : ∀ t : ℝ, t ∈ Γ → t / (p : ℝ) ∈ Γ)
    (x y : HahnSeries ℚ k) (hy : SupportClosureIn Γ y) (hx : x^p - x = y) :
    SupportClosureIn Γ x := by
  obtain ⟨r, hr, hrΓ⟩ := exists_asRoot_supportClosureIn p Γ hdiv y hy
  have hdiff : (x-r)^p = x-r := by
    rw [sub_pow_char]
    linear_combination hx - hr
  obtain ⟨c, hc⟩ := exists_constant_of_pow_eq_self p (x-r) hdiff
  have hxrepr : x = r + HahnSeries.C c := by rw [← hc]; abel
  rw [hxrepr]
  exact supportClosureIn_add Γ r _ hrΓ (supportClosureIn_constant Γ c)


/-- Series satisfying the support-closure invariant form a subalgebra over
any field all of whose elements satisfy that invariant. -/
noncomputable def supportClosureSubalgebra (Γ : AddSubgroup ℝ) (K : Subfield (HahnSeries ℚ k))
    (hK : ∀ f ∈ K, SupportClosureIn Γ f) : Subalgebra K (HahnSeries ℚ k) where
  carrier := {f | SupportClosureIn Γ f}
  zero_mem' := by simpa using supportClosureIn_constant (k := k) Γ 0
  one_mem' := by simpa using supportClosureIn_constant (k := k) Γ 1
  add_mem' := fun hf hg => supportClosureIn_add Γ _ _ hf hg
  mul_mem' := fun hf hg => supportClosureIn_mul Γ _ _ hf hg
  algebraMap_mem' := fun a => hK a a.property

/-- Once a generator is algebraic, field adjunction creates no extra
support-closure difficulty: the field adjoin equals the algebra adjoin. -/
theorem supportClosureIn_fieldAdjoin (Γ : AddSubgroup ℝ)
    (K : Subfield (HahnSeries ℚ k)) (hK : ∀ f ∈ K, SupportClosureIn Γ f)
    (x : HahnSeries ℚ k) (hx : IsIntegral K x) (hxΓ : SupportClosureIn Γ x)
    (z : HahnSeries ℚ k) (hz : z ∈ IntermediateField.adjoin K {x}) :
    SupportClosureIn Γ z := by
  have hsub : Algebra.adjoin K {x} ≤ supportClosureSubalgebra Γ K hK := by
    apply Algebra.adjoin_le
    intro a ha
    have hax : a = x := Set.mem_singleton_iff.mp ha
    simpa only [hax] using hxΓ
  have hz' : z ∈ Algebra.adjoin K {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral hx]
    exact hz
  exact hsub hz'

/-- An actual AS equation over K certifies integrality over K. -/
theorem isIntegral_of_as_equation (K : Subfield (HahnSeries ℚ k))
    (x y : HahnSeries ℚ k) (hyK : y ∈ K) (hx : x^p - x = y) : IsIntegral K x := by
  apply IsAlgebraic.isIntegral
  let f : Polynomial K := Polynomial.X^p - Polynomial.X - Polynomial.C ⟨y, hyK⟩
  refine ⟨f, ?_, ?_⟩
  · intro hzero
    have hc := congrArg (fun g : Polynomial K => g.coeff p) hzero
    simpa [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, hp.out.ne_zero, hp.out.ne_one,
      Ne.symm hp.out.ne_zero, Ne.symm hp.out.ne_one] using hc
  · simp only [f, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    change x^p - x - y = 0
    rw [hx, sub_self]

/-- One full AS field extension preserves the support-closure invariant for
all elements of the extension. -/
theorem supportClosureIn_asFieldAdjoin (Γ : AddSubgroup ℝ)
    (hdiv : ∀ t : ℝ, t ∈ Γ → t / (p : ℝ) ∈ Γ)
    (K : Subfield (HahnSeries ℚ k)) (hK : ∀ f ∈ K, SupportClosureIn Γ f)
    (x y : HahnSeries ℚ k) (hyK : y ∈ K) (hx : x^p - x = y)
    (z : HahnSeries ℚ k) (hz : z ∈ IntermediateField.adjoin K {x}) :
    SupportClosureIn Γ z :=
  supportClosureIn_fieldAdjoin Γ K hK x (isIntegral_of_as_equation p K x y hyK hx)
    (supportClosureIn_of_as_equation p Γ hdiv x y (hK y hyK) hx) z hz

/-- The real support-closure invariant for every element of an actual finite
Artin-Schreier tower in the rational Hahn field. A step may be trivial; neither
Galois normality of the whole tower nor finite coefficient fields are assumed. -/
theorem supportClosureIn_finite_asTower (Γ : AddSubgroup ℝ)
    (hdiv : ∀ t : ℝ, t ∈ Γ → t / (p : ℝ) ∈ Γ)
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (θ : ℕ → HahnSeries ℚ k)
    (hbase : ∀ f ∈ F 0, SupportClosureIn Γ f)
    (hstep : ∀ i < N, ∃ a ∈ F i, θ i ^ p - θ i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {θ i}).toSubfield) :
    ∀ f ∈ F N, SupportClosureIn Γ f := by
  have hind : ∀ n ≤ N, ∀ f ∈ F n, SupportClosureIn Γ f := by
    intro n
    induction n with
    | zero => intro _; exact hbase
    | succ n ih =>
      intro hn f hf
      obtain ⟨a, ha, hθ, hF⟩ := hstep n (Nat.lt_of_succ_le hn)
      rw [hF] at hf
      exact supportClosureIn_asFieldAdjoin p Γ hdiv (F n)
        (ih (Nat.le_trans (Nat.le_succ n) hn)) (θ n) a ha hθ f hf
  exact hind N le_rfl

end PerfectField
end NTCThird
