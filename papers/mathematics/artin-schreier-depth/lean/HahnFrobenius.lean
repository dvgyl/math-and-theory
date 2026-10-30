/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan

Adapted for the NT-C project on 2026-10-30: Lean 4.19 compatibility,
namespace changes and truncation/iteration additions. Source pinned at
https://github.com/YijunYuan/TrustworthyKedlaya/blob/f97be4372713e25a21603dec26706d8bb0cd9d24/TrustworthyKedlaya/Kedlaya/Frobenius.lean
-/
import Mathlib
import HahnSupport

/-!
# Frobenius acts coefficientwise on Hahn series over `ℚ`

Over a commutative ring `R` of characteristic `p`, the `p`-th power map on
`HahnSeries ℚ R` is computed coefficientwise together with the support scaling
`i ↦ p·i`:

- `NTCThird.coeff_pow_char`: `(x ^ p).coeff g = (x.coeff (g / p)) ^ p`.

No multinomial or orbit-counting combinatorics is needed: for a *fixed* exponent `g`,
split `x = x_{< g/p} + x_{g/p} + x_{> g/p}` (restriction of the coefficient function).
The `p`-th power is additive in characteristic `p` (`add_pow_char`), the `p`-th powers
of the outer parts are supported strictly below resp. above `g`, and the middle single
term contributes exactly `(x.coeff (g/p))^p`.

From the formula we obtain the inverse Frobenius:

- `NTCThird.invFrobeniusHahn`: for `R` perfect, the preimage of `x` under the
  `p`-th power map, with `invFrobeniusHahn_pow : invFrobeniusHahn p x ^ p = x`;
- `NTCThird.pow_char_bijective`: the Frobenius of `HahnSeries ℚ R` is
  bijective when `R` is perfect.

The restriction-of-support construction `NTCThird.hahnRestrict` is shared
infrastructure (it also implements truncation of Hahn series at a point).
-/

noncomputable section

namespace NTCThird

open HahnSeries

variable {R : Type*}

/-! ### Restricting the coefficient function to a set of exponents -/

/-- Restriction of a Hahn series to a set `S` of exponents: keep the coefficients with
exponent in `S`, zero out the rest. -/
noncomputable def hahnRestrict [Zero R] (S : Set ℚ) (x : HahnSeries ℚ R) :
    HahnSeries ℚ R where
  coeff := S.indicator x.coeff
  isPWO_support' := x.isPWO_support'.mono fun g hg => by
    rw [Function.mem_support] at hg ⊢
    intro h0
    apply hg
    by_cases hgS : g ∈ S
    · rw [Set.indicator_of_mem hgS, h0]
    · exact Set.indicator_of_not_mem hgS _

theorem coeff_hahnRestrict_of_mem [Zero R] {S : Set ℚ} (x : HahnSeries ℚ R) {g : ℚ}
    (h : g ∈ S) : (hahnRestrict S x).coeff g = x.coeff g :=
  Set.indicator_of_mem h _

theorem coeff_hahnRestrict_of_notMem [Zero R] {S : Set ℚ} (x : HahnSeries ℚ R) {g : ℚ}
    (h : g ∉ S) : (hahnRestrict S x).coeff g = 0 :=
  Set.indicator_of_not_mem h _

theorem support_hahnRestrict_subset [Zero R] (S : Set ℚ) (x : HahnSeries ℚ R) :
    (hahnRestrict S x).support ⊆ x.support := fun g hg => by
  rw [HahnSeries.mem_support] at hg ⊢
  intro h0
  apply hg
  by_cases hgS : g ∈ S
  · rw [coeff_hahnRestrict_of_mem x hgS, h0]
  · exact coeff_hahnRestrict_of_notMem x hgS

theorem support_hahnRestrict_subset_set [Zero R] (S : Set ℚ) (x : HahnSeries ℚ R) :
    (hahnRestrict S x).support ⊆ S := fun g hg => by
  rw [HahnSeries.mem_support] at hg
  by_contra h
  exact hg (coeff_hahnRestrict_of_notMem x h)

/-- Three-way decomposition of a Hahn series at a point `θ` of the exponent line:
the part strictly below `θ`, the single term at `θ`, and the part strictly above `θ`. -/
theorem hahnRestrict_tridecomp [AddCommMonoid R] (θ : ℚ) (x : HahnSeries ℚ R) :
    x = hahnRestrict (Set.Iio θ) x + single θ (x.coeff θ)
        + hahnRestrict (Set.Ioi θ) x := by
  ext g
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add]
  rcases lt_trichotomy g θ with h | rfl | h
  · rw [coeff_hahnRestrict_of_mem x (Set.mem_Iio.mpr h),
      coeff_single_of_ne h.ne,
      coeff_hahnRestrict_of_notMem x (by simp [Set.mem_Ioi, not_lt_of_gt h]),
      add_zero, add_zero]
  · rw [coeff_hahnRestrict_of_notMem x (by simp),
      coeff_hahnRestrict_of_notMem x (by simp),
      coeff_single_same, zero_add, add_zero]
  · rw [coeff_hahnRestrict_of_mem x (Set.mem_Ioi.mpr h),
      coeff_single_of_ne h.ne',
      coeff_hahnRestrict_of_notMem x (by simp [Set.mem_Iio, not_lt_of_gt h]),
      zero_add, zero_add]

/-! ### Support bounds for powers -/

/-- If every exponent of `y` is `< θ`, every exponent of `y ^ n` (`n ≥ 1`) is `< n·θ`. -/
theorem support_pow_lt [CommRing R] {y : HahnSeries ℚ R} {θ : ℚ}
    (hy : ∀ i ∈ y.support, i < θ) :
    ∀ n : ℕ, 1 ≤ n → ∀ g ∈ (y ^ n).support, g < n * θ := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    intro _ g hg
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_one] at hg
      simpa using hy g hg
    · rw [pow_succ] at hg
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := support_mul_subset_add_support hg
      have h1 := ih hn g₁ hg₁
      have h2 := hy g₂ hg₂
      push_cast
      linarith

/-- If every exponent of `y` is `> θ`, every exponent of `y ^ n` (`n ≥ 1`) is `> n·θ`. -/
theorem support_pow_gt [CommRing R] {y : HahnSeries ℚ R} {θ : ℚ}
    (hy : ∀ i ∈ y.support, θ < i) :
    ∀ n : ℕ, 1 ≤ n → ∀ g ∈ (y ^ n).support, n * θ < g := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    intro _ g hg
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_one] at hg
      simpa using hy g hg
    · rw [pow_succ] at hg
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := support_mul_subset_add_support hg
      have h1 := ih hn g₁ hg₁
      have h2 := hy g₂ hg₂
      push_cast
      linarith

/-- Powers of single terms. -/
theorem hahn_single_pow [CommRing R] (a : ℚ) (r : R) :
    ∀ n : ℕ, (single a r : HahnSeries ℚ R) ^ n = single (n * a) (r ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, single_mul_single, pow_succ]
    push_cast
    ring_nf

/-! ### The coefficientwise formula for the Frobenius -/

variable [CommRing R]

instance instCharPHahnSeries (p : ℕ) [CharP R p] : CharP (HahnSeries ℚ R) p :=
  charP_of_injective_ringHom (f := HahnSeries.C (Γ := ℚ) (R := R))
    (fun _ _ h => by simpa using congrArg (fun z => z.coeff 0) h) p

variable {p : ℕ} [hp : Fact p.Prime] [CharP R p]

/-- **The Frobenius of `HahnSeries ℚ R` acts coefficientwise**, with the support
scaling `i ↦ p·i`:  `(x ^ p).coeff g = (x.coeff (g / p)) ^ p` for every `g`.
(When `g/p` is not in the support both sides are `0`.) -/
theorem coeff_pow_char (x : HahnSeries ℚ R) (g : ℚ) :
    (x ^ p).coeff g = x.coeff (g / p) ^ p := by
  have : ExpChar (HahnSeries ℚ R) p := .prime hp.out
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  set θ : ℚ := g / p with hθ
  have hgθ : (p : ℚ) * θ = g := mul_div_cancel₀ g hp0.ne'
  -- Split `x` at the exponent `θ` and take `p`-th powers additively.
  rw [show x ^ p = (hahnRestrict (Set.Iio θ) x + single θ (x.coeff θ)
      + hahnRestrict (Set.Ioi θ) x) ^ p from by rw [← hahnRestrict_tridecomp],
    add_pow_char, add_pow_char, HahnSeries.coeff_add, HahnSeries.coeff_add]
  -- The part below `θ` contributes nothing at `g = p·θ`.
  have hlo : ((hahnRestrict (Set.Iio θ) x) ^ p).coeff g = 0 := by
    by_contra h0
    have := support_pow_lt
      (fun i hi => support_hahnRestrict_subset_set _ x hi) p hp1 g h0
    rw [hgθ] at this
    exact lt_irrefl g this
  -- The part above `θ` contributes nothing at `g = p·θ`.
  have hhi : ((hahnRestrict (Set.Ioi θ) x) ^ p).coeff g = 0 := by
    by_contra h0
    have := support_pow_gt
      (fun i hi => support_hahnRestrict_subset_set _ x hi) p hp1 g h0
    rw [hgθ] at this
    exact lt_irrefl g this
  -- The single term at `θ` contributes exactly `(x.coeff θ)^p`.
  rw [hlo, hhi, hahn_single_pow, hgθ, zero_add, add_zero, coeff_single_same]

/-! ### The inverse Frobenius -/

section Perfect

variable [PerfectRing R p]

/-- The inverse Frobenius of a Hahn series over a perfect ring: coefficientwise inverse
Frobenius together with the support scaling `i ↦ i / p`. -/
noncomputable def invFrobeniusHahn (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p]
    (x : HahnSeries ℚ R) : HahnSeries ℚ R where
  coeff g := (frobeniusEquiv R p).symm (x.coeff (p * g))
  isPWO_support' := by
    have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (Fact.out : p.Prime).pos
    have hmono : Monotone fun i : ℚ => i / p := fun i j hij =>
      div_le_div_of_nonneg_right hij hp0.le
    refine (x.isPWO_support'.image_of_monotone hmono).mono ?_
    intro g hg
    rw [Function.mem_support] at hg
    refine ⟨p * g, ?_, by field_simp⟩
    rw [Function.mem_support]
    intro h0
    rw [h0, map_zero] at hg
    exact hg rfl

@[simp] theorem coeff_invFrobeniusHahn (x : HahnSeries ℚ R) (g : ℚ) :
    (invFrobeniusHahn p x).coeff g = (frobeniusEquiv R p).symm (x.coeff (p * g)) := rfl

/-- The inverse Frobenius is a right inverse of the `p`-th power map. -/
theorem invFrobeniusHahn_pow (x : HahnSeries ℚ R) : invFrobeniusHahn p x ^ p = x := by
  ext g
  rw [coeff_pow_char, coeff_invFrobeniusHahn]
  have hp0 : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
  rw [mul_div_cancel₀ g hp0]
  exact frobeniusEquiv_symm_pow_p R p _

/-- **The Frobenius `x ↦ x^p` of `HahnSeries ℚ R` is bijective** for `R` perfect. -/
theorem pow_char_bijective :
    Function.Bijective fun x : HahnSeries ℚ R => x ^ p := by
  constructor
  · intro x y hxy
    ext g
    have hcoeff := congrArg (fun z : HahnSeries ℚ R => z.coeff (p * g)) hxy
    simp only [coeff_pow_char] at hcoeff
    have hp0 : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
    rw [mul_div_cancel_left₀ g hp0] at hcoeff
    exact (frobeniusEquiv R p).injective
      (by simpa [frobeniusEquiv_apply, frobenius_def] using hcoeff)
  · intro x
    exact ⟨invFrobeniusHahn p x, invFrobeniusHahn_pow x⟩

end Perfect

/-- Iterated Frobenius coefficient formula over an arbitrary characteristic-p ring. -/
theorem coeff_pow_char_pow (p : ℕ) [Fact p.Prime] [CharP R p]
    (x : HahnSeries ℚ R) (n : ℕ) (q : ℚ) :
    (x ^ (p ^ n)).coeff q = (x.coeff (q / (p : ℚ) ^ n)) ^ (p ^ n) := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
    calc (x ^ p ^ (n + 1)).coeff q
        = ((x ^ p ^ n) ^ p).coeff q := by rw [← pow_mul, ← pow_succ]
      _ = ((x ^ p ^ n).coeff (q / p)) ^ p := coeff_pow_char _ q
      _ = ((x.coeff ((q / p) / (p : ℚ) ^ n)) ^ p ^ n) ^ p := by rw [ih (q / p)]
      _ = (x.coeff (q / (p : ℚ) ^ (n + 1))) ^ p ^ (n + 1) := by
          rw [div_div, ← pow_succ', ← pow_mul, ← pow_succ]

section Truncation
variable {k : Type*} [Field k]

/-- Frobenius powers commute with genuine Hahn truncation after scaling the cutoff. -/
theorem truncLT_pow_char_pow (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : HahnSeries ℚ k) (n : ℕ) (δ : ℚ) :
    truncLT ((p : ℚ) ^ n * δ) (x ^ (p ^ n)) = (truncLT δ x) ^ (p ^ n) := by
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpn : 0 < (p : ℚ) ^ n := pow_pos hp0 n
  have hn0 : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  ext q
  rw [coeff_truncLT, coeff_pow_char_pow p, coeff_pow_char_pow p, coeff_truncLT]
  have hiff : q / (p : ℚ) ^ n < δ ↔ q < (p : ℚ) ^ n * δ := by
    rw [div_lt_iff₀ hpn, mul_comm δ]
  by_cases h : q < (p : ℚ) ^ n * δ
  · simp [h, hiff.mpr h]
  · simp [h, hiff.not.mpr h, zero_pow hn0]

/-- Exact support scaling for an iterated Frobenius power over a field. -/
theorem support_pow_char_pow (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : HahnSeries ℚ k) (n : ℕ) :
    (x ^ (p ^ n)).support = (fun q : ℚ => (p : ℚ) ^ n * q) '' x.support := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hn0 : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  ext q
  rw [HahnSeries.mem_support, coeff_pow_char_pow p]
  constructor
  · intro h
    refine ⟨q / (p : ℚ) ^ n, ?_, mul_div_cancel₀ q (pow_ne_zero n hp0)⟩
    rw [HahnSeries.mem_support]
    intro hz
    rw [hz, zero_pow hn0] at h
    exact h rfl
  · rintro ⟨r, hr, rfl⟩
    rw [mul_div_cancel_left₀ _ (pow_ne_zero n hp0)]
    exact pow_ne_zero _ ((HahnSeries.mem_support _ _).mp hr)

/-- Exact finite-prefix transport for a Frobenius power. -/
theorem support_pow_char_pow_prefix (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : HahnSeries ℚ k) (n : ℕ) (c : ℚ) :
    (x ^ (p ^ n)).support ∩ Set.Iio c =
      (fun q : ℚ => (p : ℚ) ^ n * q) ''
        (x.support ∩ Set.Iio (c / (p : ℚ) ^ n)) := by
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpn : 0 < (p : ℚ) ^ n := pow_pos hp0 n
  rw [support_pow_char_pow p]
  ext q
  constructor
  · rintro ⟨⟨r, hr, rfl⟩, hrc⟩
    refine ⟨r, ⟨hr, ?_⟩, rfl⟩
    exact (lt_div_iff₀ hpn).mpr (by simpa [mul_comm] using hrc)
  · rintro ⟨r, ⟨hr, hrc⟩, rfl⟩
    refine ⟨⟨r, hr, rfl⟩, ?_⟩
    have h := (lt_div_iff₀ hpn).mp hrc
    simpa [mul_comm] using h

/-- Every strict lower prefix remains finite after a Frobenius power. -/
theorem finite_strict_prefix_pow_char_pow (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : HahnSeries ℚ k) (n : ℕ) (δ : ℚ)
    (hfinite : ∀ r < δ, (x.support ∩ Set.Iio r).Finite) :
    ∀ c < (p : ℚ) ^ n * δ, ((x ^ (p ^ n)).support ∩ Set.Iio c).Finite := by
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (Fact.out : p.Prime).pos
  intro c hc
  rw [support_pow_char_pow_prefix p]
  apply Set.Finite.image
  apply hfinite
  exact (div_lt_iff₀ (pow_pos hp0 n)).mpr (by simpa [mul_comm] using hc)


end Truncation

end NTCThird
