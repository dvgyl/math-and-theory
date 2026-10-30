import HahnFinite
import AdditiveGalois

/-!
# Minimum-face extraction for an actual Hahn first block

This adapts the Ore/truncation construction of Kedlaya, On the algebraicity of
generalized power series (2017), Lemma 9.3. The finite-prefix product lemma gives
the finite remainder directly. No novelty is claimed for that construction.
-/

noncomputable section
attribute [local instance 2000] HahnSeries.instAlgebra
open scoped BigOperators Pointwise Polynomial IntermediateField
open HahnSeries Polynomial
namespace NTCThird
variable {k : Type*} [Field k]

def oreFaceTerm (p : ℕ) (θ : HahnSeries ℚ k) (δ c : ℚ)
    (a : HahnSeries ℚ k) (i : ℕ) : HahnSeries ℚ k :=
  if a.order + (p : ℚ) ^ i * δ = c then
    single a.order (a.coeff a.order) * (truncLT δ θ) ^ (p ^ i)
  else 0

def oreFaceCoeff (p : ℕ) (δ c : ℚ) (a : HahnSeries ℚ k) (i : ℕ) : k :=
  if a.order + (p : ℚ) ^ i * δ = c then a.coeff a.order else 0

/-- Each truncated Ore term differs from its retained leading-face term by a
finite-support series in K. All hypotheses concern actual Hahn support. -/
theorem ore_face_residual_mem (p : ℕ) [Fact p.Prime] [CharP k p]
    (K : Subfield (HahnSeries ℚ k)) (Γ : AddSubgroup ℚ)
    (hmon : ∀ q ∈ Γ, ∀ d : k, single q d ∈ K)
    (θ a : HahnSeries ℚ k) (δ c : ℚ) (i : ℕ)
    (hθ : SupportedIn Γ θ)
    (hfinite : ∀ r < δ, (θ.support ∩ Set.Iio r).Finite)
    (ha : LeftFinite a) (haΓ : SupportedIn Γ a) (ha0 : a ≠ 0)
    (hc : c ≤ a.order + (p : ℚ) ^ i * δ) :
    truncLT c (a * θ ^ (p ^ i)) - oreFaceTerm p θ δ c a i ∈ K := by
  let α := truncLT δ θ
  let g := α ^ (p ^ i)
  let B := (p : ℚ) ^ i * δ
  have hα : SupportedIn Γ α := supported_truncLT Γ θ hθ δ
  have hgΓ : SupportedIn Γ g := supported_pow Γ α hα (p ^ i)
  have hαfinite : ∀ r < δ, (α.support ∩ Set.Iio r).Finite := by
    intro r hr
    apply (hfinite r hr).subset
    rintro q ⟨hq, hqr⟩
    rw [show α = truncLT δ θ from rfl, support_truncLT] at hq
    exact ⟨hq.1, hqr⟩
  have hgfinite : ∀ r < B, (g.support ∩ Set.Iio r).Finite :=
    finite_strict_prefix_pow_char_pow p α i δ hαfinite
  have hreplace : truncLT c (a * θ ^ (p ^ i)) = truncLT c (a * g) := by
    rw [truncLT_mul_right a (θ ^ (p ^ i)) B c hc]
    rw [show B = (p : ℚ) ^ i * δ from rfl, truncLT_pow_char_pow p]
  rw [hreplace]
  unfold oreFaceTerm
  split_ifs with hface
  · let l := single a.order (a.coeff a.order)
    let t := a - l
    have haorderΓ : a.order ∈ Γ := haΓ (coeff_order_ne_zero ha0)
    have hlΓ : SupportedIn Γ l := supported_single Γ a.order _ haorderΓ
    have htΓ : SupportedIn Γ t := supported_sub Γ a l haΓ hlΓ
    have htfinite : LeftFinite t := leftFinite_sub a l ha (leftFinite_single _ _)
    have hglt : ∀ q ∈ g.support, q < B := by
      intro q hq
      have h := support_pow_lt (y := α) (θ := δ) (by
        intro r hr
        rw [show α = truncLT δ θ from rfl, support_truncLT] at hr
        exact hr.2) (p ^ i) (Nat.one_le_iff_ne_zero.mpr
          (pow_ne_zero i (Fact.out : p.Prime).ne_zero)) q hq
      simpa only [B, Nat.cast_pow] using h
    have hltrunc : truncLT c (l * g) = l * g := by
      apply truncLT_eq_self_of_support_lt
      intro q hq
      obtain ⟨r, hr, s, hs, hrs⟩ := support_mul_subset_add_support hq
      have hr' : r = a.order := eq_of_mem_support_single hr
      have hs' : s < B := hglt s hs
      change r + s = q at hrs
      dsimp [B] at hs'
      linarith
    have hR : truncLT c (t * g) ∈ K := by
      by_cases ht0 : t = 0
      · simpa only [ht0, zero_mul, truncLT_zero] using K.zero_mem
      · apply finite_prefix_supported_mem K Γ hmon
        · apply finite_prefix_mul t g B c htfinite hgfinite
          have hlt : a.order < t.order := order_lt_sub_leading_order a ht0
          dsimp [B]
          linarith
        · exact supported_mul Γ t g htΓ hgΓ
    have hdecomp : a * g = l * g + t * g := by dsimp [t]; ring
    rw [hdecomp, truncLT_add, hltrunc]
    change l * g + truncLT c (t * g) - l * g ∈ K
    simpa only [add_sub_cancel_left] using hR
  · simp only [sub_zero]
    apply finite_prefix_supported_mem K Γ hmon
    · apply finite_prefix_mul a g B c ha hgfinite
      exact lt_of_le_of_ne hc (Ne.symm hface)
    · exact supported_mul Γ a g haΓ hgΓ

/-- Normalizing a retained leading-face term turns its coefficient into a
constant. This is an equality of actual Hahn products and Frobenius powers. -/
theorem normalize_oreFaceTerm (p : ℕ) (θ : HahnSeries ℚ k) (δ c : ℚ)
    (a : HahnSeries ℚ k) (i : ℕ) :
    single (-c) (1 : k) * oreFaceTerm p θ δ c a i =
      algebraMap k (HahnSeries ℚ k) (oreFaceCoeff p δ c a i) *
        (single (-δ) (1 : k) * truncLT δ θ) ^ (p ^ i) := by
  unfold oreFaceTerm oreFaceCoeff
  split_ifs with hface
  · have hmap (d : k) : algebraMap k (HahnSeries ℚ k) d = single 0 d := by
      rfl
    rw [hmap]
    change single (-c) (1 : k) *
        (single a.order (a.coeff a.order) * (truncLT δ θ) ^ (p ^ i)) =
      single 0 (a.coeff a.order) *
        (single (-δ) (1 : k) * truncLT δ θ) ^ (p ^ i)
    rw [mul_pow, hahn_single_pow]
    simp only [one_pow]
    rw [← mul_assoc, single_mul_single, one_mul,
      ← mul_assoc, single_mul_single, mul_one, zero_add]
    have he : -c + a.order = (p ^ i : ℕ) * (-δ) := by
      push_cast
      nlinarith
    rw [he]
  · simp

/-- The actual coefficient-field extraction from a nontrivial Ore relation.
The output coefficients belong to k, not merely to K. -/
theorem ore_first_block_equation (p : ℕ) [Fact p.Prime] [CharP k p]
    (K : Subfield (HahnSeries ℚ k)) (Γ : AddSubgroup ℚ)
    (hmon : ∀ q ∈ Γ, ∀ d : k, single q d ∈ K)
    (θ : HahnSeries ℚ k) (δ : ℚ) (hδ : δ ∈ Γ)
    (hθ : SupportedIn Γ θ)
    (hfinite : ∀ r < δ, (θ.support ∩ Set.Iio r).Finite)
    (s : Finset ℕ) (hs : s.Nonempty) (a : ℕ → HahnSeries ℚ k)
    (ha0 : ∀ i ∈ s, a i ≠ 0)
    (haf : ∀ i ∈ s, LeftFinite (a i))
    (haΓ : ∀ i ∈ s, SupportedIn Γ (a i))
    (hrel : ∑ i ∈ s, a i * θ ^ (p ^ i) = 0) :
    ∃ b : ℕ → k, (∃ i ∈ s, b i ≠ 0) ∧
      aeval (single (-δ) (1 : k) * truncLT δ θ) (linearized p s b) ∈ K := by
  classical
  obtain ⟨j, hj, hmin⟩ := s.exists_min_image
    (fun i => (a i).order + (p : ℚ) ^ i * δ) hs
  let c := (a j).order + (p : ℚ) ^ j * δ
  let b : ℕ → k := fun i => oreFaceCoeff p δ c (a i) i
  have hcΓ : c ∈ Γ := by
    apply Γ.add_mem (haΓ j hj (coeff_order_ne_zero (ha0 j hj)))
    have h := Γ.nsmul_mem hδ (p ^ j)
    simpa only [nsmul_eq_mul, Nat.cast_pow] using h
  have hres : ∑ i ∈ s,
      (truncLT c (a i * θ ^ (p ^ i)) - oreFaceTerm p θ δ c (a i) i) ∈ K := by
    apply K.sum_mem
    intro i hi
    exact ore_face_residual_mem p K Γ hmon θ (a i) δ c i hθ hfinite
      (haf i hi) (haΓ i hi) (ha0 i hi) (hmin i hi)
  have htruncsum : ∑ i ∈ s, truncLT c (a i * θ ^ (p ^ i)) = 0 := by
    rw [← truncLT_sum, hrel, truncLT_zero]
  rw [Finset.sum_sub_distrib, htruncsum, zero_sub] at hres
  have hfaceSum : ∑ i ∈ s, oreFaceTerm p θ δ c (a i) i ∈ K := by
    simpa only [neg_neg] using K.neg_mem hres
  refine ⟨b, ⟨j, hj, ?_⟩, ?_⟩
  · change oreFaceCoeff p δ c (a j) j ≠ 0
    simpa only [oreFaceCoeff, c, if_pos rfl] using coeff_order_ne_zero (ha0 j hj)
  · have hmul := K.mul_mem (hmon (-c) (Γ.neg_mem hcΓ) 1) hfaceSum
    rw [Finset.mul_sum] at hmul
    simp_rw [normalize_oreFaceTerm] at hmul
    simpa only [aeval_linearized, b] using hmul

end NTCThird
