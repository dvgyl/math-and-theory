import TowerFirstBlock
import HahnASRoot

/-!
# Negative flat AS generators for the forward direction

This file isolates the support estimates and the positive-root Krasner
argument used to normalize Artin--Schreier generators.  All Hahn sums below
are the actual sums constructed in `HahnASRoot`, and all field memberships
refer to the given base field.
-/

noncomputable section
set_option maxHeartbeats 1200000
attribute [local instance 2000] HahnSeries.instAlgebra

open HahnSeries IntermediateField Polynomial Set
open scoped BigOperators

namespace NTCThird

variable {k : Type*} [Field k]

/-- The actual negative AS root has negative support. -/
theorem support_asNegRoot_negative
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (a : HahnSeries ℚ k) (ha : a.support ⊆ Iio 0) :
    (asNegRoot p a ha).support ⊆ Iio 0 := by
  intro q hq
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp
    (HahnSeries.SummableFamily.support_hsum_subset
      (s := asNegFamily p a ha) hq)
  change q ∈ (invFrobeniusIterHahn p a (n + 1)).support at hn
  rw [support_invFrobeniusIterHahn] at hn
  obtain ⟨r, hr, rfl⟩ := hn
  have hp : (0 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact div_neg_of_neg_of_pos (ha hr) (pow_pos hp _)

/-- If the negative AS coefficient has finite support, every prefix of its
actual negative root bounded strictly below zero is finite. -/
theorem finite_prefix_asNegRoot
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (a : HahnSeries ℚ k) (ha : a.support ⊆ Iio 0)
    (hafinite : a.support.Finite) (q : ℚ) (hq : q < 0) :
    ((asNegRoot p a ha).support ∩ Iio q).Finite := by
  classical
  let I : Set ℕ := {n : ℕ | ∃ r ∈
    (fun s : ℚ => s / (p : ℚ) ^ n) '' a.support, r ≤ q}
  have hI : I.Finite := finite_lower_indices_inv_pow p
    (Fact.out : p.Prime).one_lt
    ⟨a.order, fun _ h => HahnSeries.order_le_of_coeff_ne_zero h⟩ hq
  have hfinite : (⋃ n ∈ hI.toFinset,
      (fun s : ℚ => s / (p : ℚ) ^ n) '' a.support).Finite := by
    apply Set.Finite.biUnion (Finset.finite_toSet _)
    intro n _
    exact hafinite.image _
  apply hfinite.subset
  rintro r ⟨hr, hrq⟩
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp
    (HahnSeries.SummableFamily.support_hsum_subset
      (s := asNegFamily p a ha) hr)
  change r ∈ (invFrobeniusIterHahn p a (n + 1)).support at hn
  rw [support_invFrobeniusIterHahn] at hn
  have hnI : n + 1 ∈ I := ⟨r, hn, hrq.le⟩
  exact Set.mem_iUnion.mpr ⟨n + 1, Set.mem_iUnion.mpr
    ⟨hI.mem_toFinset.mpr hnI, hn⟩⟩

/-- The explicit positive AS root has strictly positive support. -/
theorem support_asPosRoot_positive
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (a : HahnSeries ℚ k) (ha : a.support ⊆ Ioi 0) :
    (asPosRoot p a ha).support ⊆ Ioi 0 := by
  intro q hq
  change q ∈ (-(asPosFamily p a ha).hsum).support at hq
  rw [HahnSeries.support_neg] at hq
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp
    (HahnSeries.SummableFamily.support_hsum_subset hq)
  change q ∈ (a ^ (p ^ n)).support at hn
  have hpowpos : 1 ≤ p ^ n := Nat.one_le_pow n p (Fact.out : p.Prime).pos
  have h := support_pow_gt (fun r hr => ha hr) (p ^ n) hpowpos q hn
  simpa only [mul_zero, Set.mem_Ioi] using h

/-- A convenient exact linearized-polynomial presentation of the AS map. -/
theorem aeval_artinSchreier_linearized
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (p : ℕ) (z : F) :
    aeval z (linearized p {0, 1} (fun i : ℕ => if i = 0 then (-1 : K) else 1)) =
      z ^ p - z := by
  simp [aeval_linearized]
  ring

/-- A positive-valued AS root belongs to the given henselian base.  This
uses the normal simple AS field and actual Krasner containment against zero;
there is no separate completeness or left-finiteness premise on the root. -/
theorem positive_artinSchreier_root_mem_base
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (z : HahnSeries ℚ k) (a : K) (hz : z ^ p - z = (a : HahnSeries ℚ k))
    (hv : 0 < HahnSeries.addVal ℚ k z) : z ∈ K := by
  letI : Algebra K (HahnSeries ℚ k) := K.toAlgebra
  let b : ℕ → k := fun i => if i = 0 then -1 else 1
  have hb : ∃ i ∈ ({0, 1} : Finset ℕ), b i ≠ 0 := by
    exact ⟨0, by simp, by simp [b]⟩
  have heq : aeval z (linearized p {0, 1} b) =
      algebraMap K (HahnSeries ℚ k) a := by
    simpa only [b, aeval_artinSchreier_linearized, IntermediateField.algebraMap_apply] using hz
  have hpoly : linearized p {0, 1} b ≠ 0 :=
    linearized_ne_zero p (Fact.out : p.Prime).two_le _ b hb
  obtain ⟨hgal, _, _, _⟩ := linearized_adjoin_galois_elementary
    p {0, 1} b hb z a heq
  letI : IsGalois K K⟮z⟯ := hgal
  have hint : IsIntegral K z := isIntegral_of_linearized_equation
    p (Fact.out : p.Prime).two_le {0, 1} b hb z a heq
  have hmem : z ∈ K⟮(0 : HahnSeries ℚ k)⟯ :=
    krasner_mem_of_normal_adjoin
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K))
      (HahnSeries.addVal ℚ k) (fun _ => rfl) hK z 0 hint
      (isIntegral_zero : IsIntegral K (0 : HahnSeries ℚ k)) hgal.to_normal (by
        intro σ hσ
        rw [linearized_adjoin_aut_distance_zero p {0, 1} b hpoly z a heq
          (HahnSeries.addVal ℚ k) hahn_nonzero_constant_value σ hσ, sub_zero]
        exact hv)
  have hbot : K⟮(0 : HahnSeries ℚ k)⟯ = ⊥ :=
    IntermediateField.adjoin_simple_eq_bot_iff.mpr
      ((⊥ : IntermediateField K (HahnSeries ℚ k)).zero_mem)
  rw [hbot] at hmem
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
  rw [← hc]
  exact c.property

/-- The explicit negative root stays in every exponent subgroup closed
under division by the characteristic. -/
theorem supported_asNegRoot
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (Γ : AddSubgroup ℚ)
    (hdiv : ∀ q : ℚ, q ∈ Γ → q / (p : ℚ) ∈ Γ)
    (a : HahnSeries ℚ k) (ha : a.support ⊆ Iio 0)
    (haΓ : SupportedIn Γ a) : SupportedIn Γ (asNegRoot p a ha) := by
  have hdivpow : ∀ n : ℕ, ∀ r ∈ Γ, r / (p : ℚ) ^ n ∈ Γ := by
    intro n
    induction n with
    | zero => intro r hr; simpa using hr
    | succ n ih =>
      intro r hr
      rw [pow_succ, ← div_div]
      exact hdiv _ (ih r hr)
  intro q hq
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp
    (HahnSeries.SummableFamily.support_hsum_subset
      (s := asNegFamily p a ha) hq)
  change q ∈ (invFrobeniusIterHahn p a (n + 1)).support at hn
  rw [support_invFrobeniusIterHahn] at hn
  obtain ⟨r, hr, rfl⟩ := hn
  exact hdivpow _ r (haΓ hr)

theorem hahnRestrict_Iio_eq_truncLT (q : ℚ) (a : HahnSeries ℚ k) :
    hahnRestrict (Iio q) a = truncLT q a := by
  ext r
  simp only [hahnRestrict, truncLT, Set.indicator, Set.mem_Iio]

/-- Every AS generator over the actual allowed Hahn base differs by a base
element from a negative-support AS root whose prefixes below zero are finite.
Its support is in the actual value subgroup of the base. -/
theorem exists_negative_flat_artinSchreier_generator
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ a ∈ K, LeftFinite a)
    (x : HahnSeries ℚ k) (a : K) (hx : x ^ p - x = (a : HahnSeries ℚ k)) :
    ∃ z : HahnSeries ℚ k, ∃ b : K,
      x = z + (b : HahnSeries ℚ k) ∧
      z ^ p - z ∈ K ∧ z.support ⊆ Iio 0 ∧
      (∀ q < 0, (z.support ∩ Iio q).Finite) ∧
      SupportedIn (hahnValueGroup K.toSubfield) z := by
  classical
  letI : Algebra K (HahnSeries ℚ k) := K.toAlgebra
  letI : PerfectField K.toSubfield := ‹PerfectField K›
  let Γ := hahnValueGroup K.toSubfield
  have hmon := hahnValueGroup_single_mem_of_henselian K hK hy
  have haΓ : SupportedIn Γ (a : HahnSeries ℚ k) :=
    supportedIn_hahnValueGroup_of_leftFinite K.toSubfield hmon
      a a.property (hbase a a.property)
  let an := truncLT 0 (a : HahnSeries ℚ k)
  let ap := hahnRestrict (Ioi 0) (a : HahnSeries ℚ k)
  have han : an.support ⊆ Iio 0 := by
    intro q hq
    exact (support_truncLT 0 (a : HahnSeries ℚ k) ▸ hq).2
  have hap : ap.support ⊆ Ioi 0 := support_hahnRestrict_subset_set _ _
  have hanfin : an.support.Finite :=
    finite_support_truncLT 0 (a : HahnSeries ℚ k) (hbase a a.property)
  have hanK : an ∈ K := finite_prefix_supported_mem K.toSubfield Γ hmon
    a 0 (hbase a a.property 0) haΓ
  have ha0K : single (0 : ℚ) ((a : HahnSeries ℚ k).coeff 0) ∈ K :=
    K.algebraMap_mem _
  have hsplit : (a : HahnSeries ℚ k) =
      an + single 0 ((a : HahnSeries ℚ k).coeff 0) + ap := by
    simpa only [hahnRestrict_Iio_eq_truncLT] using hahnRestrict_tridecomp 0
      (a : HahnSeries ℚ k)
  have hapK : ap ∈ K := by
    have hrepr : ap = (a : HahnSeries ℚ k) - an -
        single 0 ((a : HahnSeries ℚ k).coeff 0) := by
      linear_combination -hsplit
    rw [hrepr]
    exact K.sub_mem (K.sub_mem a.property hanK) ha0K
  let z := asNegRoot p an han
  let u := asPosRoot p ap hap
  have hz : z ^ p - z = an := asNegRoot_equation p an han
  have hu : u ^ p - u = ap := asPosRoot_equation p ap hap
  have huK : u ∈ K := positive_artinSchreier_root_mem_base p K hK
    u ⟨ap, hapK⟩ hu (zero_lt_orderTop_of_positive_support u
      (support_asPosRoot_positive p ap hap))
  obtain ⟨c, hc⟩ := exists_artinSchreier_constant p ((a : HahnSeries ℚ k).coeff 0)
  let d : HahnSeries ℚ k := HahnSeries.C c + u
  have hdK : d ∈ K := K.add_mem (K.algebraMap_mem c) huK
  have hcH : (HahnSeries.C (Γ := ℚ) c) ^ p - HahnSeries.C c =
      single 0 ((a : HahnSeries ℚ k).coeff 0) := by
    simpa only [map_sub, map_pow, HahnSeries.C_apply] using
      congrArg (HahnSeries.C (Γ := ℚ)) hc
  have hroot : (z + d) ^ p - (z + d) = (a : HahnSeries ℚ k) := by
    dsimp only [d]
    rw [add_pow_char, add_pow_char]
    linear_combination hz + hcH + hu - hsplit
  have hdiff : (x - (z + d)) ^ p = x - (z + d) := by
    rw [sub_pow_char]
    linear_combination hx - hroot
  obtain ⟨e, he⟩ := exists_constant_of_pow_eq_self p (x - (z + d)) hdiff
  have hbK : d + HahnSeries.C e ∈ K := K.add_mem hdK (K.algebraMap_mem e)
  refine ⟨z, ⟨d + HahnSeries.C e, hbK⟩, ?_, hz ▸ hanK,
    support_asNegRoot_negative p an han, finite_prefix_asNegRoot p an han hanfin,
    supported_asNegRoot p Γ (hahnValueGroup_div p K.toSubfield) an han
      (supported_truncLT Γ (a : HahnSeries ℚ k) haΓ 0)⟩
  change x = z + (d + HahnSeries.C e)
  rw [← he]
  ring

/-- Finite prefixes below zero give actual base approximations cofinal
strictly below zero.  The truncating rational is chosen strictly between
the requested bound and zero. -/
theorem cofinal_base_approximations_of_finite_prefix
    (K : IntermediateField k (HahnSeries ℚ k))
    (Γ : AddSubgroup ℚ)
    (hmon : ∀ q ∈ Γ, ∀ c : k, single q c ∈ K.toSubfield)
    (z : HahnSeries ℚ k) (hzΓ : SupportedIn Γ z)
    (hfinite : ∀ q < 0, (z.support ∩ Iio q).Finite) :
    ∀ q : ℚ, q < 0 → ∃ a : K,
      (q : WithTop ℚ) < HahnSeries.addVal ℚ k (z - (a : HahnSeries ℚ k)) := by
  intro q hq
  obtain ⟨r, hqr, hr⟩ := exists_between hq
  have htrunc : truncLT r z ∈ K := finite_prefix_supported_mem
    K.toSubfield Γ hmon z r (hfinite r hr) hzΓ
  refine ⟨⟨truncLT r z, htrunc⟩, ?_⟩
  exact (WithTop.coe_lt_coe.mpr hqr).trans_le (le_orderTop_sub_truncLT r z)

/-- Multiplication by a constant does not enlarge a Hahn support. -/
theorem support_constant_mul_subset (c : k) (z : HahnSeries ℚ k) :
    (algebraMap k (HahnSeries ℚ k) c * z).support ⊆ z.support := by
  intro q hq
  obtain ⟨a, ha, b, hb, hab⟩ := HahnSeries.support_mul_subset hq
  have ha0 : a = 0 := HahnSeries.eq_of_mem_support_single ha
  simpa only [ha0, zero_add, ← hab] using hb

/-- A finite constant linear combination retains finite prefixes below
zero and the actual exponent subgroup. -/
theorem constant_sum_finite_prefix_supported
    {ι : Type*} (s : Finset ι) (Γ : AddSubgroup ℚ)
    (c : ι → k) (z : ι → HahnSeries ℚ k)
    (hzfinite : ∀ i ∈ s, ∀ q < 0, ((z i).support ∩ Iio q).Finite)
    (hzΓ : ∀ i ∈ s, SupportedIn Γ (z i)) :
    (∀ q < 0, ((∑ i ∈ s, algebraMap k (HahnSeries ℚ k) (c i) * z i).support ∩
      Iio q).Finite) ∧
    SupportedIn Γ (∑ i ∈ s, algebraMap k (HahnSeries ℚ k) (c i) * z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SupportedIn]
  | @insert i s hi ih =>
    obtain ⟨hfinite, hΓ⟩ := ih
      (fun j hj => hzfinite j (Finset.mem_insert_of_mem hj))
      (fun j hj => hzΓ j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi]
    constructor
    · intro q hq
      apply ((hzfinite i (Finset.mem_insert_self _ _) q hq).union (hfinite q hq)).subset
      rintro r ⟨hr, hrq⟩
      rcases HahnSeries.support_add_subset _ _ hr with h | h
      · exact Or.inl ⟨support_constant_mul_subset (c i) (z i) h, hrq⟩
      · exact Or.inr ⟨h, hrq⟩
    · exact supported_add Γ _ _
        (supported_mul Γ _ _ (supported_single Γ 0 (c i) Γ.zero_mem)
          (hzΓ i (Finset.mem_insert_self _ _))) hΓ

/-- The difference of any two conjugates of a constant linear combination
of AS generators belongs to the actual algebraically closed constant field. -/
theorem artinSchreier_sum_aut_difference_constant
    {K E : Type*} [Field K] [Field E]
    [Algebra k K] [Algebra K E] [Algebra k E] [IsScalarTower k K E]
    [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP E p]
    {ι : Type*} (s : Finset ι) (z : ι → E) (a : ι → K)
    (hz : ∀ i ∈ s, (z i) ^ p - z i = algebraMap K E (a i))
    (c : ι → k) (σ : E ≃ₐ[K] E) :
    ∃ d : k, algebraMap k E d =
      σ (∑ i ∈ s, algebraMap k E (c i) * z i) -
        ∑ i ∈ s, algebraMap k E (c i) * z i := by
  classical
  let b : ℕ → k := fun i => if i = 0 then -1 else 1
  have hb : ∃ i ∈ ({0, 1} : Finset ℕ), b i ≠ 0 :=
    ⟨0, by simp, by simp [b]⟩
  have hpoly : linearized p {0, 1} b ≠ 0 :=
    linearized_ne_zero p (Fact.out : p.Prime).two_le _ b hb
  have hdiff : ∀ i : s, ∃ d : k, algebraMap k E d = σ (z i) - z i := by
    intro i
    apply linearized_aut_difference p {0, 1} b hpoly (z i) (a i) _ σ
    simpa only [b, aeval_artinSchreier_linearized] using hz i i.property
  choose d hd using hdiff
  refine ⟨∑ i : s, c i * d i, ?_⟩
  rw [← Finset.sum_attach s (fun i => algebraMap k E (c i) * z i)]
  simp only [map_sum, map_mul, (σ.restrictScalars k).commutes]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hd i]
  rw [show σ (algebraMap k E (c i)) = algebraMap k E (c i) from
    (σ.restrictScalars k).commutes (c i)]
  ring

end NTCThird
