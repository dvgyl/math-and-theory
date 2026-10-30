import HahnASRoot
import FirstAccumulation
import HahnFinite
import HenselianKrasner

/-!
# Actual Hahn value subgroup and support induction through AS towers

The value subgroup is the image of nonzero base elements under actual Hahn
order. It is not a free parameter. Perfectness proves its p-divisibility;
left-finiteness and monomial containment prove base support containment by
well-founded induction. These facts supply the real invariant to the actual
finite AS tower theorem.
-/

noncomputable section
open HahnSeries Set
namespace NTCThird
attribute [local instance 2000] HahnSeries.instAlgebra
variable {k : Type*} [Field k]

/-- The actual rational value subgroup of a subfield of the Hahn field. -/
noncomputable def hahnValueGroup (K : Subfield (HahnSeries ℚ k)) : AddSubgroup ℚ where
  carrier := {q | ∃ a ∈ K, a ≠ 0 ∧ a.order = q}
  zero_mem' := ⟨1, K.one_mem, one_ne_zero, HahnSeries.order_one⟩
  add_mem' := by
    rintro q r ⟨a, haK, ha0, haq⟩ ⟨b, hbK, hb0, hbr⟩
    refine ⟨a*b, K.mul_mem haK hbK, mul_ne_zero ha0 hb0, ?_⟩
    rw [HahnSeries.order_mul ha0 hb0, haq, hbr]
  neg_mem' := by
    rintro q ⟨a, haK, ha0, haq⟩
    refine ⟨a⁻¹, K.inv_mem haK, inv_ne_zero ha0, ?_⟩
    have h := HahnSeries.order_mul ha0 (inv_ne_zero ha0)
    rw [mul_inv_cancel₀ ha0, HahnSeries.order_one, haq] at h
    linarith

/-- The carrier is exactly the finite actual Hahn valuation image, expressed
through orderTop. Nonzeroness is recovered from finiteness of the value. -/
theorem mem_hahnValueGroup_iff_orderTop (K : Subfield (HahnSeries ℚ k)) (q : ℚ) :
    q ∈ hahnValueGroup K ↔ ∃ a : K, (a : HahnSeries ℚ k).orderTop = (q : WithTop ℚ) := by
  constructor
  · rintro ⟨a, haK, ha0, haq⟩
    refine ⟨⟨a, haK⟩, ?_⟩
    rw [← HahnSeries.order_eq_orderTop_of_ne ha0, haq]
  · rintro ⟨a, ha⟩
    have ha0 : (a : HahnSeries ℚ k) ≠ 0 := by
      intro hz
      simp only [hz, HahnSeries.orderTop_zero, WithTop.top_ne_coe] at ha
    refine ⟨(a : HahnSeries ℚ k), a.property, ha0, ?_⟩
    exact WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne ha0).trans ha)

/-- The same identification stated directly using the library's Hahn
additive valuation. -/
theorem mem_hahnValueGroup_iff_addVal (K : Subfield (HahnSeries ℚ k)) (q : ℚ) :
    q ∈ hahnValueGroup K ↔
      ∃ a : K, HahnSeries.addVal ℚ k (a : HahnSeries ℚ k) = (q : WithTop ℚ) := by
  simpa only [HahnSeries.addVal_apply] using mem_hahnValueGroup_iff_orderTop K q

/-- The actual value subgroup of a perfect characteristic-p subfield is
closed under division by p. -/
theorem hahnValueGroup_div (p : ℕ) [Fact p.Prime] [CharP k p]
    (K : Subfield (HahnSeries ℚ k)) [PerfectField K] :
    ∀ q : ℚ, q ∈ hahnValueGroup K → q / (p : ℚ) ∈ hahnValueGroup K := by
  letI : CharP K p := K.subtype.charP Subtype.val_injective p
  intro q hq
  obtain ⟨a, haK, ha0, haq⟩ := hq
  obtain ⟨b, hb⟩ := surjective_frobenius K p (⟨a, haK⟩ : K)
  have hb' : (b : HahnSeries ℚ k)^p = a := by
    exact congrArg (fun z : K => (z : HahnSeries ℚ k)) hb
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hb0 : (b : HahnSeries ℚ k) ≠ 0 := by
    intro hz
    rw [hz, zero_pow hp0] at hb'
    exact ha0 hb'.symm
  refine ⟨(b : HahnSeries ℚ k), b.property, hb0, ?_⟩
  have horder := congrArg HahnSeries.order hb'
  rw [HahnSeries.order_pow, nsmul_eq_mul, haq] at horder
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  apply (eq_div_iff hpQ).mpr
  simpa only [mul_comm] using horder

/-- Every exponent of a left-finite base series is an actual base value,
provided the corresponding value-group monomials belong to the base.
The induction removes an actual finite prefix from the original element. -/
theorem supportedIn_hahnValueGroup_of_leftFinite
    (K : Subfield (HahnSeries ℚ k))
    (hmon : ∀ q ∈ hahnValueGroup K, ∀ c : k, single q c ∈ K)
    (f : HahnSeries ℚ k) (hfK : f ∈ K) (hf : LeftFinite f) :
    SupportedIn (hahnValueGroup K) f := by
  intro q hq
  apply f.isWF_support.induction hq
  intro r hr ih
  have htruncΓ : SupportedIn (hahnValueGroup K) (truncLT r f) := by
    intro s hs
    rw [support_truncLT] at hs
    exact ih s hs.1 hs.2
  have htruncK : truncLT r f ∈ K :=
    finite_supported_mem K (hahnValueGroup K) hmon (truncLT r f)
      (finite_support_truncLT r f hf) htruncΓ
  have hremcoeff : (f - truncLT r f).coeff r ≠ 0 := by
    simpa only [coeff_sub, coeff_truncLT, lt_self_iff_false, if_false, sub_zero] using hr
  have hrem0 : f - truncLT r f ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hremcoeff
  have hremval : (f - truncLT r f).orderTop = (r : WithTop ℚ) :=
    le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hremcoeff)
      (le_orderTop_sub_truncLT r f)
  exact (mem_hahnValueGroup_iff_orderTop K r).mpr
    ⟨⟨f - truncLT r f, K.sub_mem hfK htruncK⟩, hremval⟩

/-- The actual base field supplies the real support-closure invariant from
left-finiteness and value-group monomial containment. -/
theorem supportClosureIn_hahnValueGroup_of_leftFinite
    (K : Subfield (HahnSeries ℚ k))
    (hmon : ∀ q ∈ hahnValueGroup K, ∀ c : k, single q c ∈ K)
    (f : HahnSeries ℚ k) (hfK : f ∈ K) (hf : LeftFinite f) :
    SupportClosureIn (rationalSubgroupReal (hahnValueGroup K)) f :=
  supportClosureIn_rational_of_leftFinite (hahnValueGroup K) f hf
    (supportedIn_hahnValueGroup_of_leftFinite K hmon f hfK hf)

/-- Actual finite AS towers over the base have real support closure in the
real image of the base's actual value subgroup. The monomial hypothesis is the
separate conclusion of the henselian monomial lemma. -/
theorem supportClosureIn_actual_asTower (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k))
    [PerfectField (F 0)] (θ : ℕ → HahnSeries ℚ k)
    (hbase : ∀ f ∈ F 0, LeftFinite f)
    (hmon : ∀ q ∈ hahnValueGroup (F 0), ∀ c : k, single q c ∈ F 0)
    (hstep : ∀ i < N, ∃ a ∈ F i, θ i ^ p - θ i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {θ i}).toSubfield) :
    ∀ f ∈ F N, SupportClosureIn (rationalSubgroupReal (hahnValueGroup (F 0))) f := by
  apply supportClosureIn_finite_asTower p (rationalSubgroupReal (hahnValueGroup (F 0)))
    (rationalSubgroupReal_div (hahnValueGroup (F 0)) p (hahnValueGroup_div p (F 0))) N F θ
  · intro f hf
    exact supportClosureIn_hahnValueGroup_of_leftFinite (F 0) hmon f hf (hbase f hf)
  · exact hstep

/-- Literal rational support containment for every element of the actual
finite AS tower, with the actual base value subgroup. -/
theorem supportedIn_actual_asTower (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k))
    [PerfectField (F 0)] (θ : ℕ → HahnSeries ℚ k)
    (hbase : ∀ f ∈ F 0, LeftFinite f)
    (hmon : ∀ q ∈ hahnValueGroup (F 0), ∀ c : k, single q c ∈ F 0)
    (hstep : ∀ i < N, ∃ a ∈ F i, θ i ^ p - θ i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {θ i}).toSubfield) :
    ∀ f ∈ F N, SupportedIn (hahnValueGroup (F 0)) f := by
  intro f hf
  exact support_subset_of_supportClosureIn_rational _ f
    (supportClosureIn_actual_asTower p N F θ hbase hmon hstep f hf)


/-- The henselian monomial theorem supplies every coefficient monomial at
an element of the actual base value group. No monomial premise is retained. -/
theorem hahnValueGroup_single_mem_of_henselian [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K) ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K) :
    ∀ q ∈ hahnValueGroup K.toSubfield, ∀ c : k, single q c ∈ K.toSubfield := by
  intro q hq c
  obtain ⟨a, ha⟩ := (mem_hahnValueGroup_iff_orderTop K.toSubfield q).mp hq
  let a' : K := ⟨(a : HahnSeries ℚ k), a.property⟩
  have ha' : (a' : HahnSeries ℚ k).orderTop = (q : WithTop ℚ) := ha
  exact hahn_single_mem_of_value K hK hy a' q ha' c

/-- Every left-finite element of the actual perfect henselian base has real
support closure in the real image of its actual value subgroup. -/
theorem supportClosureIn_henselian_base [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K) ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (f : HahnSeries ℚ k) (hfK : f ∈ K) (hf : LeftFinite f) :
    SupportClosureIn (rationalSubgroupReal (hahnValueGroup K.toSubfield)) f :=
  supportClosureIn_hahnValueGroup_of_leftFinite K.toSubfield
    (hahnValueGroup_single_mem_of_henselian K hK hy) f hfK hf

/-- Full actual tower support assembly from the perfect henselian base data.
The value subgroup, monomials, base invariant, and p-divisibility are all
derived; they are not hypotheses of this endpoint. -/
theorem supportClosureIn_henselian_asTower (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K) ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ f ∈ K, LeftFinite f)
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (θ : ℕ → HahnSeries ℚ k)
    (hF0 : F 0 = K.toSubfield)
    (hstep : ∀ i < N, ∃ a ∈ F i, θ i ^ p - θ i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {θ i}).toSubfield) :
    ∀ f ∈ F N, SupportClosureIn (rationalSubgroupReal (hahnValueGroup K.toSubfield)) f := by
  letI : PerfectField K.toSubfield := ‹PerfectField K›
  haveI : PerfectField (F 0) := hF0.symm ▸ (inferInstance : PerfectField K.toSubfield)
  have hbase' : ∀ f ∈ F 0, LeftFinite f := by rw [hF0]; exact hbase
  have hmon : ∀ q ∈ hahnValueGroup (F 0), ∀ c : k, single q c ∈ F 0 := by
    rw [hF0]
    exact hahnValueGroup_single_mem_of_henselian K hK hy
  have h := supportClosureIn_actual_asTower p N F θ hbase' hmon hstep
  simpa only [hF0] using h

/-- The same fully assembled tower statement with literal rational support
containment in the actual base value group. -/
theorem supportedIn_henselian_asTower (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K) ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ f ∈ K, LeftFinite f)
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (θ : ℕ → HahnSeries ℚ k)
    (hF0 : F 0 = K.toSubfield)
    (hstep : ∀ i < N, ∃ a ∈ F i, θ i ^ p - θ i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {θ i}).toSubfield) :
    ∀ f ∈ F N, SupportedIn (hahnValueGroup K.toSubfield) f := by
  intro f hf
  exact support_subset_of_supportClosureIn_rational _ f
    (supportClosureIn_henselian_asTower p K hK hy hbase N F θ hF0 hstep f hf)

/-- Every non-left-finite element of the actual tower has a rational first
infinite prefix at an actual base value, with all strict lower prefixes finite. -/
theorem first_cut_henselian_asTower (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K) ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ f ∈ K, LeftFinite f)
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (θ : ℕ → HahnSeries ℚ k)
    (hF0 : F 0 = K.toSubfield)
    (hstep : ∀ i < N, ∃ a ∈ F i, θ i ^ p - θ i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {θ i}).toSubfield)
    (f : HahnSeries ℚ k) (hf : f ∈ F N) (hnlf : ¬ LeftFinite f) :
    ∃ δ : ℚ, δ ∈ hahnValueGroup K.toSubfield ∧ (f.support ∩ Iio δ).Infinite ∧
      ∀ r < δ, (f.support ∩ Iio r).Finite :=
  exists_first_rational_support_cut (hahnValueGroup K.toSubfield) f hnlf
    (supportClosureIn_henselian_asTower p K hK hy hbase N F θ hF0 hstep f hf)


/-- Integrality passes from an AS right-hand side to its root, by composing
monic equations. This is an actual polynomial argument and needs no assumed
algebraicity of the root. -/
theorem isIntegral_of_as_eq_of_integral (p : ℕ) [Fact p.Prime]
    (K : Subfield (HahnSeries ℚ k)) (x y : HahnSeries ℚ k)
    (hy : IsIntegral K y) (hx : x^p - x = y) : IsIntegral K x := by
  let P : Polynomial K := Polynomial.X^p - Polynomial.X
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hmonic : P.Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    exact_mod_cast hp1
  have hdegree : P.natDegree = p := by
    dsimp [P]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow (R := K) p
    · simpa only [Polynomial.natDegree_X, Polynomial.natDegree_X_pow] using hp1
  apply IsIntegral.of_aeval_monic hmonic
    (hdegree ▸ (Fact.out : p.Prime).ne_zero)
  simpa only [P, map_sub, map_pow, Polynomial.aeval_X, hx] using hy

/-- Every element of an actual finite AS tower is integral over its actual
base subfield. The proof inducts inside the relative algebraic closure and
uses the literal field-adjoin condition for each step. -/
theorem isIntegral_actual_asTower (p : ℕ) [Fact p.Prime]
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (θ : ℕ → HahnSeries ℚ k)
    (hstep : ∀ i < N, ∃ a ∈ F i, θ i ^ p - θ i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {θ i}).toSubfield) :
    ∀ f ∈ F N, IsIntegral (F 0) f := by
  let A : Subfield (HahnSeries ℚ k) :=
    (algebraicClosure (F 0) (HahnSeries ℚ k)).toSubfield
  have hind : ∀ n ≤ N, F n ≤ A := by
    intro n
    induction n with
    | zero =>
      intro _ f hf
      change IsIntegral (F 0) f
      exact isIntegral_algebraMap (R := F 0) (A := HahnSeries ℚ k) (x := ⟨f, hf⟩)
    | succ n ih =>
      intro hn
      have hnA : F n ≤ A := ih (Nat.le_trans (Nat.le_succ n) hn)
      obtain ⟨a, ha, hθ, hF⟩ := hstep n (Nat.lt_of_succ_le hn)
      have hθA : θ n ∈ A :=
        isIntegral_of_as_eq_of_integral p (F 0) (θ n) a (hnA ha) hθ
      rw [hF]
      apply IntermediateField.adjoin_le_subfield
      · rintro f ⟨a, rfl⟩
        exact hnA a.property
      · intro f hf
        have hfx : f = θ n := Set.mem_singleton_iff.mp hf
        simpa only [hfx] using hθA
  exact hind N le_rfl

/-- Complete first-cut endpoint from the original actual base/tower data and
nonmembership in the base. Both integrality and non-left-finiteness are
proved internally; neither is an extra hypothesis. -/
theorem first_cut_henselian_asTower_of_not_mem (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ f ∈ K, LeftFinite f)
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (θ : ℕ → HahnSeries ℚ k)
    (hF0 : F 0 = K.toSubfield)
    (hstep : ∀ i < N, ∃ a ∈ F i, θ i ^ p - θ i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {θ i}).toSubfield)
    (f : HahnSeries ℚ k) (hf : f ∈ F N) (hfnot : f ∉ K) :
    ∃ δ : ℚ, δ ∈ hahnValueGroup K.toSubfield ∧ (f.support ∩ Iio δ).Infinite ∧
      ∀ r < δ, (f.support ∩ Iio r).Finite := by
  letI : PerfectField K.toSubfield := ‹PerfectField K›
  have hint : IsIntegral K.toSubfield f := by
    have h := isIntegral_actual_asTower p N F θ hstep f hf
    exact hF0 ▸ h
  have hsupp : SupportedIn (hahnValueGroup K.toSubfield) f :=
    supportedIn_henselian_asTower p K hK hy hbase N F θ hF0 hstep f hf
  have hnotLF : ¬ LeftFinite f := by
    intro hLF
    apply hfnot
    apply hahn_leftFinite_algebraic_mem K.toSubfield hK f hint hLF
    intro q hq
    exact hahnValueGroup_single_mem_of_henselian K hK hy q (hsupp hq) (f.coeff q)
  exact first_cut_henselian_asTower p K hK hy hbase N F θ hF0 hstep f hf hnotLF

end NTCThird
