import HahnClosureDepth

/-!
# The forward implication and the equivalence in the source's ambient field

Nart--Novacoski, arXiv:2503.18827v2, prove (Theorem 3.15) that a compositum of
Artin--Schreier extensions has depth one, and conjecture the converse
(Conjecture 4.1). `HahnClosureDepth.lean` proves the converse with depth one
stated as minimum Okutsu length one in their ambient field, the algebraic
closure of `K` inside the Hahn field. This file proves the forward implication
in the same formulation, `hahnClosure_okutsu_minimum_of_asCompositum`, and the
resulting equivalence for literal towers, `okutsu_minimum_one_iff_asCompositum`.

The forward proof follows the source: each Artin--Schreier generator is moved by
an element of `K` to the explicit negative root of a finite negative constant,
using henselian splitting of nonnegative constants (via Krasner's lemma); a
`k`-linear combination of these roots with coefficients avoiding finitely many
linear relations is a primitive element whose conjugates differ from it by
nonzero constants; Krasner's lemma with a constant (residue) shift shows that no
element of smaller degree comes within valuation zero; and partial
inverse-Frobenius sums in `K` approximate it at every negative level.

The identification of minimum Okutsu length with Mac Lane--Vaquié depth is
Theorem 1.3 of the source and is not formalized here.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
attribute [local instance 2000] HahnSeries.instAlgebra
attribute [local instance 3000] Algebra.id

open HahnSeries IntermediateField Set Polynomial

namespace NTCThird

-- From the Fwd1 development stage.
section Approx
variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] [PerfectRing k p]

theorem invFrobeniusIterHahn_pow (y : HahnSeries ℚ k) (n : ℕ) :
    (invFrobeniusIterHahn p y n)^(p^n) = y := by
  induction n with
  | zero =>
    ext q
    simp
  | succ n ih =>
    rw [pow_succ', pow_mul, invFrobeniusIterHahn_succ_pow, ih]

theorem invFrobeniusIterHahn_mem (K : Subfield (HahnSeries ℚ k)) [PerfectField K]
    (y : HahnSeries ℚ k) (hy : y ∈ K) (n : ℕ) : invFrobeniusIterHahn p y n ∈ K := by
  letI : CharP K p := K.subtype.charP Subtype.val_injective p
  induction n with
  | zero =>
    have h0 : invFrobeniusIterHahn p y 0 = y := by
      ext q
      simp
    rwa [h0]
  | succ n ih =>
    obtain ⟨b, hb⟩ := surjective_frobenius K p (⟨_, ih⟩ : K)
    have hb' : (b : HahnSeries ℚ k)^p = invFrobeniusIterHahn p y n :=
      congrArg (fun z : K => (z : HahnSeries ℚ k)) hb
    have heq : (b : HahnSeries ℚ k) = invFrobeniusIterHahn p y (n+1) := by
      apply frobenius_inj (HahnSeries ℚ k) p
      change (b : HahnSeries ℚ k)^p = (invFrobeniusIterHahn p y (n+1))^p
      rw [hb', invFrobeniusIterHahn_succ_pow]
    exact heq ▸ b.property

/-- The coefficients of the negative Artin--Schreier root below a negative
level are already given by finitely many inverse-Frobenius terms. -/
theorem asNegRoot_coeff_eq_partial (y : HahnSeries ℚ k) (hneg : y.support ⊆ Iio 0)
    (N : ℕ) (q : ℚ) (hq : q < 0)
    (hbound : ∀ r ∈ y.support, q * (p : ℚ)^(N+1) < r) :
    (asNegRoot p y hneg).coeff q =
      (∑ n ∈ Finset.range N, invFrobeniusIterHahn p y (n+1)).coeff q := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  change (∑ᶠ n, (invFrobeniusIterHahn p y (n+1)).coeff q) = _
  rw [HahnSeries.coeff_sum]
  apply finsum_eq_sum_of_support_subset
  intro n hn
  rw [Function.mem_support] at hn
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hN
  push_neg at hN
  apply hn
  rw [coeff_invFrobeniusIterHahn]
  have hz : y.coeff (q * (p : ℚ)^(n+1)) = 0 := by
    by_contra hne
    have hmem : q * (p : ℚ)^(n+1) ∈ y.support := hne
    have hlt := hbound _ hmem
    have hpow : (p : ℚ)^(N+1) ≤ (p : ℚ)^(n+1) :=
      pow_le_pow_right₀ hp1 (by omega)
    have : q * (p : ℚ)^(n+1) ≤ q * (p : ℚ)^(N+1) :=
      mul_le_mul_of_nonpos_left hpow hq.le
    linarith
  rw [hz, invFrobenius_iterate_zero]

end Approx

-- From the Fwd2 development stage.
section Normality
variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] [IsAlgClosed k]

/-- Two Hahn roots of the same Artin--Schreier equation differ by a constant. -/
theorem as_root_sub_const (z w : HahnSeries ℚ k) (h : z^p - z = w^p - w) :
    ∃ c : k, w - z = HahnSeries.C c := by
  apply exists_constant_of_pow_eq_self p
  rw [sub_pow_char]
  linear_combination -h

/-- Coefficients of the linearized polynomial `X^p - X`. -/
def asCoeff : ℕ → k := fun i => if i = 0 then -1 else 1

omit hp [CharP k p] [IsAlgClosed k] in
theorem aeval_linearized_asCoeff {E : Type*} [Field E] [Algebra k E] (z : E) :
    aeval z (linearized p ({0, 1} : Finset ℕ) (asCoeff (k := k))) = z^p - z := by
  rw [aeval_linearized, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  simp [asCoeff, sub_eq_add_neg, add_comm]

variable (K : IntermediateField k (HahnSeries ℚ k))

/-- The Artin--Schreier polynomial `X^p - X - a` over `K`. -/
def asPoly (a : K) : K[X] :=
  (linearized p ({0, 1} : Finset ℕ) (asCoeff (k := k))).map (algebraMap k K) - C a

omit hp [CharP k p] [IsAlgClosed k] in
theorem aeval_asPoly (a : K) (z : HahnSeries ℚ k) :
    aeval z (asPoly p K a) = z^p - z - algebraMap K (HahnSeries ℚ k) a := by
  rw [asPoly, map_sub, aeval_map_algebraMap, aeval_C, aeval_linearized_asCoeff]

omit [CharP k p] [IsAlgClosed k] in
theorem asPoly_ne_zero (a : K) : asPoly p K a ≠ 0 := by
  intro h
  have := congrArg (fun f : K[X] => f.coeff p) h
  simp only [asPoly, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_map, linearized,
    Polynomial.finset_sum_coeff, Polynomial.coeff_monomial] at this
  rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)] at this
  have hp1 : p ≠ 0 := hp.out.ne_zero
  have hp2 : (1 : ℕ) ≠ p := hp.out.one_lt.ne
  simp [asCoeff, hp1, hp2, Polynomial.coeff_monomial, Polynomial.coeff_C] at this

theorem asPoly_splits (a : K) (z : HahnSeries ℚ k)
    (hz : z^p - z = algebraMap K (HahnSeries ℚ k) a) :
    (asPoly p K a).Splits (algebraMap K (HahnSeries ℚ k)) := by
  apply linearized_splits_of_root p ({0, 1} : Finset ℕ) (asCoeff (k := k)) z a
  rw [aeval_linearized_asCoeff, hz]

/-- A field generated over `K` by finitely many Artin--Schreier roots is normal
over `K`: it is the splitting field of the product of their polynomials. -/
theorem normal_of_as_generators (s : Finset (HahnSeries ℚ k))
    (ha : ∀ z ∈ s, ∃ a : K, z^p - z = algebraMap K (HahnSeries ℚ k) a)
    (M : IntermediateField K (HahnSeries ℚ k))
    (hM : IntermediateField.adjoin K (s : Set (HahnSeries ℚ k)) = M) :
    Normal K M := by
  classical
  choose! a hza using ha
  let f : K[X] := ∏ z ∈ s, asPoly p K (a z)
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.mpr fun z _ => asPoly_ne_zero p K (a z)
  have hsplit : f.Splits (algebraMap K (HahnSeries ℚ k)) :=
    Polynomial.splits_prod _ fun z hz => asPoly_splits p K (a z) z (hza z hz)
  have hN : IntermediateField.adjoin K (f.rootSet (HahnSeries ℚ k)) = M := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro r hr
      rw [Polynomial.mem_rootSet_of_ne hf0] at hr
      change aeval r (∏ z ∈ s, asPoly p K (a z)) = 0 at hr
      rw [map_prod, Finset.prod_eq_zero_iff] at hr
      obtain ⟨z, hz, hr⟩ := hr
      rw [aeval_asPoly, sub_eq_zero] at hr
      obtain ⟨c, hc⟩ := as_root_sub_const p z r (by rw [hr, hza z hz])
      have hzM : z ∈ M := hM ▸ IntermediateField.subset_adjoin K _ (by exact_mod_cast hz)
      have hcM : HahnSeries.C c ∈ M := by
        have : (HahnSeries.C c : HahnSeries ℚ k) = algebraMap K (HahnSeries ℚ k)
            (algebraMap k K c) := rfl
        rw [this]
        exact M.algebraMap_mem _
      have hr' : r = z + HahnSeries.C c := by rw [← hc]; ring
      rw [hr']
      exact M.add_mem hzM hcM
    · rw [← hM, IntermediateField.adjoin_le_iff]
      intro z hz
      apply IntermediateField.subset_adjoin
      rw [Polynomial.mem_rootSet_of_ne hf0]
      change aeval z (∏ z ∈ s, asPoly p K (a z)) = 0
      rw [map_prod, Finset.prod_eq_zero_iff]
      refine ⟨z, by exact_mod_cast hz, ?_⟩
      rw [aeval_asPoly, hza z (by exact_mod_cast hz), sub_self]
  haveI := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hnorm : Normal K (IntermediateField.adjoin K (f.rootSet (HahnSeries ℚ k))) :=
    Normal.of_isSplittingField f
  rw [hN] at hnorm
  exact hnorm

end Normality

-- From the Fwd3 development stage.
/-- Over an infinite field, finitely many nonzero linear forms have a common
nonvanishing point. -/
theorem exists_coeffs_avoiding {k ι G : Type*} [Field k] [Infinite k] [Fintype ι]
    [DecidableEq ι] [Fintype G] (d : G → ι → k) (hd : ∀ g, d g ≠ 0) :
    ∃ c : ι → k, ∀ g, ∑ i, c i * d g i ≠ 0 := by
  classical
  let L : G → MvPolynomial ι k := fun g => ∑ i, MvPolynomial.C (d g i) * MvPolynomial.X i
  have hevalL : ∀ g (c : ι → k), MvPolynomial.eval c (L g) = ∑ i, c i * d g i := by
    intro g c
    simp [L, MvPolynomial.eval_sum, mul_comm]
  have hL : ∀ g, L g ≠ 0 := by
    intro g hzero
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hd g)
    have h := hevalL g (Pi.single i0 1)
    rw [hzero, map_zero] at h
    have : ∑ i, (Pi.single i0 (1 : k) : ι → k) i * d g i = d g i0 := by
      rw [Finset.sum_eq_single i0]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
    rw [this] at h
    exact hi0 h.symm
  let P : MvPolynomial ι k := ∏ g, L g
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun g _ => hL g
  by_contra hall
  push_neg at hall
  apply hP
  apply MvPolynomial.funext
  intro c
  obtain ⟨g, hg⟩ := hall c
  rw [map_zero]
  change MvPolynomial.eval c (∏ g, L g) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ g) ((hevalL g c).trans hg)

section Split
variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] [IsAlgClosed k]

theorem asPosRoot_orderTop_pos (y : HahnSeries ℚ k) (hpos : y.support ⊆ Ioi 0) :
    0 < (asPosRoot p y hpos).orderTop := by
  apply lt_orderTop_of_coeff_zero_le
  intro q hq
  by_contra hne
  have hmem : (q : ℝ) ∈ realSupport (asPosRoot p y hpos) := ⟨q, hne, rfl⟩
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (realSupport_asPosRoot_subset p y hpos hmem)
  obtain ⟨x, ⟨r, hr, rfl⟩, hx⟩ := Set.mem_smul_set.mp hn
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hpos hr
  have hpn : (0 : ℝ) < (p : ℝ)^n := pow_pos (by exact_mod_cast hp.out.pos) n
  have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast hq
  simp only [smul_eq_mul] at hx
  nlinarith

/-- Henselian splitting of nonnegative Artin--Schreier constants: an element of
`K` with nonnegative support is `e^p - e` for some `e` in `K`. -/
theorem exists_as_preimage_of_nonneg
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (a : K) (ha : (a : HahnSeries ℚ k).support ⊆ Ici 0) :
    ∃ e : K, (e : HahnSeries ℚ k)^p - e = a := by
  classical
  obtain ⟨c₀, hc₀⟩ := exists_artinSchreier_constant p ((a : HahnSeries ℚ k).coeff 0)
  set a₀ := (a : HahnSeries ℚ k).coeff 0
  let aplus : HahnSeries ℚ k := (a : HahnSeries ℚ k) - HahnSeries.C a₀
  have hplus : aplus.support ⊆ Ioi 0 := by
    intro q hq
    rw [HahnSeries.mem_support] at hq
    by_contra hle
    rw [Set.mem_Ioi, not_lt] at hle
    rcases hle.lt_or_eq with hlt | rfl
    · apply hq
      simp only [aplus, HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single,
        if_neg hlt.ne]
      rw [sub_zero]
      by_contra hne
      exact (not_le_of_gt hlt) (ha hne)
    · apply hq
      simp [aplus, a₀]
  let e : HahnSeries ℚ k := HahnSeries.C c₀ + asPosRoot p aplus hplus
  have he : e^p - e = (a : HahnSeries ℚ k) := by
    have hadd : e^p = (HahnSeries.C c₀)^p + (asPosRoot p aplus hplus)^p :=
      add_pow_char (HahnSeries.C c₀ : HahnSeries ℚ k) (asPosRoot p aplus hplus) p
    have hroot := asPosRoot_equation p aplus hplus
    have hconst : (HahnSeries.C c₀ : HahnSeries ℚ k)^p - HahnSeries.C c₀ = HahnSeries.C a₀ := by
      rw [← map_pow, ← map_sub, hc₀]
    simp only [e, aplus] at hroot ⊢
    rw [hadd]
    linear_combination hroot + hconst
  have haH : algebraMap K (HahnSeries ℚ k) a = (a : HahnSeries ℚ k) := rfl
  have hroot : aeval e (asPoly p K a) = 0 := by
    rw [aeval_asPoly, haH, he, sub_self]
  have hint : IsIntegral K e :=
    (show IsAlgebraic K e from ⟨asPoly p K a, asPoly_ne_zero p K a, hroot⟩).isIntegral
  have hnormal : Normal K K⟮e⟯ :=
    normal_of_as_generators p K {e}
      (by
        intro z hz
        rw [Finset.mem_singleton] at hz
        exact ⟨a, by rw [hz, he, haH]⟩)
      K⟮e⟯ (by rw [Finset.coe_singleton])
  let β : HahnSeries ℚ k := algebraMap K (HahnSeries ℚ k) (algebraMap k K c₀)
  have hβ : β = HahnSeries.C c₀ := rfl
  have hmem : e ∈ K⟮β⟯ := by
    apply krasner_mem_of_normal_adjoin
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)) (HahnSeries.addVal ℚ k)
      (fun _ => rfl) hK e β hint isIntegral_algebraMap hnormal
    intro σ hσ
    set w : HahnSeries ℚ k := (σ (AdjoinSimple.gen K e) : HahnSeries ℚ k)
    have hgen : (AdjoinSimple.gen K e)^p - AdjoinSimple.gen K e =
        algebraMap K K⟮e⟯ a := by
      apply Subtype.ext
      simp only [AdjoinSimple.coe_gen, AddSubgroupClass.coe_sub,
        SubmonoidClass.coe_pow, IntermediateField.algebraMap_apply]
      exact he
    have hw : w^p - w = (a : HahnSeries ℚ k) := by
      have h := congrArg σ hgen
      rw [map_sub, map_pow, AlgEquiv.commutes] at h
      have h' := congrArg (fun x : K⟮e⟯ => (x : HahnSeries ℚ k)) h
      simpa only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow,
        IntermediateField.algebraMap_apply] using h'
    obtain ⟨c, hc⟩ := as_root_sub_const p e w (by rw [he, hw])
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hσ
      apply Subtype.ext
      have : w = e := by
        rw [map_zero] at hc
        exact sub_eq_zero.mp hc
      rw [AdjoinSimple.coe_gen]
      exact this
    have hleft : HahnSeries.addVal ℚ k (e - w) = 0 := by
      have : e - w = -(algebraMap k (HahnSeries ℚ k) c) := by
        rw [← neg_sub, hc]
        rfl
      rw [this, AddValuation.map_neg, hahn_nonzero_constant_value c hc0]
    have hright : 0 < HahnSeries.addVal ℚ k (e - β) := by
      have : e - β = asPosRoot p aplus hplus := by
        rw [hβ]
        simp only [e]
        ring
      rw [this, HahnSeries.addVal_apply]
      exact asPosRoot_orderTop_pos p aplus hplus
    rw [hleft]
    exact hright
  have hβbot : K⟮β⟯ = ⊥ := by
    rw [IntermediateField.adjoin_simple_eq_bot_iff]
    exact IntermediateField.algebraMap_mem _ _
  rw [hβbot, IntermediateField.mem_bot] at hmem
  obtain ⟨e', he'⟩ := hmem
  refine ⟨e', ?_⟩
  have : (e' : HahnSeries ℚ k) = e := he'
  rw [this, he]

end Split

-- From the Fwd4 development stage.
section Normalize
variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] [IsAlgClosed k]

/-- Every Artin--Schreier root over `K` becomes, after subtracting an element
of `K`, the explicit negative root of a finite negative constant plus a
constant. -/
theorem as_normalize
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ a ∈ K, LeftFinite a)
    (z : HahnSeries ℚ k) (a : K) (hz : z^p - z = (a : HahnSeries ℚ k)) :
    ∃ (e aneg : K) (hneg : (aneg : HahnSeries ℚ k).support ⊆ Iio 0) (j : k),
      (z - (e : HahnSeries ℚ k))^p - (z - (e : HahnSeries ℚ k)) = (aneg : HahnSeries ℚ k) ∧
      z - (e : HahnSeries ℚ k) = asNegRoot p (aneg : HahnSeries ℚ k) hneg + HahnSeries.C j := by
  have hmonG := hahnValueGroup_single_mem_of_henselian K hK hy
  have hsupp := supportedIn_hahnValueGroup_of_leftFinite K.toSubfield hmonG
    (a : HahnSeries ℚ k) a.property (hbase _ a.property)
  have hmon : ∀ q ∈ (a : HahnSeries ℚ k).support,
      single q ((a : HahnSeries ℚ k).coeff q) ∈ K.toSubfield :=
    fun q hq => hmonG q (hsupp hq) _
  have hnegK : truncLT 0 (a : HahnSeries ℚ k) ∈ K.toSubfield :=
    truncLT_mem_subfield K.toSubfield 0 _ (hbase _ a.property 0) hmon
  let aneg : K := ⟨truncLT 0 (a : HahnSeries ℚ k), hnegK⟩
  have hneg : (aneg : HahnSeries ℚ k).support ⊆ Iio 0 := by
    intro q hq
    change q ∈ (truncLT 0 (a : HahnSeries ℚ k)).support at hq
    rw [support_truncLT] at hq
    exact hq.2
  let apos : K := a - aneg
  have hpos : (apos : HahnSeries ℚ k).support ⊆ Ici 0 := by
    intro q hq
    by_contra hge
    have hq0 : q < 0 := lt_of_not_ge hge
    apply (HahnSeries.mem_support _ _).mp hq
    change ((a : HahnSeries ℚ k) - truncLT 0 (a : HahnSeries ℚ k)).coeff q = 0
    rw [HahnSeries.coeff_sub, coeff_truncLT, if_pos hq0, sub_self]
  obtain ⟨e, he⟩ := exists_as_preimage_of_nonneg p K hK apos hpos
  have hz' : (z - (e : HahnSeries ℚ k))^p - (z - (e : HahnSeries ℚ k)) =
      (aneg : HahnSeries ℚ k) := by
    have hsub : (z - (e : HahnSeries ℚ k))^p = z^p - (e : HahnSeries ℚ k)^p :=
      sub_pow_char z (e : HahnSeries ℚ k)
    have hapos : (apos : HahnSeries ℚ k) = (a : HahnSeries ℚ k) - aneg := rfl
    rw [hsub]
    linear_combination hz - he - hapos
  obtain ⟨j, hj⟩ := as_root_sub_const p (asNegRoot p (aneg : HahnSeries ℚ k) hneg)
    (z - (e : HahnSeries ℚ k))
    (by rw [asNegRoot_equation, hz'])
  exact ⟨e, aneg, hneg, j, hz', by rw [← hj]; ring⟩

/-- Base approximations of a constant-coefficient combination of negative
roots reach every negative level. -/
theorem exists_base_approx_of_negRoots
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    {ι : Type*} [Fintype ι] (c : ι → k) (aneg : ι → K)
    (hneg : ∀ i, (aneg i : HahnSeries ℚ k).support ⊆ Iio 0) (j : ι → k)
    (q : ℚ) (hq : q < 0) :
    ∃ a : K, ((q / 2 : ℚ) : WithTop ℚ) ≤ HahnSeries.addVal ℚ k
      ((∑ i, HahnSeries.C (c i) * (asNegRoot p (aneg i : HahnSeries ℚ k) (hneg i) +
        HahnSeries.C (j i))) - (a : HahnSeries ℚ k)) := by
  classical
  obtain ⟨B, hBdef⟩ : ∃ B : ℚ, B = ∑ i, |(aneg i : HahnSeries ℚ k).order| + 1 := ⟨_, rfl⟩
  have hB : ∀ i, -B ≤ (aneg i : HahnSeries ℚ k).order := by
    intro i
    have h1 : |(aneg i : HahnSeries ℚ k).order| ≤ ∑ i, |(aneg i : HahnSeries ℚ k).order| :=
      Finset.single_le_sum (f := fun i => |(aneg i : HahnSeries ℚ k).order|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le ((aneg i : HahnSeries ℚ k).order)
    rw [hBdef]
    linarith
  have hBpos : 0 < B := by
    have : 0 ≤ ∑ i, |(aneg i : HahnSeries ℚ k).order| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    rw [hBdef]
    linarith
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 * B / (-q)) hp1
  have hpN : (p : ℚ)^N ≤ (p : ℚ)^(N+1) := pow_le_pow_right₀ hp1.le (Nat.le_succ N)
  have hkey : (q / 2) * (p : ℚ)^(N+1) < -B := by
    have hq' : 0 < -q := by linarith
    have h1 : 2 * B < (p : ℚ)^N * (-q) := by
      rwa [div_lt_iff₀ hq'] at hN
    have h2 : (q / 2) * (p : ℚ)^(N+1) ≤ (q / 2) * (p : ℚ)^N :=
      mul_le_mul_of_nonpos_left hpN (by linarith)
    have h3 : (q / 2) * (p : ℚ)^N = -((p : ℚ)^N * (-q)) / 2 := by ring
    linarith
  let psum (i : ι) : HahnSeries ℚ k :=
    ∑ n ∈ Finset.range N, invFrobeniusIterHahn p (aneg i : HahnSeries ℚ k) (n+1)
  haveI : PerfectField K.toSubfield := (inferInstance : PerfectField K)
  have hpartial : ∀ i, psum i ∈ K := by
    intro i
    apply K.toSubfield.sum_mem
    intro n _
    exact invFrobeniusIterHahn_mem p K.toSubfield _ (aneg i).property _
  have hCK : ∀ c : k, (HahnSeries.C c : HahnSeries ℚ k) ∈ K := fun c =>
    K.algebraMap_mem c
  let a : K := ⟨∑ i, HahnSeries.C (c i) * (psum i + HahnSeries.C (j i)),
    K.toSubfield.sum_mem fun i _ =>
      K.mul_mem (hCK _) (K.add_mem (hpartial i) (hCK _))⟩
  refine ⟨a, ?_⟩
  rw [HahnSeries.addVal_apply]
  apply le_orderTop_of_coeff_zero_lt
  intro r hr
  have hr0 : r < 0 := by linarith
  change ((∑ i, HahnSeries.C (c i) * (asNegRoot p (aneg i : HahnSeries ℚ k) (hneg i) +
      HahnSeries.C (j i))) - ∑ i, HahnSeries.C (c i) * (psum i + HahnSeries.C (j i))).coeff r = 0
  rw [← Finset.sum_sub_distrib, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [← mul_sub, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  have hcoeff : (asNegRoot p (aneg i : HahnSeries ℚ k) (hneg i) + HahnSeries.C (j i) -
      (psum i + HahnSeries.C (j i))).coeff r = 0 := by
    have hbound : ∀ s ∈ (aneg i : HahnSeries ℚ k).support, r * (p : ℚ)^(N+1) < s := by
      intro s hs
      have hs' : (aneg i : HahnSeries ℚ k).order ≤ s :=
        HahnSeries.order_le_of_coeff_ne_zero hs
      have hpos : (0 : ℚ) < (p : ℚ)^(N+1) := pow_pos (by linarith) _
      have : r * (p : ℚ)^(N+1) < (q / 2) * (p : ℚ)^(N+1) :=
        mul_lt_mul_of_pos_right hr hpos
      linarith [hB i]
    have h := asNegRoot_coeff_eq_partial p (aneg i : HahnSeries ℚ k) (hneg i) N r hr0 hbound
    rw [show asNegRoot p (aneg i : HahnSeries ℚ k) (hneg i) + HahnSeries.C (j i) -
        (psum i + HahnSeries.C (j i)) =
        asNegRoot p (aneg i : HahnSeries ℚ k) (hneg i) - psum i by ring,
      HahnSeries.coeff_sub, h, sub_self]
  rw [hcoeff, mul_zero]

end Normalize

-- From the Fwd5 development stage.
section Galois
variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- An automorphism fixing a generating set is the identity. -/
theorem algEquiv_eq_one_of_fixes {S : Set M} (hS : IntermediateField.adjoin K S = ⊤)
    (σ : M ≃ₐ[K] M) (hσ : ∀ x ∈ S, σ x = x) : σ = 1 := by
  ext x
  have hx : x ∈ IntermediateField.adjoin K S := hS ▸ IntermediateField.mem_top
  change σ x = x
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact hσ x hx
  | algebraMap a => exact σ.commutes a
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

/-- In a finite Galois extension, an element fixed only by the identity is primitive. -/
theorem adjoin_eq_top_of_fixed_only_by_one [FiniteDimensional K M] [IsGalois K M] (θ : M)
    (hθ : ∀ σ : M ≃ₐ[K] M, σ θ = θ → σ = 1) : K⟮θ⟯ = ⊤ := by
  have hfix : IntermediateField.fixingSubgroup K⟮θ⟯ = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    apply hθ
    exact (IntermediateField.mem_fixingSubgroup_iff K⟮θ⟯ σ).mp hσ θ
      (IntermediateField.mem_adjoin_simple_self K θ)
  rw [← IsGalois.fixedField_fixingSubgroup K⟮θ⟯, hfix, eq_top_iff]
  intro x _
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  rw [Subgroup.mem_bot] at hσ
  rw [hσ]
  rfl

end Galois

section Lower
variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] [IsAlgClosed k]

omit hp [CharP k p] [IsAlgClosed k] in
theorem elementDegree_add_const (K : IntermediateField k (HahnSeries ℚ k))
    (b : HahnSeries ℚ k) (a : K) :
    elementDegree K (b + algebraMap K (HahnSeries ℚ k) a) = elementDegree K b := by
  unfold elementDegree
  rw [minpoly.add_algebraMap, Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]

omit [IsAlgClosed k] in
/-- If every nontrivial conjugate of `θ` differs from it by a nonzero constant,
then no algebraic element of smaller degree is within valuation zero of `θ`.
The boundary value zero is handled by a constant (residue) shift. -/
theorem addVal_sub_neg_of_lower_degree
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (θ : HahnSeries ℚ k) (hθint : IsIntegral K θ) (hnormal : Normal K K⟮θ⟯)
    (hconst : ∀ σ : K⟮θ⟯ ≃ₐ[K] K⟮θ⟯, σ (AdjoinSimple.gen K θ) ≠ AdjoinSimple.gen K θ →
      ∃ c : k, c ≠ 0 ∧ (σ (AdjoinSimple.gen K θ) : HahnSeries ℚ k) - θ = HahnSeries.C c)
    (b : HahnSeries ℚ k) (hb : IsIntegral K b)
    (hdeg : elementDegree K b < elementDegree K θ) :
    HahnSeries.addVal ℚ k (θ - b) < 0 := by
  by_contra hge
  push_neg at hge
  set c₁ : k := (θ - b).coeff 0
  let b' : HahnSeries ℚ k := b + algebraMap K (HahnSeries ℚ k) (algebraMap k K c₁)
  have hb'C : algebraMap K (HahnSeries ℚ k) (algebraMap k K c₁) = HahnSeries.C c₁ := rfl
  have hpos : 0 < HahnSeries.addVal ℚ k (θ - b') := by
    rw [HahnSeries.addVal_apply]
    apply lt_orderTop_of_coeff_zero_le
    intro q hq
    have hb'def : θ - b' = (θ - b) - HahnSeries.C c₁ := by
      simp only [b', hb'C]; ring
    rw [hb'def, HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single]
    rcases hq.lt_or_eq with hlt | rfl
    · rw [if_neg hlt.ne]
      rw [HahnSeries.addVal_apply] at hge
      rw [HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
        (WithTop.coe_lt_coe.mpr hlt) hge), sub_zero]
    · rw [if_pos rfl, sub_self]
  have hb'int : IsIntegral K b' := hb.add isIntegral_algebraMap
  have hmem : θ ∈ K⟮b'⟯ := by
    apply krasner_mem_of_normal_adjoin
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)) (HahnSeries.addVal ℚ k)
      (fun _ => rfl) hK θ b' hθint hb'int hnormal
    intro σ hσ
    obtain ⟨c, hc0, hc⟩ := hconst σ hσ
    have hval : HahnSeries.addVal ℚ k (θ - (σ (AdjoinSimple.gen K θ) : HahnSeries ℚ k)) = 0 := by
      have : θ - (σ (AdjoinSimple.gen K θ) : HahnSeries ℚ k) =
          -(algebraMap k (HahnSeries ℚ k) c) := by
        rw [← neg_sub, hc]; rfl
      rw [this, AddValuation.map_neg, hahn_nonzero_constant_value c hc0]
    rw [hval]
    exact hpos
  letI := IntermediateField.adjoin.finiteDimensional hb'int
  have hle : elementDegree K θ ≤ elementDegree K b' := by
    rw [← finrank_adjoin_eq_elementDegree K b' hb'int]
    have h := elementDegree_algHom (K⟮b'⟯).val ⟨θ, hmem⟩
    change elementDegree K θ = _ at h
    rw [h]
    exact minpoly.natDegree_le _
  have hb'deg : elementDegree K b' = elementDegree K b :=
    elementDegree_add_const K b (algebraMap k K c₁)
  omega

end Lower

section Forward
variable {k : Type*} [Field k]

/-- The forward implication of Conjecture 4.1 (Theorem 3.15 of the source),
with the source's ambient field and the Hahn valuation: a nontrivial finite
Artin--Schreier compositum has minimum Okutsu length one over all primitive
generators. -/
theorem hahnClosure_okutsu_minimum_of_asCompositum
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ a ∈ K, LeftFinite a)
    (M : IntermediateField K (HahnSeries ℚ k)) [FiniteDimensional K M]
    (hAS : artinSchreierCompositum K M p = ⊤) (hbot : M ≠ ⊥)
    (hMA : M ≤ hahnClosure K) :
    IsLeast (realizedOkutsuLengths K (hahnClosureValuation K)
      (IntermediateField.inclusion hMA).fieldRange) 1 := by
  classical
  -- Finitely many Artin--Schreier generators.
  obtain ⟨θ0, hθ0⟩ := Field.exists_primitive_element K M
  obtain ⟨s, hsgen, hsAS⟩ :=
    exists_finite_nontrivial_as_generators_of_compositum_eq_top p hAS θ0 hθ0
  have hsH : ∀ z : s, ∃ a : K, ((z : M) : HahnSeries ℚ k)^p - ((z : M) : HahnSeries ℚ k) =
      (a : HahnSeries ℚ k) := by
    intro z
    obtain ⟨_, a, ha⟩ := hsAS z z.property
    exact ⟨a, congrArg (fun x : M => (x : HahnSeries ℚ k)) ha⟩
  -- Normalize every generator.
  have hnorm : ∀ z : s, ∃ (e aneg : K) (hneg : (aneg : HahnSeries ℚ k).support ⊆ Iio 0) (j : k),
      (((z : M) : HahnSeries ℚ k) - (e : HahnSeries ℚ k))^p -
          (((z : M) : HahnSeries ℚ k) - (e : HahnSeries ℚ k)) = (aneg : HahnSeries ℚ k) ∧
      ((z : M) : HahnSeries ℚ k) - (e : HahnSeries ℚ k) =
        asNegRoot p (aneg : HahnSeries ℚ k) hneg + HahnSeries.C j := by
    intro z
    obtain ⟨a, ha⟩ := hsH z
    exact as_normalize p K hK hy hbase _ a ha
  choose e aneg hneg j hzeq hzform using hnorm
  let g : s → M := fun z => (z : M) - algebraMap K M (e z)
  have hgH : ∀ z, (g z : HahnSeries ℚ k) = ((z : M) : HahnSeries ℚ k) - (e z : HahnSeries ℚ k) :=
    fun _ => rfl
  have hgAS : ∀ z, g z ^ p - g z = algebraMap K M (aneg z) := by
    intro z
    apply Subtype.ext
    change (g z : HahnSeries ℚ k)^p - (g z : HahnSeries ℚ k) = (aneg z : HahnSeries ℚ k)
    rw [hgH]
    exact hzeq z
  have hggen : IntermediateField.adjoin K (Set.range g) = ⊤ := by
    rw [eq_top_iff, ← hsgen, IntermediateField.adjoin_le_iff]
    intro z hz
    have : z = g ⟨z, hz⟩ + algebraMap K M (e ⟨z, hz⟩) := by simp [g]
    rw [this]
    exact add_mem (IntermediateField.subset_adjoin K _ ⟨⟨z, hz⟩, rfl⟩)
      (IntermediateField.algebraMap_mem _ _)
  -- Normality and Galois structure.
  have hMgen : IntermediateField.adjoin K
      ((s.image (fun z : M => (z : HahnSeries ℚ k)) : Finset (HahnSeries ℚ k)) :
        Set (HahnSeries ℚ k)) = M := by
    rw [Finset.coe_image]
    change IntermediateField.adjoin K (M.val '' (s : Set M)) = M
    rw [← IntermediateField.adjoin_map, hsgen, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
  have hnormal : Normal K M := by
    apply normal_of_as_generators p K _ _ M hMgen
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hsH ⟨z, hz⟩
    exact ⟨a, ha⟩
  haveI : IsGalois K M := isGalois_iff.mpr ⟨inferInstance, hnormal⟩
  -- Every automorphism translates each normalized generator by a constant.
  have hdiff : ∀ (σ : M ≃ₐ[K] M) (z : s), ∃ d : k,
      ((σ (g z) : M) : HahnSeries ℚ k) - (g z : HahnSeries ℚ k) = HahnSeries.C d := by
    intro σ z
    have h1 : (σ (g z))^p - σ (g z) = algebraMap K M (aneg z) := by
      rw [← map_pow, ← map_sub, hgAS, AlgEquiv.commutes]
    apply as_root_sub_const p
    have h1' := congrArg (fun x : M => (x : HahnSeries ℚ k)) h1
    have h2' := congrArg (fun x : M => (x : HahnSeries ℚ k)) (hgAS z)
    simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow] at h1' h2'
    rw [h1', h2']
  choose d hd using hdiff
  have hdne : ∀ σ : {σ : M ≃ₐ[K] M // σ ≠ 1}, d σ.1 ≠ 0 := by
    rintro ⟨σ, hσ⟩ hzero
    apply hσ
    apply algEquiv_eq_one_of_fixes hggen
    rintro x ⟨z, rfl⟩
    apply Subtype.ext
    have h := hd σ z
    rw [show d σ z = 0 from congrFun hzero z, map_zero, sub_eq_zero] at h
    exact h
  obtain ⟨c, hc⟩ := exists_coeffs_avoiding (fun σ : {σ : M ≃ₐ[K] M // σ ≠ 1} => d σ.1) hdne
  -- The primitive generator.
  let θ : M := ∑ z, algebraMap K M (algebraMap k K (c z)) * g z
  have hθH : (θ : HahnSeries ℚ k) = ∑ z, HahnSeries.C (c z) * (g z : HahnSeries ℚ k) := by
    simp only [θ, IntermediateField.coe_sum, MulMemClass.coe_mul]
    rfl
  have hθdiff : ∀ σ : M ≃ₐ[K] M, ((σ θ : M) : HahnSeries ℚ k) - (θ : HahnSeries ℚ k) =
      HahnSeries.C (∑ z, c z * d σ z) := by
    intro σ
    have hσθ : ((σ θ : M) : HahnSeries ℚ k) =
        ∑ z, HahnSeries.C (c z) * ((σ (g z) : M) : HahnSeries ℚ k) := by
      simp only [θ, map_sum, map_mul, AlgEquiv.commutes, IntermediateField.coe_sum,
        MulMemClass.coe_mul]
      rfl
    rw [hσθ, hθH, ← Finset.sum_sub_distrib, map_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [← mul_sub, hd σ z, ← map_mul]
  have hθfix : ∀ σ : M ≃ₐ[K] M, σ θ = θ → σ = 1 := by
    intro σ hσθ
    by_cases hσ : σ = 1
    · exact hσ
    exfalso
    have h := hθdiff σ
    rw [hσθ, sub_self] at h
    have hsum : ∑ z, c z * d σ z = 0 :=
      HahnSeries.C_injective (by rw [← h, map_zero])
    exact hc ⟨σ, hσ⟩ hsum
  have hθgen : K⟮θ⟯ = ⊤ := adjoin_eq_top_of_fixed_only_by_one θ hθfix
  -- Transfer to the Hahn field.
  have hgenH : K⟮(θ : HahnSeries ℚ k)⟯ = M := by
    calc
      K⟮(θ : HahnSeries ℚ k)⟯ = (K⟮θ⟯).map M.val := by
        symm
        simpa only [Set.image_singleton] using
          IntermediateField.adjoin_map K ({θ} : Set M) M.val
      _ = (⊤ : IntermediateField K M).map M.val := by rw [hθgen]
      _ = M.val.fieldRange := M.val.fieldRange_eq_map.symm
      _ = M := IntermediateField.fieldRange_val M
  have hθint : IsIntegral K (θ : HahnSeries ℚ k) :=
    (IsIntegral.of_finite K θ).map M.val
  have hnormalθ : Normal K K⟮(θ : HahnSeries ℚ k)⟯ := by
    rw [hgenH]
    exact hnormal
  have hconstθ : ∀ σ : K⟮(θ : HahnSeries ℚ k)⟯ ≃ₐ[K] K⟮(θ : HahnSeries ℚ k)⟯,
      σ (AdjoinSimple.gen K (θ : HahnSeries ℚ k)) ≠ AdjoinSimple.gen K (θ : HahnSeries ℚ k) →
      ∃ c' : k, c' ≠ 0 ∧ (σ (AdjoinSimple.gen K (θ : HahnSeries ℚ k)) : HahnSeries ℚ k) -
        (θ : HahnSeries ℚ k) = HahnSeries.C c' := by
    intro σ hσ
    let φ : K⟮(θ : HahnSeries ℚ k)⟯ ≃ₐ[K] M := IntermediateField.equivOfEq hgenH
    let τ : M ≃ₐ[K] M := (φ.symm.trans σ).trans φ
    have hφsymm : φ.symm θ = AdjoinSimple.gen K (θ : HahnSeries ℚ k) := Subtype.ext rfl
    have hτθ : ((τ θ : M) : HahnSeries ℚ k) =
        (σ (AdjoinSimple.gen K (θ : HahnSeries ℚ k)) : HahnSeries ℚ k) := by
      change ((φ (σ (φ.symm θ)) : M) : HahnSeries ℚ k) = _
      rw [hφsymm]
      rfl
    have hτ : τ ≠ 1 := by
      intro h1
      apply hσ
      apply Subtype.ext
      rw [← hτθ, h1]
      rfl
    exact ⟨∑ z, c z * d τ z, hc ⟨τ, hτ⟩, by rw [← hτθ]; exact hθdiff τ⟩
  -- The source's ambient field and its embedded copy of `M`.
  let ι : M →ₐ[K] hahnClosure K := IntermediateField.inclusion hMA
  have hL : ι.fieldRange ≠ ⊥ := by
    intro hbot'
    apply hbot
    rw [eq_bot_iff]
    intro x hx
    have hmem : ι ⟨x, hx⟩ ∈ (⊥ : IntermediateField K (hahnClosure K)) := by
      rw [← hbot']
      exact AlgHom.mem_fieldRange.mpr ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hmem
    rw [IntermediateField.mem_bot]
    exact ⟨a, congrArg Subtype.val ha⟩
  have hgenA : K⟮ι θ⟯ = ι.fieldRange := by
    calc
      K⟮ι θ⟯ = (K⟮θ⟯).map ι := by
        rw [IntermediateField.adjoin_map, Set.image_singleton]
      _ = (⊤ : IntermediateField K M).map ι := by rw [hθgen]
      _ = ι.fieldRange := ι.fieldRange_eq_map.symm
  have hθform : (θ : HahnSeries ℚ k) = ∑ z, HahnSeries.C (c z) *
      (asNegRoot p (aneg z : HahnSeries ℚ k) (hneg z) + HahnSeries.C (j z)) := by
    rw [hθH]
    apply Finset.sum_congr rfl
    intro z _
    rw [hgH, hzform]
  apply (minimum_okutsuLength_one_iff_algebraic K (hahnClosureValuation K) ι.fieldRange hL).mpr
  refine ⟨ι θ, hgenA, ?_⟩
  intro b hb
  have hbint : IsIntegral K (b : HahnSeries ℚ k) := mem_algebraicClosure_iff'.mp b.property
  have hdegθ : elementDegree K (ι θ) = elementDegree K (θ : HahnSeries ℚ k) := by
    rw [elementDegree_algHom ι θ]
    exact (elementDegree_algHom M.val θ).symm
  have hdegb : elementDegree K (b : HahnSeries ℚ k) < elementDegree K (θ : HahnSeries ℚ k) := by
    rw [← hdegθ]
    have h := elementDegree_algHom (hahnClosure K).val b
    change elementDegree K (b : HahnSeries ℚ k) = _ at h
    rw [h]
    exact hb
  have hneg0 := addVal_sub_neg_of_lower_degree K hK (θ : HahnSeries ℚ k) hθint hnormalθ
    hconstθ (b : HahnSeries ℚ k) hbint hdegb
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hneg0.ne_top
  have hq0 : q < 0 := by
    rw [← hq] at hneg0
    exact_mod_cast hneg0
  obtain ⟨a, ha⟩ := exists_base_approx_of_negRoots p K c aneg hneg j q hq0
  refine ⟨a, ?_⟩
  change HahnSeries.addVal ℚ k ((θ : HahnSeries ℚ k) - (b : HahnSeries ℚ k)) ≤
    HahnSeries.addVal ℚ k ((θ : HahnSeries ℚ k) - (a : HahnSeries ℚ k))
  rw [← hq, hθform]
  calc ((q : ℚ) : WithTop ℚ) ≤ ((q / 2 : ℚ) : WithTop ℚ) := by
        exact_mod_cast (by linarith : q ≤ q / 2)
    _ ≤ _ := ha

end Forward

-- From the Fwd6 development stage.
variable {k : Type*} [Field k]

/-- The top of a literal finite Artin--Schreier tower is finite-dimensional over
the base. -/
theorem finiteDimensional_asTower (p : ℕ) [Fact p.Prime]
    (K : IntermediateField k (HahnSeries ℚ k))
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (x : ℕ → HahnSeries ℚ k)
    (hF0 : F 0 = K.toSubfield)
    (hstep : ∀ i < N, ∃ a ∈ F i, x i ^ p - x i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {x i}).toSubfield)
    (M : IntermediateField K (HahnSeries ℚ k)) (hFN : F N = M.toSubfield) :
    FiniteDimensional K M := by
  classical
  let S : ℕ → IntermediateField K (HahnSeries ℚ k) :=
    fun n => IntermediateField.adjoin K (x '' Iio n)
  have hmono : ∀ n, F n ≤ F (n+1) ∨ N ≤ n := by
    intro n
    by_cases hn : n < N
    · left
      obtain ⟨a, _, _, hF⟩ := hstep n hn
      rw [hF]
      intro f hf
      exact IntermediateField.algebraMap_mem (IntermediateField.adjoin (F n) {x n}) ⟨f, hf⟩
    · right
      omega
  have hFS : ∀ n ≤ N, F n ≤ (S n).toSubfield := by
    intro n
    induction n with
    | zero =>
      intro _ f hf
      rw [hF0] at hf
      exact (S 0).algebraMap_mem ⟨f, hf⟩
    | succ n ih =>
      intro hn
      have hle : F n ≤ (S n).toSubfield := ih (Nat.le_trans (Nat.le_succ n) hn)
      have hSS : S n ≤ S (n+1) :=
        IntermediateField.adjoin.mono K _ _ (Set.image_subset x (Set.Iio_subset_Iio (Nat.le_succ n)))
      obtain ⟨a, _, _, hF⟩ := hstep n (Nat.lt_of_succ_le hn)
      rw [hF]
      apply IntermediateField.adjoin_le_subfield
      · rintro f ⟨b, rfl⟩
        exact hSS (hle b.property)
      · intro f hf
        rw [Set.mem_singleton_iff.mp hf]
        exact IntermediateField.subset_adjoin K _ ⟨n, Nat.lt_succ_self n, rfl⟩
  have hmem : ∀ i < N, x i ∈ F N := by
    intro i hi
    have hxi : x i ∈ F (i+1) := by
      obtain ⟨a, _, _, hF⟩ := hstep i hi
      rw [hF]
      exact IntermediateField.subset_adjoin (F i) _ (Set.mem_singleton _)
    have hchain : ∀ m, i + 1 ≤ m → m ≤ N → x i ∈ F m := by
      intro m
      induction m with
      | zero => intro h; omega
      | succ m ih =>
        intro h1 h2
        rcases Nat.lt_or_ge i m with him | him
        · have hprev := ih (by omega) (by omega)
          rcases hmono m with h | h
          · exact h hprev
          · omega
        · have : m = i := by omega
          subst this
          exact hxi
    exact hchain N (by omega) le_rfl
  have hint : ∀ y ∈ x '' Iio N, IsIntegral K y := by
    rintro y ⟨i, hi, rfl⟩
    have h := isIntegral_actual_asTower p N F x hstep (x i) (hmem i hi)
    rw [hF0] at h
    exact h
  haveI : Finite (x '' Iio N) := ((Set.finite_Iio N).image x).to_subtype
  haveI : FiniteDimensional K (S N) := IntermediateField.finiteDimensional_adjoin hint
  have hMS : M ≤ S N := by
    intro y hy
    have : y ∈ F N := by rw [hFN]; exact hy
    exact hFS N le_rfl this
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hMS).toLinearMap
    (IntermediateField.inclusion hMS).injective

section Equivalence
variable {k : Type*} [Field k]

/-- The top of a literal finite Artin--Schreier tower lies in the source's
ambient field. -/
theorem asTower_le_hahnClosure (p : ℕ) [Fact p.Prime]
    (K : IntermediateField k (HahnSeries ℚ k))
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (x : ℕ → HahnSeries ℚ k)
    (hF0 : F 0 = K.toSubfield)
    (hstep : ∀ i < N, ∃ a ∈ F i, x i ^ p - x i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {x i}).toSubfield)
    (M : IntermediateField K (HahnSeries ℚ k)) (hFN : F N = M.toSubfield) :
    M ≤ hahnClosure K := by
  apply le_hahnClosure K M
  intro m
  have hm : (m : HahnSeries ℚ k) ∈ F N := by
    rw [hFN]
    exact m.property
  have h := isIntegral_actual_asTower p N F x hstep m hm
  rw [hF0] at h
  exact h

/-- Conjecture 4.1 of Nart--Novacoski in their ambient field, with depth one
stated as minimum Okutsu length one over all primitive generators (the source's
Theorem 1.3 identifies this minimum with Mac Lane--Vaquié depth): the top of a
nontrivial literal Artin--Schreier tower over `K` has minimum Okutsu length one
if and only if it is the compositum of its Artin--Schreier subextensions. -/
theorem okutsu_minimum_one_iff_asCompositum
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ a ∈ K, LeftFinite a)
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (x : ℕ → HahnSeries ℚ k)
    (hF0 : F 0 = K.toSubfield)
    (hstep : ∀ i < N, ∃ a ∈ F i, x i ^ p - x i = a ∧
      F (i+1) = (IntermediateField.adjoin (F i) {x i}).toSubfield)
    (M : IntermediateField K (HahnSeries ℚ k)) (hFN : F N = M.toSubfield)
    (hbot : M ≠ ⊥) (hMA : M ≤ hahnClosure K) :
    IsLeast (realizedOkutsuLengths K (hahnClosureValuation K)
      (IntermediateField.inclusion hMA).fieldRange) 1 ↔
      artinSchreierCompositum K M p = ⊤ := by
  constructor
  · exact asCompositum_of_hahnClosure_okutsu_minimum p K hK hy hbase N F x hF0 hstep
      M hFN hMA
  · intro hAS
    haveI := finiteDimensional_asTower p K N F x hF0 hstep M hFN
    exact hahnClosure_okutsu_minimum_of_asCompositum p K hK hy hbase M hAS hbot hMA

end Equivalence

end NTCThird
