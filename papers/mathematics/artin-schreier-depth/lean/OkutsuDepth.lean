import Mathlib

/-!
# Genuine Okutsu sequences and their length-one criterion

This file formalizes Definition 1.2 of Nart--Novacoski, arXiv:2503.18827v2,
with actual algebraic elements, minimal-polynomial degrees, and a valuation.
It proves the length-one approximation criterion and its minimum-over-generators
formulation. It does not identify Okutsu length with Mac Lane--Vaquié depth:
the paper's Theorem 1.3 is not formalized here, nor assumed as an axiom.
-/

noncomputable section

open scoped IntermediateField

namespace NTCThird

/-- Any linearly ordered image has cofinal representatives whose images are
strictly well ordered. The representatives, not merely the image, are ordered
injectively. This is the choice step in the existence of an Okutsu set. -/
theorem cofinal_wellOrdered_representatives {A B : Type*} [LinearOrder B]
    (f : A → B) :
    ∃ s : Set A,
      (∀ a, ∃ b ∈ s, f a ≤ f b) ∧
      s.WellFoundedOn (fun a b => f a < f b) ∧ s.InjOn f := by
  classical
  let s : Set A := {a | ∀ b, WellOrderingRel b a → f b < f a}
  have hw : WellFounded (@WellOrderingRel A) :=
    (inferInstance : IsWellFounded A WellOrderingRel).wf
  have hcof : ∀ a, ∃ b ∈ s, f a ≤ f b := by
    intro a
    obtain ⟨b, hb, hmin⟩ := hw.has_min {b | f a ≤ f b} ⟨a, le_rfl⟩
    refine ⟨b, ?_, hb⟩
    intro c hcb
    by_contra h
    exact hmin c (le_trans hb (le_of_not_gt h)) hcb
  have hrel : ∀ a ∈ s, ∀ b ∈ s, f a < f b → WellOrderingRel a b := by
    intro a ha b hb hab
    rcases trichotomous_of WellOrderingRel a b with hab' | hab' | hba'
    · exact hab'
    · subst b
      exact (lt_irrefl _ hab).elim
    · exact (lt_asymm hab (ha b hba')).elim
  refine ⟨s, hcof, (hw.wellFoundedOn).mono' hrel, ?_⟩
  intro a ha b hb heq
  rcases trichotomous_of WellOrderingRel a b with hab | hab | hba
  · exact (ne_of_lt (hb a hab) heq).elim
  · exact hab
  · exact (ne_of_lt (ha b hba) heq.symm).elim

/-- The two explicit OS2 clauses give the literal strict well order on the
chosen elements, not only a well-founded relation with possible distance ties. -/
theorem isWellOrder_on_of_distance {A B : Type*} [LinearOrder B]
    (f : A → B) (s : Set A)
    (hw : s.WellFoundedOn (fun a b => f a < f b)) (hi : s.InjOn f) :
    IsWellOrder s (fun a b => f a < f b) where
  wf := hw
  trans := fun _ _ _ hab hbc => hab.trans hbc
  trichotomous := by
    intro a b
    rcases lt_trichotomy (f a) (f b) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Subtype.ext (hi a.property b.property h)))
    · exact Or.inr (Or.inr h)

section Okutsu

variable (K : Type*) {E Γ : Type*} [Field K] [Field E] [Algebra K E]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- The actual algebraic degree of an element, expressed by its minimal polynomial. -/
def elementDegree (x : E) : ℕ := (minpoly K x).natDegree

theorem elementDegree_eq_one_iff (x : E) :
    elementDegree K x = 1 ↔ x ∈ (algebraMap K E).range :=
  minpoly.natDegree_eq_one_iff

theorem elementDegree_algebraMap (a : K) :
    elementDegree K (algebraMap K E a) = 1 :=
  (elementDegree_eq_one_iff K _).2 ⟨a, rfl⟩

theorem finrank_adjoin_eq_elementDegree (x : E) (hx : IsIntegral K x) :
    Module.finrank K K⟮x⟯ = elementDegree K x :=
  IntermediateField.adjoin.finrank hx

/-- Existence of a largest value among approximations of one fixed degree. -/
def HasMaxDistance (v : AddValuation E (WithTop Γ)) (θ : E) (m : ℕ) : Prop :=
  ∃ a : E, elementDegree K a = m ∧
    ∀ b : E, elementDegree K b = m → v (θ - b) ≤ v (θ - a)

/-- Actual Okutsu sequence, including OS0--OS3. OS2 is written as well-foundedness
and injectivity of distance, which together express the strict well ordering in
the source definition. The final set is the singleton of the actual element. -/
structure OkutsuSequence (v : AddValuation E (WithTop Γ)) (θ : E) (r : ℕ) where
  sets : Fin (r + 1) → Set E
  degrees : Fin (r + 1) → ℕ
  nonempty : ∀ i, (sets i).Nonempty
  common_degree : ∀ i a, a ∈ sets i → elementDegree K a = degrees i
  first_degree : degrees 0 = 1
  last_set : sets (Fin.last r) = {θ}
  last_degree : degrees (Fin.last r) = elementDegree K θ
  strict_degrees : StrictMono degrees
  os0 : ∀ i : Fin r, ∀ b : E, elementDegree K b < degrees i.succ →
    ∃ a ∈ sets i.castSucc, v (θ - b) ≤ v (θ - a)
  os1 : ∀ i : Fin r, HasMaxDistance K v θ (degrees i.castSucc) →
    ∃ a, sets i.castSucc = {a}
  os2 : ∀ i : Fin r, ¬HasMaxDistance K v θ (degrees i.castSucc) →
    (sets i.castSucc).WellFoundedOn (fun a b => v (θ - a) < v (θ - b)) ∧
    (sets i.castSucc).InjOn (fun a => v (θ - a))
  os3 : ∀ i : Fin r, ∀ a ∈ sets i.castSucc, ∀ b ∈ sets i.succ,
    v (θ - a) < v (θ - b)

/-- The lower-degree approximation condition occurring in the paper's
length-one characterization, with constants from the actual base field. -/
def BaseApproximation (v : AddValuation E (WithTop Γ)) (θ : E) : Prop :=
  ∀ b : E, elementDegree K b < elementDegree K θ →
    ∃ a : K, v (θ - b) ≤ v (θ - algebraMap K E a)

/-- Data for the first set of an actual two-set Okutsu sequence. -/
structure InitialOkutsuSet (v : AddValuation E (WithTop Γ)) (θ : E) where
  carrier : Set E
  nonempty : carrier.Nonempty
  common_degree : ∀ a ∈ carrier, elementDegree K a = 1
  os0 : ∀ b : E, elementDegree K b < elementDegree K θ →
    ∃ a ∈ carrier, v (θ - b) ≤ v (θ - a)
  os1 : HasMaxDistance K v θ 1 → ∃ a, carrier = {a}
  os2 : ¬HasMaxDistance K v θ 1 →
    carrier.WellFoundedOn (fun a b => v (θ - a) < v (θ - b)) ∧
    carrier.InjOn (fun a => v (θ - a))
  os3 : ∀ a ∈ carrier, v (θ - a) < v (θ - θ)

theorem degree_one_distance_lt_self (v : AddValuation E (WithTop Γ))
    (θ a : E) (hθ : 1 < elementDegree K θ) (ha : elementDegree K a = 1) :
    v (θ - a) < v (θ - θ) := by
  have hne : θ - a ≠ 0 := by
    intro h
    have heq : θ = a := sub_eq_zero.mp h
    rw [heq, ha] at hθ
    exact (lt_irrefl _ hθ)
  rw [sub_self, v.map_zero]
  exact lt_top_iff_ne_top.mpr (v.ne_top_iff.mpr hne)

/-- The cofinal approximation condition constructs an Okutsu set satisfying
all four source conditions, including the maximum/no-maximum normalization. -/
theorem initialOkutsuSet_exists (v : AddValuation E (WithTop Γ)) (θ : E)
    (hθ : 1 < elementDegree K θ) (hc : BaseApproximation K v θ) :
    Nonempty (InitialOkutsuSet K v θ) := by
  classical
  by_cases hmax : HasMaxDistance K v θ 1
  · obtain ⟨a, ha, hdom⟩ := hmax
    refine ⟨{
      carrier := {a}
      nonempty := Set.singleton_nonempty a
      common_degree := ?_
      os0 := ?_
      os1 := fun _ => ⟨a, rfl⟩
      os2 := ?_
      os3 := ?_ }⟩
    · intro b hb
      simpa only [Set.mem_singleton_iff.mp hb] using ha
    · intro b hb
      obtain ⟨c, hc⟩ := hc b hb
      exact ⟨a, Set.mem_singleton a, hc.trans
        (hdom (algebraMap K E c) (elementDegree_algebraMap K c))⟩
    · intro h
      exact (h ⟨a, ha, hdom⟩).elim
    · intro b hb
      rcases Set.mem_singleton_iff.mp hb with rfl
      exact degree_one_distance_lt_self K v θ _ hθ ha
  · obtain ⟨s, hcof, hwf, hinj⟩ :=
      cofinal_wellOrdered_representatives (fun a : K => v (θ - algebraMap K E a))
    refine ⟨{
      carrier := algebraMap K E '' s
      nonempty := ?_
      common_degree := ?_
      os0 := ?_
      os1 := fun h => (hmax h).elim
      os2 := ?_
      os3 := ?_ }⟩
    · obtain ⟨a, ha, _⟩ := hcof 0
      exact ⟨_, a, ha, rfl⟩
    · rintro a ⟨b, hb, rfl⟩
      exact elementDegree_algebraMap K b
    · intro b hb
      obtain ⟨a, ha⟩ := hc b hb
      obtain ⟨c, hcs, hac⟩ := hcof a
      exact ⟨_, ⟨c, hcs, rfl⟩, ha.trans hac⟩
    · intro _
      refine ⟨Set.wellFoundedOn_image.mpr hwf, ?_⟩
      rintro a ⟨b, hb, rfl⟩ c ⟨d, hd, rfl⟩ heq
      exact congrArg (algebraMap K E) (hinj hb hd heq)
    · rintro a ⟨b, hb, rfl⟩
      exact degree_one_distance_lt_self K v θ _ hθ (elementDegree_algebraMap K b)

/-- Turn the genuine initial approximation set into the complete sequence
`[A₀,{θ}]`; the second degree is the actual degree of θ. -/
def InitialOkutsuSet.toSequence {v : AddValuation E (WithTop Γ)} {θ : E}
    (a : InitialOkutsuSet K v θ) (hθ : 1 < elementDegree K θ) :
    OkutsuSequence K v θ 1 where
  sets := ![a.carrier, {θ}]
  degrees := ![1, elementDegree K θ]
  nonempty := by
    intro i
    fin_cases i
    · exact a.nonempty
    · exact Set.singleton_nonempty θ
  common_degree := by
    intro i b hb
    fin_cases i
    · exact a.common_degree b hb
    · simpa using congrArg (elementDegree K) (Set.mem_singleton_iff.mp hb)
  first_degree := rfl
  last_set := rfl
  last_degree := rfl
  strict_degrees := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  os0 := by
    intro i b hb
    fin_cases i
    exact a.os0 b hb
  os1 := by
    intro i h
    fin_cases i
    exact a.os1 h
  os2 := by
    intro i h
    fin_cases i
    exact a.os2 h
  os3 := by
    intro i b hb c hc
    fin_cases i
    rcases Set.mem_singleton_iff.mp hc with rfl
    exact a.os3 b hb

theorem okutsuSequence_one_iff (v : AddValuation E (WithTop Γ)) (θ : E) :
    Nonempty (OkutsuSequence K v θ 1) ↔
      1 < elementDegree K θ ∧ BaseApproximation K v θ := by
  constructor
  · rintro ⟨s⟩
    have hlt := s.strict_degrees (show (0 : Fin 2) < 1 by decide)
    have hdeg : s.degrees 1 = elementDegree K θ := s.last_degree
    rw [s.first_degree, hdeg] at hlt
    refine ⟨hlt, ?_⟩
    intro b hb
    obtain ⟨a, ha, hab⟩ := s.os0 0 b (by simpa only [Fin.succ_zero_eq_one, hdeg] using hb)
    have ha1 : elementDegree K a = 1 :=
      (s.common_degree 0 a ha).trans s.first_degree
    obtain ⟨c, rfl⟩ := (elementDegree_eq_one_iff K a).mp ha1
    exact ⟨c, hab⟩
  · rintro ⟨hθ, hc⟩
    obtain ⟨a⟩ := initialOkutsuSet_exists K v θ hθ hc
    exact ⟨a.toSequence K hθ⟩

theorem elementDegree_one_iff_adjoin_eq_bot (θ : E) :
    elementDegree K θ = 1 ↔ K⟮θ⟯ = ⊥ := by
  rw [elementDegree_eq_one_iff, IntermediateField.adjoin_simple_eq_bot_iff,
    IntermediateField.mem_bot]
  rfl

/-- Lengths realized by genuine sequences for every primitive element of an
actual intermediate field. No preferred generator is fixed in this definition. -/
def realizedOkutsuLengths (v : AddValuation E (WithTop Γ))
    (L : IntermediateField K E) : Set ℕ :=
  {r | ∃ θ : E, K⟮θ⟯ = L ∧ Nonempty (OkutsuSequence K v θ r)}

theorem okutsuSequence_zero_degree (v : AddValuation E (WithTop Γ)) (θ : E)
    (s : OkutsuSequence K v θ 0) : elementDegree K θ = 1 := by
  have hl : s.degrees 0 = elementDegree K θ := s.last_degree
  exact hl.symm.trans s.first_degree

theorem zero_not_mem_realizedOkutsuLengths (v : AddValuation E (WithTop Γ))
    (L : IntermediateField K E) (hL : L ≠ ⊥) :
    0 ∉ realizedOkutsuLengths K v L := by
  rintro ⟨θ, hgen, ⟨s⟩⟩
  apply hL
  rw [← hgen]
  exact (elementDegree_one_iff_adjoin_eq_bot K θ).mp
    (okutsuSequence_zero_degree K v θ s)

/-- Minimum one over all primitive generators is equivalent to the explicit
approximation criterion for some generator. This conclusion concerns actual
Okutsu sequences; identifying this minimum with MLV depth is a separate theorem. -/
theorem minimum_okutsuLength_one_iff (v : AddValuation E (WithTop Γ))
    (L : IntermediateField K E) (hL : L ≠ ⊥) :
    IsLeast (realizedOkutsuLengths K v L) 1 ↔
      ∃ θ : E, K⟮θ⟯ = L ∧
        1 < elementDegree K θ ∧ BaseApproximation K v θ := by
  constructor
  · rintro ⟨⟨θ, hθ, hs⟩, _⟩
    exact ⟨θ, hθ, (okutsuSequence_one_iff K v θ).mp hs⟩
  · rintro ⟨θ, hgen, hdeg, happ⟩
    refine ⟨⟨θ, hgen, (okutsuSequence_one_iff K v θ).mpr ⟨hdeg, happ⟩⟩, ?_⟩
    intro r hr
    have hr0 : r ≠ 0 := by
      intro h
      subst r
      exact zero_not_mem_realizedOkutsuLengths K v L hL hr
    omega

/-- In an algebraic ambient field (in particular an algebraic closure),
nontrivial generation already gives the necessary degree bound. -/
theorem minimum_okutsuLength_one_iff_algebraic [Algebra.IsAlgebraic K E]
    (v : AddValuation E (WithTop Γ)) (L : IntermediateField K E) (hL : L ≠ ⊥) :
    IsLeast (realizedOkutsuLengths K v L) 1 ↔
      ∃ θ : E, K⟮θ⟯ = L ∧ BaseApproximation K v θ := by
  rw [minimum_okutsuLength_one_iff K v L hL]
  constructor
  · rintro ⟨θ, hgen, _, happ⟩
    exact ⟨θ, hgen, happ⟩
  · rintro ⟨θ, hgen, happ⟩
    have hnot : θ ∉ (algebraMap K E).range := by
      intro h
      apply hL
      rw [← hgen, ← elementDegree_one_iff_adjoin_eq_bot]
      exact (elementDegree_eq_one_iff K θ).mpr h
    have hdeg : 2 ≤ elementDegree K θ :=
      (minpoly.two_le_natDegree_iff
        (Algebra.IsAlgebraic.isAlgebraic (R := K) θ).isIntegral).mpr hnot
    exact ⟨θ, hgen, hdeg, happ⟩

/-- A strict separation from all base-field approximations rules out any
Okutsu sequence of length one when the separating element has lower degree. -/
theorem not_okutsuSequence_one_of_lower_degree
    (v : AddValuation E (WithTop Γ)) (θ α : E)
    (hdeg : elementDegree K α < elementDegree K θ)
    (hsep : ∀ a : K, v (θ - algebraMap K E a) < v (θ - α)) :
    ¬Nonempty (OkutsuSequence K v θ 1) := by
  intro hs
  obtain ⟨_, happ⟩ := (okutsuSequence_one_iff K v θ).mp hs
  obtain ⟨a, ha⟩ := happ α hdeg
  exact (not_lt_of_ge ha) (hsep a)

theorem not_okutsuSequence_one_of_boundary
    (v : AddValuation E (WithTop Γ)) (θ α : E) (δ : WithTop Γ)
    (hdeg : elementDegree K α < elementDegree K θ)
    (hbase : ∀ a : K, v (θ - algebraMap K E a) < δ)
    (hα : δ ≤ v (θ - α)) :
    ¬Nonempty (OkutsuSequence K v θ 1) :=
  not_okutsuSequence_one_of_lower_degree K v θ α hdeg
    (fun a => (hbase a).trans_le hα)

/-- The exact final degree argument: a contained first-block field whose
generator beats all constants must be the entire primitive field whenever θ
has an actual length-one Okutsu sequence. -/
theorem adjoin_eq_of_okutsuSequence_one
    (v : AddValuation E (WithTop Γ)) (θ α : E)
    (hθint : IsIntegral K θ) (hαint : IsIntegral K α)
    (hs : Nonempty (OkutsuSequence K v θ 1))
    (hsub : K⟮α⟯ ≤ K⟮θ⟯)
    (hsep : ∀ a : K, v (θ - algebraMap K E a) < v (θ - α)) :
    K⟮α⟯ = K⟮θ⟯ := by
  letI := IntermediateField.adjoin.finiteDimensional hθint
  apply IntermediateField.eq_of_le_of_finrank_le hsub
  rw [finrank_adjoin_eq_elementDegree K θ hθint,
    finrank_adjoin_eq_elementDegree K α hαint]
  exact le_of_not_gt fun hdeg =>
    not_okutsuSequence_one_of_lower_degree K v θ α hdeg hsep hs

/-- The all-generator minimum theorem in the paper's exact ambient algebraic
closure, so every lower-degree algebraic approximant is quantified over. -/
theorem algebraicClosure_minimum_okutsuLength_one_iff
    (v : AddValuation (AlgebraicClosure K) (WithTop Γ))
    (L : IntermediateField K (AlgebraicClosure K)) (hL : L ≠ ⊥) :
    IsLeast (realizedOkutsuLengths K v L) 1 ↔
      ∃ θ : AlgebraicClosure K, K⟮θ⟯ = L ∧ BaseApproximation K v θ :=
  minimum_okutsuLength_one_iff_algebraic K v L hL

end Okutsu

/-- A nonzero vector is detected by a surjective additive linear form. -/
theorem exists_separating_additive_form {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] (x : V) (hx : x ≠ 0) :
    ∃ f : V →+ F, Function.Surjective f ∧ f x ≠ 0 := by
  classical
  have hn : ¬∀ f : Module.Dual F V, f x = 0 := by
    rw [Module.forall_dual_apply_eq_zero_iff]
    exact hx
  obtain ⟨f, hf⟩ := not_forall.mp hn
  refine ⟨f.toAddMonoidHom, ?_, hf⟩
  intro a
  refine ⟨(a / f x) • x, ?_⟩
  change f ((a / f x) • x) = a
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ a hf]

/-- Characters into the prime cyclic group separate elements of an actual
commutative group of exponent p. The character is constructed from a genuine
linear form over `ZMod p`, and is surjective. -/
theorem exists_prime_character {G : Type*} [CommGroup G]
    (p : ℕ) [Fact p.Prime] (hp : ∀ g : G, g ^ p = 1)
    (g : G) (hg : g ≠ 1) :
    ∃ χ : G →* Multiplicative (ZMod p), Function.Surjective χ ∧ χ g ≠ 1 := by
  classical
  letI : Module (ZMod p) (Additive G) :=
    AddCommGroup.zmodModule (fun x => congrArg Additive.ofMul (hp x.toMul))
  have hg0 : Additive.ofMul g ≠ 0 := hg
  obtain ⟨f, hsurj, hf⟩ :=
    exists_separating_additive_form (F := ZMod p) (Additive.ofMul g) hg0
  let χ : G →* Multiplicative (ZMod p) := AddMonoidHom.toMultiplicative' f
  refine ⟨χ, ?_, ?_⟩
  · intro z
    obtain ⟨x, hx⟩ := hsurj z.toAdd
    exact ⟨x.toMul, congrArg Multiplicative.ofAdd hx⟩
  · intro h
    exact hf (congrArg Multiplicative.toAdd h)

/-!
## Degree-p Galois extensions

The following standard theorem is adapted to the pinned Lean 4.19 API from
Yijun Yuan's Apache-2.0 `TrustworthyKedlaya.exists_artinSchreier_generator`:
https://github.com/YijunYuan/TrustworthyKedlaya/blob/f97be4372713e25a21603dec26706d8bb0cd9d24/TrustworthyKedlaya/Kedlaya/ArtinSchreierGalois.lean
Copyright (c) 2026 Yijun Yuan. Released under Apache 2.0.
This is prior-known supporting mathematics, not a claimed new result.
-/

section ArtinSchreier

open Finset IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **Degree-`p` Galois extensions are Artin–Schreier**: if `F` has characteristic `p`
and `E/F` is Galois of degree `p`, then `E = F(θ)` with `θ^p - θ ∈ F`. -/
theorem exists_artinSchreier_generator_of_prime_degree (p : ℕ) [Fact p.Prime] [CharP F p] [IsGalois F E]
    (hrank : Module.finrank F E = p) :
    ∃ θ : E, F⟮θ⟯ = ⊤ ∧ θ ^ p - θ ∈ (algebraMap F E).range := by
  have hp : p.Prime := Fact.out
  have : FiniteDimensional F E := FiniteDimensional.of_finrank_pos (hrank ▸ hp.pos)
  have : CharP E p := charP_of_injective_algebraMap (algebraMap F E).injective p
  have : ExpChar E p := .prime hp
  -- The Galois group has prime order `p`; any `σ ≠ 1` has order `p`.
  have hcard : Fintype.card (E ≃ₐ[F] E) = p := by
    rw [IsGalois.card_aut_eq_finrank F E, hrank]
  have : Nontrivial (E ≃ₐ[F] E) := Fintype.one_lt_card_iff_nontrivial.mp (hcard ▸ hp.one_lt)
  obtain ⟨σ, hσ1⟩ := exists_ne (1 : E ≃ₐ[F] E)
  have hσp : orderOf σ = p := orderOf_eq_prime (hcard ▸ pow_card_eq_one) hσ1
  have hσpow : σ ^ p = 1 := hcard ▸ pow_card_eq_one
  -- The powers `σ^0, …, σ^{p-1}` exhaust the group.
  have hbij : Function.Bijective (fun i : Fin p => σ ^ (i : ℕ)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨fun i j hij => Fin.ext (pow_injOn_Iio_orderOf
        (by simp [hσp]) (by simp [hσp]) hij),
      (Fintype.card_fin p).trans hcard.symm⟩
  -- An element of trace one, and its power sum.
  obtain ⟨c, hc⟩ := Algebra.trace_surjective F E (1 : F)
  have hT : ∑ i ∈ range p, (σ ^ i) c = 1 := by
    calc ∑ i ∈ range p, (σ ^ i) c
        = ∑ i : Fin p, (σ ^ (i : ℕ)) c := (Fin.sum_univ_eq_sum_range (fun j => (σ ^ j) c) p).symm
      _ = ∑ g : E ≃ₐ[F] E, g c := hbij.sum_comp (fun g => g c)
      _ = 1 := by rw [← trace_eq_sum_automorphisms, hc, map_one]
  -- The Artin–Schreier generator.
  set θ : E := -∑ i ∈ range p, (i : E) * (σ ^ i) c with hθ
  have hkey : σ θ = θ + 1 := by
    have hf0 : ∑ j ∈ range (p + 1), (j : E) * (σ ^ j) c = ∑ i ∈ range p, (i : E) * (σ ^ i) c := by
      rw [sum_range_succ, CharP.cast_eq_zero E p, zero_mul, add_zero]
    have hg0 : ∑ j ∈ range (p + 1), (σ ^ j) c = 1 + c := by
      rw [sum_range_succ, hT, hσpow, AlgEquiv.one_apply]
    have hσθ : σ (∑ i ∈ range p, (i : E) * (σ ^ i) c)
        = ∑ i ∈ range p, (i : E) * (σ ^ (i + 1)) c := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [map_mul, map_natCast, pow_succ', AlgEquiv.mul_apply]
    have hsplit : ∑ i ∈ range p, (i : E) * (σ ^ (i + 1)) c
        = (∑ i ∈ range p, ((i + 1 : ℕ) : E) * (σ ^ (i + 1)) c)
          - ∑ i ∈ range p, (σ ^ (i + 1)) c := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    have hfshift : ∑ i ∈ range p, ((i + 1 : ℕ) : E) * (σ ^ (i + 1)) c
        = ∑ i ∈ range p, (i : E) * (σ ^ i) c := by
      rw [← hf0, Finset.sum_range_succ' (fun j => (j : E) * (σ ^ j) c) p]
      simp
    have hgshift : ∑ i ∈ range p, (σ ^ (i + 1)) c = 1 := by
      have := Finset.sum_range_succ' (fun j => (σ ^ j) c) p
      rw [hg0] at this
      simpa using this.symm
    rw [hθ, map_neg, hσθ, hsplit, hfshift, hgshift]
    ring
  -- `θ^p - θ` is fixed by `σ`, hence by the whole Galois group, hence lies in `F`.
  have hσfix : σ (θ ^ p - θ) = θ ^ p - θ := by
    rw [map_sub, map_pow, hkey, add_pow_char, one_pow, add_sub_add_right_eq_sub]
  have hfix : ∀ g : E ≃ₐ[F] E, g (θ ^ p - θ) = θ ^ p - θ := by
    have hpow : ∀ n : ℕ, (σ ^ n) (θ ^ p - θ) = θ ^ p - θ := by
      intro n
      induction n with
      | zero => rw [pow_zero, AlgEquiv.one_apply]
      | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hσfix]
    intro g
    obtain ⟨i, rfl⟩ := hbij.surjective g
    exact hpow i
  have hmem : θ ^ p - θ ∈ (algebraMap F E).range := by
    have hf : θ ^ p - θ ∈ fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) :=
      (mem_fixedField_iff _ _).mpr (fun g _ => hfix g)
    rw [InfiniteGalois.fixedField_bot, IntermediateField.mem_bot] at hf
    exact hf
  -- `θ` is moved by `σ`, so it does not lie in `F`; hence it generates `E`.
  have hnotbot : θ ∉ (⊥ : IntermediateField F E) := by
    intro h
    rw [IntermediateField.mem_bot] at h
    obtain ⟨x, hx⟩ := h
    have hfixθ := σ.commutes x
    rw [hx, hkey] at hfixθ
    simp at hfixθ
  refine ⟨θ, ?_, hmem⟩
  have htower : Module.finrank F F⟮θ⟯ * Module.finrank F⟮θ⟯ E = p := by
    rw [Module.finrank_mul_finrank, hrank]
  rcases hp.eq_one_or_self_of_dvd _ (Dvd.intro_left _ htower) with h1 | hpp
  · apply IntermediateField.eq_of_le_of_finrank_le' le_top
    rw [h1, IntermediateField.finrank_top]
  · exfalso
    rw [hpp] at htower
    have hone : Module.finrank F F⟮θ⟯ = 1 :=
      Nat.eq_of_mul_eq_mul_right hp.pos (htower.trans (one_mul p).symm)
    exact hnotbot (IntermediateField.finrank_eq_one_iff.mp hone ▸
      IntermediateField.mem_adjoin_simple_self F θ)


/-- The actual subfield generated by all Artin--Schreier roots already in E. -/
def artinSchreierCompositum (F E : Type*) [Field F] [Field E] [Algebra F E]
    (p : ℕ) : IntermediateField F E :=
  IntermediateField.adjoin F {x : E | x ^ p - x ∈ (algebraMap F E).range}

/-- A finite Galois extension with commutative exponent-p Galois group is
generated by actual Artin--Schreier roots over its base field. -/
theorem artinSchreierCompositum_eq_top (p : ℕ) [Fact p.Prime] [CharP F p]
    [FiniteDimensional F E] [IsGalois F E]
    (hcomm : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ)
    (hexp : ∀ σ : E ≃ₐ[F] E, σ ^ p = 1) :
    artinSchreierCompositum F E p = ⊤ := by
  classical
  letI : CommGroup (E ≃ₐ[F] E) := { inferInstanceAs (Group (E ≃ₐ[F] E)) with
    mul_comm := hcomm }
  apply (IsGalois.intermediateFieldEquivSubgroup (F := F) (E := E)).injective
  change (artinSchreierCompositum F E p).fixingSubgroup =
    (⊤ : IntermediateField F E).fixingSubgroup
  rw [IntermediateField.fixingSubgroup_top]
  apply le_antisymm ?_ bot_le
  intro σ hσ
  change σ = 1
  by_contra hσ1
  obtain ⟨χ, hχsurj, hχσ⟩ := exists_prime_character p hexp σ hσ1
  let L : IntermediateField F E := fixedField χ.ker
  haveI : IsGalois F L := IsGalois.of_fixedField_normal_subgroup χ.ker
  let e : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod p) :=
    (IsGalois.normalAutEquivQuotient χ.ker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective χ hχsurj)
  have hrank : Module.finrank F L = p := by
    rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_eq_fintype_card]
    exact (Nat.card_congr e.toEquiv).trans
      ((Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p))
  obtain ⟨θ, hgen, hθ⟩ := exists_artinSchreier_generator_of_prime_degree (F := F) p hrank
  have hθE : (θ : E)^p - (θ : E) ∈ (algebraMap F E).range := by
    obtain ⟨a, ha⟩ := hθ
    exact ⟨a, congrArg Subtype.val ha⟩
  have hθM : (θ : E) ∈ artinSchreierCompositum F E p :=
    subset_adjoin F _ hθE
  have hσθ : σ (θ : E) = (θ : E) := hσ ⟨θ, hθM⟩
  have hgenA : Algebra.adjoin F ({θ} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral
      (IsIntegral.of_finite F θ), hgen, IntermediateField.top_toSubalgebra]
  have hres : AlgEquiv.restrictNormalHom L σ = 1 := by
    have hh : (AlgEquiv.restrictNormalHom L σ).toAlgHom = (1 : L ≃ₐ[F] L).toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top hgenA
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      apply Subtype.val_injective
      change ((AlgEquiv.restrictNormalHom L σ) x : E) = ((1 : L ≃ₐ[F] L) x : E)
      rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.one_apply]
      exact hσθ
    ext x
    exact congrArg Subtype.val (congrArg (fun f : L →ₐ[F] L => f x) hh)
  have hker : σ ∈ (AlgEquiv.restrictNormalHom L).ker := hres
  rw [IntermediateField.restrictNormalHom_ker] at hker
  change σ ∈ (fixedField χ.ker).fixingSubgroup at hker
  rw [IntermediateField.fixingSubgroup_fixedField] at hker
  exact hχσ hker

/-- Finiteness is explicit: the elementary-abelian extension is generated by a
finite set of elements, each satisfying an actual AS equation over the base. -/
theorem exists_finite_artinSchreier_generators (p : ℕ) [Fact p.Prime] [CharP F p]
    [FiniteDimensional F E] [IsGalois F E]
    (hcomm : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ)
    (hexp : ∀ σ : E ≃ₐ[F] E, σ ^ p = 1) :
    ∃ s : Finset E, IntermediateField.adjoin F (s : Set E) = ⊤ ∧
      ∀ x ∈ s, ∃ a : F, x ^ p - x = algebraMap F E a := by
  classical
  obtain ⟨θ, hgen⟩ := Field.exists_primitive_element F E
  have hθ : θ ∈ artinSchreierCompositum F E p := by
    rw [artinSchreierCompositum_eq_top p hcomm hexp]
    exact IntermediateField.mem_top
  obtain ⟨s, hs, hθs⟩ := IntermediateField.exists_finset_of_mem_adjoin hθ
  refine ⟨s, ?_, ?_⟩
  · apply top_unique
    rw [← hgen]
    exact IntermediateField.adjoin_simple_le_iff.mpr hθs
  · intro x hx
    obtain ⟨a, ha⟩ := hs hx
    exact ⟨a, ha.symm⟩

/-- Redundant base-field generators can be removed. Thus the compositum is
generated by finitely many nontrivial AS extensions, including the empty set
in the trivial-extension edge case. -/
theorem exists_finite_nontrivial_artinSchreier_generators
    (p : ℕ) [Fact p.Prime] [CharP F p] [FiniteDimensional F E] [IsGalois F E]
    (hcomm : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ)
    (hexp : ∀ σ : E ≃ₐ[F] E, σ ^ p = 1) :
    ∃ s : Finset E, IntermediateField.adjoin F (s : Set E) = ⊤ ∧
      ∀ x ∈ s, x ∉ (algebraMap F E).range ∧
        ∃ a : F, x ^ p - x = algebraMap F E a := by
  classical
  obtain ⟨s, hgen, heq⟩ := exists_finite_artinSchreier_generators p hcomm hexp
  let t := s.filter (fun x => x ∉ (algebraMap F E).range)
  refine ⟨t, ?_, ?_⟩
  · apply top_unique
    rw [← hgen]
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    by_cases hbase : x ∈ (algebraMap F E).range
    · exact (show (⊥ : IntermediateField F E) ≤ IntermediateField.adjoin F (t : Set E)
        from bot_le) (IntermediateField.mem_bot.mpr hbase)
    · exact IntermediateField.subset_adjoin F _ (Finset.mem_filter.mpr ⟨hx, hbase⟩)
  · intro x hx
    obtain ⟨hxs, hbase⟩ := Finset.mem_filter.mp hx
    exact ⟨hbase, heq x hxs⟩

end ArtinSchreier

end NTCThird
