import Mathlib

/-!
# Actual polynomial valuations and terminal MLV augmentations

This file records genuine polynomial-valued objects, independently of Okutsu
sequences. It specializes the terminal step of a Mac Lane--Vaquie chain to an
augmentation of value infinity. In that case the augmentation formula is
exactly the stable value of the remainder modulo the final key polynomial.

References: Nart, *Okutsu sequences in Henselian valued fields*, Polynesian
J. Math. 1 (2024), no. 4, Definitions 1.2 and 1.7--1.11. Initial-form
divisibility is expressed by cancellation of strictly higher valuation, its
usual algebraic characterization. No comparison theorem is an axiom here.

This module does NOT establish existence of MLV chains or invariance of their
length. It does not define an approximation criterion to be MLV depth.
-/

noncomputable section

open Polynomial

namespace NTCThird.MLV

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- The terminal polynomial valuation is evaluation at the actual element. -/
noncomputable def evaluationValuation (v : AddValuation E (WithTop ℚ)) (θ : E) :
    AddValuation K[X] (WithTop ℚ) :=
  v.comap (aeval θ).toRingHom

@[simp] theorem evaluationValuation_apply (v : AddValuation E (WithTop ℚ))
    (θ : E) (f : K[X]) : evaluationValuation v θ f = v (aeval θ f) := rfl

/-- Divisibility of initial forms. The first disjunct treats the zero initial
form; the second is strict cancellation by a polynomial multiple. -/
noncomputable def InitialDivides (μ : AddValuation K[X] (WithTop ℚ)) (φ f : K[X]) : Prop :=
  μ f = ⊤ ∨ ∃ h : K[X], μ f < μ (f - φ * h)

/-- The usual minimal/prime initial-form definition of a key polynomial.
The finite-value condition excludes the support of a terminal valuation. -/
structure KeyPolynomial (μ : AddValuation K[X] (WithTop ℚ)) (φ : K[X]) : Prop where
  monic : φ.Monic
  finite : μ φ ≠ ⊤
  positive_degree : 0 < φ.natDegree
  minimal : ∀ f : K[X], f ≠ 0 → InitialDivides μ φ f →
    φ.natDegree ≤ f.natDegree
  prime : ∀ f g : K[X], InitialDivides μ φ (f * g) →
    InitialDivides μ φ f ∨ InitialDivides μ φ g

/-- Degree of a nonterminal valuation, defined by actual key polynomials. -/
noncomputable def HasDegree (μ : AddValuation K[X] (WithTop ℚ)) (d : ℕ) : Prop :=
  (∃ φ : K[X], KeyPolynomial μ φ ∧ φ.natDegree = d) ∧
  ∀ φ : K[X], KeyPolynomial μ φ → d ≤ φ.natDegree

theorem initialDivides_zero (μ : AddValuation K[X] (WithTop ℚ)) (φ : K[X]) :
    InitialDivides μ φ 0 := Or.inl μ.map_zero

theorem initialDivides_self (μ : AddValuation K[X] (WithTop ℚ)) (φ : K[X]) :
    InitialDivides μ φ φ := by
  by_cases h : μ φ = ⊤
  · exact Or.inl h
  · exact Or.inr ⟨1, by simpa using (lt_top_iff_ne_top.mpr h)⟩

/-- Initial divisibility by a linear polynomial is strict improvement on its
constant remainder. This uses actual valuation domination by evaluation at
the centre, not any approximation-degree criterion. -/
theorem initialDivides_linear_iff
    (μ : AddValuation K[X] (WithTop ℚ)) (v : AddValuation K (WithTop ℚ)) (a : K)
    (hC : ∀ c : K, μ (C c) = v c)
    (hdom : ∀ f : K[X], μ f ≤ v (f.eval a)) (f : K[X]) :
    InitialDivides μ (X - C a) f ↔ μ f = ⊤ ∨ μ f < v (f.eval a) := by
  constructor
  · rintro (h | ⟨g, hg⟩)
    · exact Or.inl h
    · right
      have h := hg.trans_le (hdom (f - (X - C a) * g))
      simpa using h
  · rintro (h | h)
    · exact Or.inl h
    · right
      refine ⟨f /ₘ (X - C a), ?_⟩
      rw [← modByMonic_eq_sub_mul_div f (X - C a),
        modByMonic_X_sub_C_eq_C_eval, hC]
      exact h

/-- Every finite-valued linear polynomial is a genuine key polynomial for a
valuation below evaluation at its centre. The proof verifies both minimality
and primality of initial divisibility. -/
theorem keyPolynomial_linear
    (μ : AddValuation K[X] (WithTop ℚ)) (v : AddValuation K (WithTop ℚ)) (a : K)
    (hC : ∀ c : K, μ (C c) = v c)
    (hdom : ∀ f : K[X], μ f ≤ v (f.eval a))
    (hfinite : μ (X - C a) ≠ ⊤) : KeyPolynomial μ (X - C a) := by
  refine ⟨monic_X_sub_C a, hfinite, by simp, ?_, ?_⟩
  · intro f hf hdiv
    rw [natDegree_X_sub_C]
    by_contra hn
    have hdeg : f.natDegree = 0 := by omega
    have heq := eq_C_of_natDegree_eq_zero hdeg
    have hc : f.coeff 0 ≠ 0 := by
      intro hz
      apply hf
      rw [heq, hz, map_zero]
    have hfinite_f : μ f ≠ ⊤ := by
      rw [heq, hC]
      exact v.ne_top_iff.mpr hc
    have hlt := ((initialDivides_linear_iff μ v a hC hdom f).mp hdiv).resolve_left hfinite_f
    rw [heq, hC, eval_C] at hlt
    exact lt_irrefl _ hlt
  · intro f g hdiv
    by_contra hnot
    have hf : ¬InitialDivides μ (X - C a) f := fun h => hnot (Or.inl h)
    have hg : ¬InitialDivides μ (X - C a) g := fun h => hnot (Or.inr h)
    have hf' : μ f ≠ ⊤ ∧ ¬μ f < v (f.eval a) := by
      simpa only [initialDivides_linear_iff μ v a hC hdom, not_or] using hf
    have hg' : μ g ≠ ⊤ ∧ ¬μ g < v (g.eval a) := by
      simpa only [initialDivides_linear_iff μ v a hC hdom, not_or] using hg
    have hef : μ f = v (f.eval a) := le_antisymm (hdom f) (le_of_not_gt hf'.2)
    have heg : μ g = v (g.eval a) := le_antisymm (hdom g) (le_of_not_gt hg'.2)
    have hfg : μ (f * g) ≠ ⊤ := by
      rw [μ.map_mul, WithTop.add_ne_top]
      exact ⟨hf'.1, hg'.1⟩
    have hstrict := ((initialDivides_linear_iff μ v a hC hdom (f * g)).mp hdiv)
      |>.resolve_left hfg
    rw [μ.map_mul, eval_mul, v.map_mul, hef, heg] at hstrict
    exact lt_irrefl _ hstrict

theorem hasDegree_one_of_linear_key
    (μ : AddValuation K[X] (WithTop ℚ)) (a : K)
    (h : KeyPolynomial μ (X - C a)) : HasDegree μ 1 := by
  exact ⟨⟨X - C a, h, natDegree_X_sub_C a⟩, fun φ hφ => hφ.positive_degree⟩

/-- A countable linear order without a largest element has a strictly
increasing cofinal sequence. This chooses actual indices, rather than
postulating a continuous valuation family. -/
theorem exists_strictMono_cofinal_nat {A : Type*} [LinearOrder A]
    [Countable A] [Nonempty A] [NoMaxOrder A] :
    ∃ s : ℕ → A, StrictMono s ∧ ∀ a : A, ∃ n : ℕ, a ≤ s n := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat A
  choose next hnext using (fun a : A => exists_gt a)
  let s : ℕ → A := Nat.rec (e 0) (fun n prev => next (max prev (e (n + 1))))
  have hsucc : ∀ n, s n < s (n + 1) := by
    intro n
    change s n < next (max (s n) (e (n + 1)))
    exact (le_max_left _ _).trans_lt (hnext _)
  have he_le : ∀ n, e n ≤ s n := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ n =>
      change e (n + 1) ≤ next (max (s n) (e (n + 1)))
      exact (le_max_right _ _).trans (hnext _).le
  refine ⟨s, strictMono_nat_of_lt_succ hsucc, ?_⟩
  intro a
  obtain ⟨n, rfl⟩ := he a
  exact ⟨n, he_le n⟩

/-- A stable value is eventually constant, with its value retained explicitly. -/
noncomputable def StableValue {I : Type*} [Preorder I]
    (ρ : I → AddValuation K[X] (WithTop ℚ)) (f : K[X]) (γ : WithTop ℚ) : Prop :=
  ∃ i : I, ∀ j : I, i ≤ j → ρ j f = γ

/-- An unstable polynomial has strictly increasing values throughout the
family, exactly as defined in Nart (2024), p. 6. For totally ordered families
of valuations, Nart (2021), equation (5), identifies this with failure of
eventual constancy. The definition below does not assume that equivalence as
an axiom. -/
noncomputable def Unstable {I : Type*} [Preorder I]
    (ρ : I → AddValuation K[X] (WithTop ℚ)) (f : K[X]) : Prop :=
  StrictMono (fun i => ρ i f)

/-- The monic polynomial of least unstable degree. -/
structure LimitKeyPolynomial {I : Type*} [Preorder I]
    (ρ : I → AddValuation K[X] (WithTop ℚ)) (φ : K[X]) : Prop where
  monic : φ.Monic
  unstable : Unstable ρ φ
  minimal : ∀ f : K[X], Unstable ρ f → φ.natDegree ≤ f.natDegree

theorem stableValue_unique {I : Type*} [LinearOrder I]
    {ρ : I → AddValuation K[X] (WithTop ℚ)} {f : K[X]} {γ δ : WithTop ℚ}
    (hγ : StableValue ρ f γ) (hδ : StableValue ρ f δ) : γ = δ := by
  obtain ⟨i, hi⟩ := hγ
  obtain ⟨j, hj⟩ := hδ
  exact (hi (max i j) (le_max_left _ _)).symm.trans
    (hj (max i j) (le_max_right _ _))

theorem not_unstable_of_stableValue {I : Type*} [LinearOrder I] [NoMaxOrder I]
    {ρ : I → AddValuation K[X] (WithTop ℚ)} {f : K[X]} {γ : WithTop ℚ}
    (h : StableValue ρ f γ) : ¬Unstable ρ f := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨j, hij⟩ := exists_gt i
  intro hu
  have hlt := hu hij
  change ρ i f < ρ j f at hlt
  rw [hi i le_rfl, hi j hij.le] at hlt
  exact (lt_irrefl _ hlt)

/-- At infinity, the ordinary augmentation formula is the old valuation of
the polynomial remainder. The new object is itself an actual valuation. -/
structure OrdinaryAtInfinity (μ ν : AddValuation K[X] (WithTop ℚ))
    (φ : K[X]) : Prop where
  key : KeyPolynomial μ φ
  remainder_formula : ∀ f : K[X], ν f = μ (f %ₘ φ)

/-- At infinity, a limit augmentation evaluates every remainder at its stable
value. The stability clauses are explicit, so the formula is not vacuous. -/
structure LimitAtInfinity {I : Type*} [LinearOrder I] [NoMaxOrder I]
    (ρ : I → AddValuation K[X] (WithTop ℚ))
    (ν : AddValuation K[X] (WithTop ℚ)) (φ : K[X]) : Prop where
  key : LimitKeyPolynomial ρ φ
  stable_below : ∀ f : K[X], f.natDegree < φ.natDegree →
    ∃ γ : WithTop ℚ, StableValue ρ f γ
  remainder_formula : ∀ f : K[X], StableValue ρ (f %ₘ φ) (ν f)

/-- The terminal limit formula is forced by low-degree stability at actual
evaluation. This lemma applies to any monic annihilating polynomial; its being
a limit key polynomial is a separate, genuinely mathematical input. -/
theorem limitAtInfinity_of_stable_evaluation
    {I : Type*} [LinearOrder I] [NoMaxOrder I]
    (ρ : I → AddValuation K[X] (WithTop ℚ))
    (v : AddValuation E (WithTop ℚ)) (θ : E) (φ : K[X])
    (hkey : LimitKeyPolynomial ρ φ) (hφ : φ ≠ 1)
    (hroot : aeval θ φ = 0)
    (hstable : ∀ f : K[X], f.natDegree < φ.natDegree →
      StableValue ρ f (v (aeval θ f))) :
    LimitAtInfinity ρ (evaluationValuation v θ) φ := by
  refine ⟨hkey, fun f hf => ⟨_, hstable f hf⟩, ?_⟩
  intro f
  have h := hstable (f %ₘ φ) (natDegree_modByMonic_lt f hkey.monic hφ)
  simpa only [evaluationValuation_apply,
    aeval_modByMonic_eq_self_of_root hroot] using h

end NTCThird.MLV
