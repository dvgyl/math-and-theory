import QPermanentResearch.IntegerPolynomial
import Mathlib.Data.List.Chain

open scoped BigOperators
namespace QPermanentResearch

def integerPowerWeight (e : Power3) : ℕ :=
  (powerX e).factorial * (powerY e).factorial * (powerZ e).factorial

def integerTermNorm (k : ℕ) (t : Power3 × ℤ) : ℤ :=
  if powerX t.1 ≤ k ∧ powerY t.1 ≤ k ∧ powerZ t.1 ≤ k then
    (integerPowerWeight t.1 : ℤ) * t.2^2 else 0

def integerPolyNorm (k : ℕ) (p : IntegerPoly3) : ℤ :=
  (p.map (integerTermNorm k)).sum

def integerPolyParity (e : Power3) (p : IntegerPoly3) : IntegerPoly3 :=
  p.map (fun t => (powerAdd e (powerAdd t.1 t.1), t.2))

def integerParityNorm (k : ℕ) (e : Power3) (p : IntegerPoly3) : ℤ :=
  integerPolyNorm k (integerPolyParity e p)

def integerPolyOrdered (p : IntegerPoly3) : Prop :=
  (p.map Prod.fst).Chain' (· < ·)

instance (p : IntegerPoly3) : Decidable (integerPolyOrdered p) := inferInstanceAs
  (Decidable ((p.map Prod.fst).Chain' (· < ·)))

theorem integerPolyOrdered_nodup (p : IntegerPoly3) (h : integerPolyOrdered p) :
    (p.map Prod.fst).Nodup := by
  have hp := List.chain'_iff_pairwise.mp h
  exact hp.imp (fun hab => ne_of_lt hab)

noncomputable def exponentWeight (e : Exponent3) : ℝ :=
  ∏ i : Fin 3, ((e i).factorial : ℝ)

theorem boundedFischerNorm_monomial (k : ℕ) (e : Exponent3) (a : ℝ) :
    boundedFischerNorm k (MvPolynomial.monomial e a) =
      if (∀ i, e i ≤ k) then exponentWeight e * a^2 else 0 := by
  classical
  by_cases h : ∀ i, e i ≤ k
  · rw [if_pos h]
    let α : Fin 3 → Fin (k + 1) := fun i => ⟨e i, Nat.lt_succ_of_le (h i)⟩
    have he : indexExponent α = e := by ext i; rfl
    unfold boundedFischerNorm
    rw [Finset.sum_eq_single α]
    · simp only [he, MvPolynomial.coeff_monomial, if_pos rfl]
      rfl
    · intro β _ hβα
      have hneq : e ≠ indexExponent β := by
        intro hb
        apply hβα
        funext i
        apply Fin.ext
        have hi := congrArg (fun m : Exponent3 => m i) hb
        exact hi.symm
      simp [MvPolynomial.coeff_monomial, hneq]
    · simp
  · rw [if_neg h]
    unfold boundedFischerNorm
    apply Finset.sum_eq_zero
    intro β _
    have hneq : e ≠ indexExponent β := by
      intro hb
      apply h
      intro i
      have hi := congrArg (fun m : Exponent3 => m i) hb
      calc
        e i = (β i).val := hi
        _ ≤ k := Nat.le_of_lt_succ (β i).isLt
    simp [MvPolynomial.coeff_monomial, hneq]

theorem integerTermNorm_semantics (k : ℕ) (e : Power3) (a : ℤ) :
    boundedFischerNorm k (MvPolynomial.monomial (powerExponent e) (a : ℝ)) =
      (integerTermNorm k (e, a) : ℝ) := by
  rw [boundedFischerNorm_monomial]
  have hb : (∀ i, powerExponent e i ≤ k) ↔
      powerX e ≤ k ∧ powerY e ≤ k ∧ powerZ e ≤ k := by
    simp [Fin.forall_fin_succ, powerExponent, powerCoord]
  simp only [hb]
  unfold integerTermNorm
  split_ifs
  · simp [exponentWeight, integerPowerWeight, Fin.prod_univ_succ, powerExponent, powerCoord]
    ring <;> simp
  · norm_num

theorem integerPolySemantics_coeff_zero (p : IntegerPoly3) (e : Power3)
    (h : e ∉ p.map Prod.fst) :
    MvPolynomial.coeff (powerExponent e) (integerPolySemantics p) = 0 := by
  induction p with
  | nil => simp [integerPolySemantics]
  | cons t p ih =>
    rcases t with ⟨f, a⟩
    have hh : e ≠ f ∧ e ∉ p.map Prod.fst := by simpa using h
    have hf : f ≠ e := hh.1.symm
    have ht : e ∉ p.map Prod.fst := hh.2
    have he : powerExponent f ≠ powerExponent e := fun hfe => hf (powerExponent_injective hfe)
    simp [integerPolySemantics, MvPolynomial.coeff_monomial, he, ih ht]

theorem integerPolyNorm_semantics (k : ℕ) (p : IntegerPoly3)
    (h : (p.map Prod.fst).Nodup) :
    boundedFischerNorm k (integerPolySemantics p) = (integerPolyNorm k p : ℝ) := by
  induction p with
  | nil => simp [integerPolySemantics, integerPolyNorm, boundedFischerNorm]
  | cons t p ih =>
    rcases t with ⟨e, a⟩
    have hn : e ∉ p.map Prod.fst := (List.nodup_cons.mp h).1
    have ht : (p.map Prod.fst).Nodup := (List.nodup_cons.mp h).2
    have hd : ∀ m, MvPolynomial.coeff m (MvPolynomial.monomial (powerExponent e) (a : ℝ)) *
        MvPolynomial.coeff m (integerPolySemantics p) = 0 := by
      intro m
      by_cases hm : powerExponent e = m
      · subst m
        rw [integerPolySemantics_coeff_zero p e hn]
        simp
      · simp [MvPolynomial.coeff_monomial, hm]
    rw [integerPolySemantics, boundedFischerNorm_add_disjoint _ _ _ hd,
      integerTermNorm_semantics, ih ht]
    simp [integerPolyNorm]

theorem integerPolyParity_semantics (e : Power3) (p : IntegerPoly3) :
    integerPolySemantics (integerPolyParity e p) =
      parityPolynomial (powerExponent e) (integerPolySemantics p) := by
  induction p with
  | nil => simp [integerPolyParity, integerPolySemantics, parityPolynomial]
  | cons t p ih =>
    rcases t with ⟨f, a⟩
    simp only [integerPolyParity, List.map_cons, integerPolySemantics] at ih ⊢
    rw [ih]
    simp only [parityPolynomial, map_add, mul_add, squareLift_monomial,
      MvPolynomial.monomial_mul, one_mul, powerExponent_add]

theorem integerPolyParity_nodup (e : Power3) (p : IntegerPoly3)
    (h : (p.map Prod.fst).Nodup) :
    ((integerPolyParity e p).map Prod.fst).Nodup := by
  have hinj : Function.Injective (fun f => powerAdd e (powerAdd f f)) := by
    intro f g hfg
    apply powerExponent_injective
    apply (parityEmbedding (powerExponent e)).injective
    have he := congrArg powerExponent hfg
    simpa only [powerExponent_add, parityEmbedding, Function.Embedding.coeFn_mk] using he
  have hn := h.map hinj
  simpa [integerPolyParity, List.map_map, Function.comp_def] using hn

theorem integerParityNorm_semantics (k : ℕ) (e : Power3) (p : IntegerPoly3)
    (h : (p.map Prod.fst).Nodup) :
    boundedFischerNorm k (parityPolynomial (powerExponent e) (integerPolySemantics p)) =
      (integerParityNorm k e p : ℝ) := by
  rw [← integerPolyParity_semantics]
  exact integerPolyNorm_semantics k _ (integerPolyParity_nodup e p h)

#print axioms integerPolyNorm_semantics
#print axioms integerParityNorm_semantics

end QPermanentResearch
