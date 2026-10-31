import TowerForwardRoots
import Mathlib.FieldTheory.Extension

/-!
# Embedding abstract finite AS towers into the Hahn field

The target Hahn field is not assumed algebraically closed.  Its explicit
Artin--Schreier roots make each AS polynomial split; the actual minimal
polynomial divides that polynomial.  Mathlib's relative extension-of-lifts
theorem then extends a partial embedding at every step of the finite tower.

The splitting/minpoly/lift induction is a prior construction, including
Yijun Yuan's `TrustworthyKedlaya/Kedlaya/TowerEmbedding.lean` at commit
`f97be4372713e25a21603dec26706d8bb0cd9d24` (first file release 2026-09-06).
That implementation treats finite Galois extensions of Fpbar((t)) with
uniformly periodic image. Its source was inspected after this module's
initial draft; no originality is claimed for the embedding method.
-/

noncomputable section
set_option maxHeartbeats 1200000
attribute [local instance 2000] HahnSeries.instAlgebra
attribute [local instance 3000] Algebra.id

open HahnSeries IntermediateField Polynomial Set

namespace NTCThird

-- Choose the canonical base action directly. The generic inherited-subfield
-- instance otherwise searches for an irrelevant Hahn-algebra structure on E.
noncomputable local instance (priority := 4000) forwardIntermediateAlgebra
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) : Algebra F L := L.toSubalgebra.algebra

theorem artinSchreier_linearized_polynomial
    {R : Type*} [Field R] (p : ℕ) :
    linearized p {0, 1} (fun i : ℕ => if i = 0 then (-1 : R) else 1) =
      Polynomial.X ^ p - Polynomial.X := by
  simp [linearized, ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

/-- Every actual Hahn coefficient has an AS root, obtained from the
explicit negative, constant and positive Hahn sums. -/
theorem exists_artinSchreier_hahn_root
    {k : Type*} [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (a : HahnSeries ℚ k) :
    ∃ z : HahnSeries ℚ k, z ^ p - z = a := by
  obtain ⟨z, hz, _⟩ := exists_asRoot_supportClosureIn p (⊤ : AddSubgroup ℝ)
    (fun _ _ => trivial) a (by intro q hq; trivial)
  exact ⟨z, hz⟩

/-- The minimal polynomial of an AS generator splits under every actual
embedding of its coefficient field into the Hahn field. -/
theorem minpoly_splits_hahn_of_artinSchreier
    {k E : Type*} [Field k] [IsAlgClosed k] [Field E]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (K : IntermediateField k (HahnSeries ℚ k)) [Algebra K E]
    (L : IntermediateField K E) (f : L →ₐ[K] HahnSeries ℚ k)
    (x : E) (a : L) (hx : x ^ p - x = algebraMap L E a) :
    IsIntegral L x ∧ ((minpoly L x).map f.toRingHom).Splits := by
  letI : Algebra K (HahnSeries ℚ k) := K.toAlgebra
  letI : Algebra L (HahnSeries ℚ k) := f.toRingHom.toAlgebra
  letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k L (HahnSeries ℚ k) := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k (HahnSeries ℚ k) c = f (algebraMap K L (algebraMap k K c))
    rw [f.commutes]
    exact IsScalarTower.algebraMap_apply k K (HahnSeries ℚ k) c
  let P : L[X] := Polynomial.X ^ p - Polynomial.X - Polynomial.C a
  have hP : P ≠ 0 := by
    have hone : (1 : L) ≠ 0 := by
      intro h
      exact (one_ne_zero : (1 : E) ≠ 0)
        (congrArg (fun y : L => (y : E)) h)
    have h := linearized_sub_C_ne_zero_of_nonzero p
      (Fact.out : p.Prime).two_le {0, 1}
      (fun i : ℕ => if i = 0 then (-1 : L) else 1)
      ⟨0, Finset.mem_insert_self _ _, by
        change (-1 : L) ≠ 0
        exact neg_ne_zero.mpr hone⟩ a
    simpa only [artinSchreier_linearized_polynomial, P] using h
  have hxP : aeval x P = 0 := by
    simp only [P, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact sub_eq_zero.mpr hx
  have hint : IsIntegral L x := (show IsAlgebraic L x from ⟨P, hP, hxP⟩).isIntegral
  obtain ⟨z, hz⟩ := exists_artinSchreier_hahn_root p (f a)
  have hzeval : aeval z (linearized p {0, 1}
      (fun i : ℕ => if i = 0 then (-1 : k) else 1)) =
        algebraMap L (HahnSeries ℚ k) a := by
    rw [aeval_artinSchreier_linearized]
    exact hz
  have hsplit : (P.map f.toRingHom).Splits := by
    have h := linearized_splits_of_root p {0, 1}
      (fun i : ℕ => if i = 0 then (-1 : k) else 1) z a hzeval
    simpa only [artinSchreier_linearized_polynomial, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      RingHom.algebraMap_toAlgebra, P] using h
  exact ⟨hint, hsplit.of_dvd (Polynomial.map_ne_zero hP)
    (Polynomial.map_dvd f.toRingHom (minpoly.dvd L x hxP))⟩

/-- An abstract finite tower obtained by adjoining AS roots embeds over
the actual base into its Hahn field. The tower steps use the ordinary
supremum/adjoin of actual intermediate fields; no valuation or algebraic
closedness premise on the Hahn field is assumed. -/
theorem exists_embedding_hahn_of_abstract_asTower
    {k E : Type*} [Field k] [IsAlgClosed k] [Field E]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (K : IntermediateField k (HahnSeries ℚ k)) [Algebra K E]
    (N : ℕ) (F : ℕ → IntermediateField K E) (x : ℕ → E)
    (hF0 : F 0 = ⊥) (hFN : F N = ⊤)
    (hstep : ∀ i < N, ∃ a : F i,
      x i ^ p - x i = (a : E) ∧ F (i + 1) = F i ⊔ K⟮x i⟯) :
    Nonempty (E →ₐ[K] HahnSeries ℚ k) := by
  classical
  letI : Algebra K (HahnSeries ℚ k) := K.toAlgebra
  have hind : ∀ n ≤ N, ∃ L : IntermediateField.Lifts K E (HahnSeries ℚ k),
      F n ≤ L.carrier := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨⊥, ?_⟩
      rw [hF0]
      exact bot_le
    | succ n ih =>
      intro hn
      obtain ⟨L, hL⟩ := ih (Nat.le_trans (Nat.le_succ n) hn)
      obtain ⟨a, ha, hnext⟩ := hstep n (Nat.lt_of_succ_le hn)
      let aL : L.carrier := ⟨(a : E), hL a.property⟩
      have hxL : x n ^ p - x n = algebraMap L.carrier E aL := ha
      obtain ⟨hint, hsplit⟩ := minpoly_splits_hahn_of_artinSchreier
        p K L.carrier L.emb (x n) aL hxL
      obtain ⟨L', hLL', hx⟩ := L.exists_lift_of_splits' hint hsplit
      refine ⟨L', ?_⟩
      rw [hnext]
      exact sup_le (hL.trans hLL'.1) (IntermediateField.adjoin_simple_le_iff.mpr hx)
  obtain ⟨L, hL⟩ := hind N le_rfl
  have htop : L.carrier = ⊤ := top_unique (hFN ▸ hL)
  let e : L.carrier ≃ₐ[K] E := (IntermediateField.equivOfEq htop).trans
    (IntermediateField.topEquiv : (⊤ : IntermediateField K E) ≃ₐ[K] E)
  exact ⟨L.emb.comp e.symm.toAlgHom⟩

end NTCThird
