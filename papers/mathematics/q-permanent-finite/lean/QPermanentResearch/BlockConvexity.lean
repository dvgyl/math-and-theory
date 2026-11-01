import QPermanentResearch.PairMinorIdentity
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
Finite block-order convexity for arbitrary weighted coefficient arrays.
The representative-selection averaging identity is proved, not assumed.
The final theorem constructs an actual permutation of the type labels.

This module formalizes the combinatorial and quadratic-norm core. Its arrays
may be instantiated with exterior-polynomial coefficients. The separate
identification of an arbitrary interleaved Gram word with these type-pair
arrays is not claimed as a theorem in this module.
-/

open scoped BigOperators
namespace QPermanentResearch
noncomputable section

theorem sum_two_pi_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → Type*) [∀ i, Fintype (X i)]
    (i j : ι) (hij : i ≠ j) (f : X i → X j → ℝ) :
    (Fintype.card (X i) : ℝ) * Fintype.card (X j) *
        (∑ ω : ∀ k, X k, f (ω i) (ω j)) =
      (Fintype.card (∀ k, X k) : ℝ) * ∑ x : X i, ∑ y : X j, f x y := by
  classical
  let Y := {k : ι // k ≠ i}
  let j' : Y := ⟨j, hij.symm⟩
  let Z := ∀ k : {k : Y // k ≠ j'}, X k.val.val
  let e : (∀ k, X k) ≃ X i × (X j × Z) :=
    (Equiv.piSplitAt i X).trans
      (Equiv.prodCongr (Equiv.refl (X i))
        (Equiv.piSplitAt j' (fun k : Y => X k.val)))
  have hsum : (∑ ω : ∀ k, X k, f (ω i) (ω j)) =
      (Fintype.card Z : ℝ) * ∑ x : X i, ∑ y : X j, f x y := by
    calc
      _ = ∑ t : X i × (X j × Z), f t.1 t.2.1 :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := by
        simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        simp only [Finset.mul_sum]
  have hcard : Fintype.card (∀ k, X k) =
      Fintype.card (X i) * (Fintype.card (X j) * Fintype.card Z) := by
    simpa only [Fintype.card_prod] using Fintype.card_congr e
  rw [hsum, hcard]
  push_cast
  ring

def weightedSquareSum {κ : Type*} [Fintype κ] (w x : κ → ℝ) : ℝ :=
  ∑ k : κ, w k * (x k)^2

theorem exists_weightedSquareSum_ge_of_average
    {Ω κ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype κ]
    (w x : κ → ℝ) (y : Ω → κ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (haverage : ∀ k, (Fintype.card Ω : ℝ) * x k = ∑ ω : Ω, y ω k) :
    ∃ ω : Ω, weightedSquareSum w x ≤ weightedSquareSum w (y ω) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hpoint : ∀ k, (Fintype.card Ω : ℝ) * (x k)^2 ≤
      ∑ ω : Ω, (y ω k)^2 := by
    intro k
    apply (mul_le_mul_left hcard).mp
    calc
      (Fintype.card Ω : ℝ) * (Fintype.card Ω * (x k)^2) =
          ((Fintype.card Ω : ℝ) * x k)^2 := by ring
      _ = (∑ ω : Ω, y ω k)^2 := by rw [haverage]
      _ ≤ (Fintype.card Ω : ℝ) * ∑ ω : Ω, (y ω k)^2 := by
        simpa only [Finset.card_univ] using
          (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun ω : Ω => y ω k))
  have hsum : (Fintype.card Ω : ℝ) * weightedSquareSum w x ≤
      ∑ ω : Ω, weightedSquareSum w (y ω) := by
    unfold weightedSquareSum
    rw [Finset.mul_sum, Finset.sum_comm]
    apply Finset.sum_le_sum
    intro k _
    calc
      (Fintype.card Ω : ℝ) * (w k * (x k)^2) =
          w k * ((Fintype.card Ω : ℝ) * (x k)^2) := by ring
      _ ≤ w k * ∑ ω : Ω, (y ω k)^2 := mul_le_mul_of_nonneg_left (hpoint k) (hw k)
      _ = ∑ ω : Ω, w k * (y ω k)^2 := Finset.mul_sum _ _ _
  have hsum' : (∑ _ω : Ω, weightedSquareSum w x) ≤
      ∑ ω : Ω, weightedSquareSum w (y ω) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
  obtain ⟨ω, _, hω⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum'
  exact ⟨ω, hω⟩

def orderSign (x y : ℕ) : ℝ := if x < y then 1 else -1

abbrev RepresentativeChoice {m : ℕ} (a : Fin m → ℕ) := ∀ i : Fin m, Fin (a i)

def interleavedCoefficients {m : ℕ} {κ : Type*}
    (a : Fin m → ℕ) (position : ∀ i : Fin m, Fin (a i) → ℕ)
    (K : Fin m → Fin m → κ → ℝ) (k : κ) : ℝ :=
  ∑ p ∈ rowPairs m,
    (∑ x : Fin (a p.1), ∑ y : Fin (a p.2),
      orderSign (position p.1 x) (position p.2 y)) * K p.1 p.2 k

def representativeCoefficients {m : ℕ} {κ : Type*}
    (a : Fin m → ℕ) (position : ∀ i : Fin m, Fin (a i) → ℕ)
    (K : Fin m → Fin m → κ → ℝ) (ω : RepresentativeChoice a) (k : κ) : ℝ :=
  ∑ p ∈ rowPairs m,
    ((a p.1 : ℝ) * a p.2 *
      orderSign (position p.1 (ω p.1)) (position p.2 (ω p.2))) * K p.1 p.2 k

def blockCoefficients {m : ℕ} {κ : Type*}
    (a : Fin m → ℕ) (K : Fin m → Fin m → κ → ℝ)
    (π : Equiv.Perm (Fin m)) (k : κ) : ℝ :=
  ∑ p ∈ rowPairs m,
    ((a p.1 : ℝ) * a p.2 *
      (if π.symm p.1 < π.symm p.2 then 1 else -1)) * K p.1 p.2 k

theorem representativeCoefficients_average {m : ℕ} {κ : Type*}
    (a : Fin m → ℕ) (position : ∀ i : Fin m, Fin (a i) → ℕ)
    (K : Fin m → Fin m → κ → ℝ) (k : κ) :
    (Fintype.card (RepresentativeChoice a) : ℝ) * interleavedCoefficients a position K k =
      ∑ ω : RepresentativeChoice a, representativeCoefficients a position K ω k := by
  classical
  unfold interleavedCoefficients representativeCoefficients
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2.ne
  have h := sum_two_pi_coordinates (fun i => Fin (a i)) p.1 p.2 hij
    (fun x y => orderSign (position p.1 x) (position p.2 y))
  simp only [Fintype.card_fin] at h
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [h]
  ring

theorem representativeCoefficients_is_block {m : ℕ} {κ : Type*}
    (a : Fin m → ℕ) (position : ∀ i : Fin m, Fin (a i) → ℕ)
    (K : Fin m → Fin m → κ → ℝ) (ω : RepresentativeChoice a)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x : Fin (a i), ∀ y : Fin (a j),
      position i x ≠ position j y) :
    ∃ π : Equiv.Perm (Fin m),
      representativeCoefficients a position K ω = blockCoefficients a K π := by
  classical
  let f : Fin m → ℕ := fun i => position i (ω i)
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact hdisjoint i j hne (ω i) (ω j) hij
  let π := Tuple.sort f
  have hs : StrictMono (f ∘ π) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hinj.comp π.injective)
  have horder : ∀ i j : Fin m, (π.symm i < π.symm j) ↔ f i < f j := by
    intro i j
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      (hs.lt_iff_lt (a := π.symm i) (b := π.symm j)).symm
  refine ⟨π, ?_⟩
  funext k
  unfold representativeCoefficients blockCoefficients orderSign
  simp only [horder]
  rfl

/-- Some contiguous block order has at least the weighted squared coefficient
norm of the interleaved order. No averaging identity is a hypothesis. -/
theorem exists_blockOrder_ge_interleaving {m : ℕ} {κ : Type*} [Fintype κ]
    (a : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (position : ∀ i : Fin m, Fin (a i) → ℕ)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x : Fin (a i), ∀ y : Fin (a j),
      position i x ≠ position j y)
    (K : Fin m → Fin m → κ → ℝ) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) :
    ∃ π : Equiv.Perm (Fin m),
      weightedSquareSum w (interleavedCoefficients a position K) ≤
        weightedSquareSum w (blockCoefficients a K π) := by
  letI : Nonempty (RepresentativeChoice a) := ⟨fun i => ⟨0, ha i⟩⟩
  obtain ⟨ω, hω⟩ := exists_weightedSquareSum_ge_of_average w
    (interleavedCoefficients a position K) (representativeCoefficients a position K)
    hw (representativeCoefficients_average a position K)
  obtain ⟨π, hπ⟩ := representativeCoefficients_is_block a position K ω hdisjoint
  exact ⟨π, hπ ▸ hω⟩

#print axioms exists_blockOrder_ge_interleaving

end
end QPermanentResearch
