module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Polynomial
namespace PowerRank

abbrev Seq := ℕ → ℂ

/-- Fixed numeral proofs keep the definitions identical across modules. -/
instance instAtLeastTwo2 : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩
instance instAtLeastTwo3 : Nat.AtLeastTwo 3 := ⟨Nat.le_add_right 2 1⟩
instance instAtLeastTwo6 : Nat.AtLeastTwo 6 := ⟨Nat.le_add_right 2 4⟩
instance instAtLeastTwo7 : Nat.AtLeastTwo 7 := ⟨Nat.le_add_right 2 5⟩
instance instAtLeastTwo9 : Nat.AtLeastTwo 9 := ⟨Nat.le_add_right 2 7⟩

def shift : Module.End ℂ Seq where
  toFun u n := u (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def expPoly (lam : ℂ) (P : ℂ[X]) : Seq := fun n => P.eval (n : ℂ) * lam ^ n

def polyAction (q : ℂ[X]) : Module.End ℂ Seq := aeval shift q

def EventuallyAnnihilates (q : ℂ[X]) (u : Seq) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, polyAction q u n = 0

def AdmissibleAnnihilator (q : ℂ[X]) (u : Seq) : Prop :=
  q.Monic ∧ q.coeff 0 ≠ 0 ∧ EventuallyAnnihilates q u

def MinimalCharacteristic (χ : ℂ[X]) (u : Seq) : Prop :=
  AdmissibleAnnihilator χ u ∧ ∀ q, AdmissibleAnnihilator q u → χ ∣ q

/-- A polynomial vanishing on an integer tail is the zero polynomial. -/
theorem eq_zero_of_eval_nat_tail (P : ℂ[X]) (N : ℕ)
    (h : ∀ n ≥ N, P.eval (n : ℂ) = 0) : P = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := fun i : Fin (P.natDegree + 1) => ((N + i.val : ℕ) : ℂ))
  · intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel (Nat.cast_injective hij)
  · intro i
    exact h _ (Nat.le_add_right _ _)
  · simp

/-- The exponential-polynomial representation remains injective on every tail. -/
theorem expPoly_eventually_zero_iff (lam : ℂ) (hlam : lam ≠ 0) (P : ℂ[X]) :
    (∃ N, ∀ n ≥ N, expPoly lam P n = 0) ↔ P = 0 := by
  constructor
  · rintro ⟨N, hN⟩
    apply eq_zero_of_eval_nat_tail P N
    intro n hn
    exact (mul_eq_zero.mp (hN n hn)).resolve_right (pow_ne_zero n hlam)
  · rintro rfl
    exact ⟨0, by simp [expPoly]⟩

/-- The twisted shift acts on coefficient polynomials. -/
def coeffShift (lam : ℂ) : Module.End ℂ ℂ[X] where
  toFun P := C lam * P.comp (X + C 1)
  map_add' P Q := by simp [Polynomial.add_comp, mul_add]
  map_smul' a P := by
    simp only [smul_eq_C_mul, Polynomial.C_mul_comp, RingHom.id_apply]
    ring

def expPolyLinear (lam : ℂ) : ℂ[X] →ₗ[ℂ] Seq where
  toFun := expPoly lam
  map_add' P Q := by ext n; simp [expPoly, add_mul]
  map_smul' a P := by ext n; simp [expPoly, smul_eq_C_mul, mul_assoc]

/-- Exact intertwining, with the shift on the actual sequence index. -/
theorem expPoly_intertwines (lam : ℂ) :
    shift.comp (expPolyLinear lam) = (expPolyLinear lam).comp (coeffShift lam) := by
  ext P n
  simp [shift, expPolyLinear, expPoly, coeffShift,
    pow_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem expPoly_intertwines_pow (lam : ℂ) (k : ℕ) (P : ℂ[X]) :
    (shift ^ k) (expPoly lam P) = expPoly lam ((coeffShift lam ^ k) P) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ']
    change shift ((shift ^ k) (expPoly lam P)) =
      expPoly lam (coeffShift lam ((coeffShift lam ^ k) P))
    rw [ih]
    exact congrArg (fun L : ℂ[X] →ₗ[ℂ] Seq => L ((coeffShift lam ^ k) P))
      (expPoly_intertwines lam)

/-- Every recurrence polynomial acts through an actual coefficient polynomial. -/
theorem polyAction_expPoly (lam : ℂ) (q P : ℂ[X]) :
    polyAction q (expPoly lam P) = expPoly lam ((aeval (coeffShift lam) q) P) := by
  rw [polyAction, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, expPoly_intertwines_pow]
  change (∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i • expPolyLinear lam ((coeffShift lam ^ i) P)) =
    expPolyLinear lam (∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i • (coeffShift lam ^ i) P)
  simp only [map_sum, map_smul]

/-- Tail annihilation is equivalent to exact polynomial-kernel membership. -/
theorem eventual_annihilator_iff_coeff_kernel (lam : ℂ) (hlam : lam ≠ 0)
    (q P : ℂ[X]) :
    EventuallyAnnihilates q (expPoly lam P) ↔ (aeval (coeffShift lam) q) P = 0 := by
  unfold EventuallyAnnihilates
  simp_rw [polyAction_expPoly]
  exact expPoly_eventually_zero_iff lam hlam _

end PowerRank
