module
public import MathAndTheory.Mathematics.QPermanent.GeneralNormalization
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Tactic.FunProp

@[expose] public section

namespace MathAndTheory.QPermanent

open scoped BigOperators Matrix
open Set

noncomputable section

theorem qPermanent_family_deriv (m : ℕ) (a d q : ℝ) :
    deriv (qPermanent (familyMatrix m a d)) q = familyDerivative m (a ^ 2) (d ^ 2) q := by
  have h : qPermanent (familyMatrix m a d) = familyPolynomial m (a ^ 2) (d ^ 2) := by
    funext r
    rw [qPermanent_family_formula]
    unfold familyPolynomial
    ring
  rw [h, family_deriv]

/-- The derivative and strict positivity inequalities remain valid for suitable
rational parameters. This uses density only in a two-dimensional parameter space. -/
theorem exists_rational_family_parameters (r : ℝ) (hr : 1 < r) :
    ∃ (m : ℕ) (a d : ℚ), (0 : ℝ) < d ∧ (a : ℝ) ^ 2 + 1 < (d : ℝ) ^ 2 ∧
      familyDerivative m ((a : ℝ) ^ 2) ((d : ℝ) ^ 2) r < 0 := by
  obtain ⟨m, hm, hb⟩ := exists_family_dimension hr
  let t := familyT m r
  have ht : 0 < t := familyT_pos m (by linarith)
  let U : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.1 ^ 2 + 1 < p.2 ^ 2 ∧
    familyDerivative m (p.1 ^ 2) (p.2 ^ 2) r < 0}
  have hcont : Continuous (fun p : ℝ × ℝ => familyDerivative m (p.1 ^ 2) (p.2 ^ 2) r) := by
    unfold familyDerivative
    fun_prop
  have hopen : IsOpen U := by
    have h₁ : IsOpen {p : ℝ × ℝ | 0 < p.2} :=
      isOpen_lt continuous_const continuous_snd
    have h₂ : IsOpen {p : ℝ × ℝ | p.1 ^ 2 + 1 < p.2 ^ 2} :=
      isOpen_lt
        (by fun_prop : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 + 1))
        (by fun_prop : Continuous (fun p : ℝ × ℝ => p.2 ^ 2))
    have h₃ : IsOpen {p : ℝ × ℝ |
        familyDerivative m (p.1 ^ 2) (p.2 ^ 2) r < 0} :=
      isOpen_lt hcont continuous_const
    exact h₁.inter (h₂.inter h₃)
  have hpoint : (Real.sqrt t, Real.sqrt (t + 2)) ∈ U := by
    refine ⟨Real.sqrt_pos.mpr (by linarith), ?_, ?_⟩
    · rw [Real.sq_sqrt ht.le, Real.sq_sqrt (by linarith : 0 ≤ t + 2)]
      linarith
    · rw [Real.sq_sqrt ht.le, Real.sq_sqrt (by linarith : 0 ≤ t + 2)]
      exact familyDerivative_negative hr m hb
  have hdense : DenseRange (fun p : ℚ × ℚ => ((p.1 : ℝ), (p.2 : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  obtain ⟨⟨a, d⟩, had⟩ := hdense.exists_mem_open hopen ⟨_, hpoint⟩
  exact ⟨m, a, d, had⟩

def integerFamilyCore (a d : ℚ) : Matrix (Fin 4) (Fin 4) ℤ :=
  let c : ℤ := a.den * d.den
  let aa : ℤ := a.num * d.den
  let dd : ℤ := d.num * a.den
  !![dd, 0, aa, c;
     0, dd, -c, aa;
     aa, -c, dd, 0;
     c, aa, 0, dd]

def integerFamilyMatrix (m : ℕ) (a d : ℚ) : Matrix (Fin (m + 4)) (Fin (m + 4)) ℤ :=
  (Matrix.fromBlocks (integerFamilyCore a d) 0 0
    ((a.den * d.den : ℤ) • (1 : Matrix (Fin m) (Fin m) ℤ))).submatrix
      (familyIndex m).symm (familyIndex m).symm

theorem integerFamilyCore_cast (a d : ℚ) (i j : Fin 4) :
    (integerFamilyCore a d i j : ℝ) =
      (a.den * d.den : ℝ) * familyCore (a : ℝ) (d : ℝ) i j := by
  have ha : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_nz
  have hd : (d.den : ℝ) ≠ 0 := by exact_mod_cast d.den_nz
  fin_cases i <;> fin_cases j <;>
    simp [integerFamilyCore, familyCore, Rat.cast_def] <;>
    field_simp [ha, hd] <;> ring

theorem integerFamilyMatrix_cast (m : ℕ) (a d : ℚ) :
    (fun i j => (integerFamilyMatrix m a d i j : ℝ)) =
      (a.den * d.den : ℝ) • familyMatrix m (a : ℝ) (d : ℝ) := by
  ext i j
  change ((Matrix.fromBlocks (integerFamilyCore a d) 0 0
      ((a.den * d.den : ℤ) • (1 : Matrix (Fin m) (Fin m) ℤ))
      ((familyIndex m).symm i) ((familyIndex m).symm j) : ℤ) : ℝ) =
    (a.den * d.den : ℝ) *
      Matrix.fromBlocks (familyCore (a : ℝ) (d : ℝ)) 0 0
        (1 : Matrix (Fin m) (Fin m) ℝ)
        ((familyIndex m).symm i) ((familyIndex m).symm j)
  cases (familyIndex m).symm i with
  | inl u =>
    cases (familyIndex m).symm j with
    | inl v =>
      exact integerFamilyCore_cast a d u v
    | inr v => simp
  | inr u =>
    cases (familyIndex m).symm j with
    | inl v => simp
    | inr v =>
      rw [Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₂,
        Matrix.smul_apply, smul_eq_mul]
      by_cases huv : u = v <;> simp [Matrix.one_apply, huv]

theorem qPermanent_smul {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) :
    qPermanent (c • A) q = c ^ n * qPermanent A q := by
  unfold qPermanent
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem deriv_qPermanent_smul {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) :
    deriv (qPermanent (c • A)) q = c ^ n * deriv (qPermanent A) q := by
  have hfun : qPermanent (c • A) = fun r => c ^ n * qPermanent A r := by
    funext r
    exact qPermanent_smul c A r
  rw [hfun, qPermanent_deriv]
  exact ((qPermanent_hasDerivAt A q).const_mul (c ^ n)).deriv

/-- At every real parameter above one, the counterexample can have integer entries. -/
theorem exists_integer_posDef_negative_qPermanent_derivative (r : ℝ) (hr : 1 < r) :
    ∃ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ),
      Matrix.PosDef (fun i j => (B i j : ℝ)) ∧
      deriv (qPermanent (fun i j => (B i j : ℝ))) r < 0 := by
  obtain ⟨m, a, d, hd, had, hderiv⟩ := exists_rational_family_parameters r hr
  have hc : (0 : ℝ) < a.den * d.den := by
    exact_mod_cast Nat.mul_pos a.den_pos d.den_pos
  have hA : (familyMatrix m (a : ℝ) (d : ℝ)).PosDef := familyMatrix_posDef m _ _ hd had
  refine ⟨m + 4, integerFamilyMatrix m a d, ?_, ?_⟩
  · rw [integerFamilyMatrix_cast]
    exact hA.smul hc
  · rw [integerFamilyMatrix_cast, deriv_qPermanent_smul, qPermanent_family_deriv]
    exact mul_neg_of_pos_of_neg (pow_pos hc _) hderiv

end

end MathAndTheory.QPermanent
