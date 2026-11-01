import QPermanentResearch.Fischer
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Ordinary multivariate coefficients, connected to the finite color sums. -/
open scoped BigOperators
namespace QPermanentResearch
noncomputable section

def colorExponent {n d : ℕ} (f : Fin n → Fin d) : Fin d →₀ ℕ :=
  ∑ i : Fin n, Finsupp.single (f i) 1

theorem colorExponent_apply {n d : ℕ} (f : Fin n → Fin d) (c : Fin d) :
    colorExponent f c = colorCount f c := by
  classical
  unfold colorExponent colorCount
  rw [Fintype.card_subtype, Finset.card_filter]
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]

def indexExponent {n d : ℕ} (α : Fin d → Fin (n + 1)) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun c => (α c).val)

@[simp] theorem indexExponent_apply {n d : ℕ}
    (α : Fin d → Fin (n + 1)) (c : Fin d) : indexExponent α c = (α c).val := by
  simp [indexExponent]

theorem colorExponent_eq_index_iff {n d : ℕ} (f : Fin n → Fin d)
    (α : Fin d → Fin (n + 1)) :
    colorExponent f = indexExponent α ↔ colorIndex f = α := by
  constructor
  · intro h
    funext c
    apply Fin.ext
    have hc := congrArg (fun s : Fin d →₀ ℕ => s c) h
    simpa [colorExponent_apply, colorIndex] using hc
  · intro h
    ext c
    have hc := congrArg Fin.val (congrFun h c)
    simpa [colorExponent_apply, colorIndex] using hc

def linearForm {d : ℕ} (v : Fin d → ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ c : Fin d, MvPolynomial.C (v c) * MvPolynomial.X c

def factorPolynomial {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ) :
    MvPolynomial (Fin d) ℝ := ∏ i : Fin n, linearForm (V i)

theorem factorPolynomial_colorExpansion {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) :
    factorPolynomial V = ∑ f : Fin n → Fin d,
      MvPolynomial.monomial (colorExponent f) (colorMonomial V f) := by
  classical
  unfold factorPolynomial linearForm
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [Finset.prod_mul_distrib, ← map_prod]
  change MvPolynomial.C (colorMonomial V f) *
    (∏ i : Fin n, MvPolynomial.monomial (Finsupp.single (f i) 1) (1 : ℝ)) = _
  rw [← MvPolynomial.monomial_sum_index]
  rfl

theorem factorPolynomial_coeff {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (α : Fin d → Fin (n + 1)) :
    MvPolynomial.coeff (indexExponent α) (factorPolynomial V) =
      colorCoefficient V α := by
  classical
  rw [factorPolynomial_colorExpansion]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  simp [colorCoefficient, eq_comm, colorExponent_eq_index_iff]

/-- The permanent is the actual factorial-weighted coefficient norm of the
product of the row linear forms, with no coefficient identity as a hypothesis. -/
theorem gram_permanent_polynomial {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) :
    qPermanent (V * V.transpose) 1 =
      ∑ α : Fin d → Fin (n + 1), colorWeight α *
        (MvPolynomial.coeff (indexExponent α) (factorPolynomial V)) ^ 2 := by
  simp only [factorPolynomial_coeff]
  exact gram_permanent_squares V

#print axioms gram_permanent_polynomial

end
end QPermanentResearch
