import QPermanentResearch.D2Compressed

/-!
Exact parity embedding and orthogonality for the compressed D2 polynomials.
All norms below are finite coefficient sums, with the same bounds as the
existing endpoint identity; no analytic Hilbert-space assumption is introduced.
-/

open scoped BigOperators
namespace QPermanentResearch
noncomputable section

abbrev Exponent3 := Fin 3 →₀ ℕ

def parityEmbedding (e : Exponent3) : Exponent3 ↪ Exponent3 where
  toFun m := e + (m + m)
  inj' := by
    intro m n h
    ext i
    have hi := congrArg (fun u : Exponent3 => u i) h
    simp only [Finsupp.add_apply] at hi
    omega

def parityPolynomial (e : Exponent3) (F : RealPoly3) : RealPoly3 :=
  MvPolynomial.monomial e 1 * squareLift F

theorem squareLift_monomial (m : Exponent3) (a : ℝ) :
    squareLift (MvPolynomial.monomial m a) = MvPolynomial.monomial (m + m) a := by
  classical
  rw [MvPolynomial.monomial_eq, map_mul, squareLift_C]
  simp only [Finsupp.prod, map_prod, map_pow, squareLift_X]
  have hprod : (∏ i ∈ m.support, ((MvPolynomial.X i : RealPoly3)^2)^(m i)) =
      (∏ i ∈ m.support, (MvPolynomial.X i : RealPoly3)^(m i))^2 := by
    simp only [← Finset.prod_pow, ← pow_mul, Nat.mul_comm]
  rw [hprod, MvPolynomial.prod_X_pow_eq_monomial, pow_two,
    MvPolynomial.monomial_mul, MvPolynomial.C_mul_monomial]
  simp

theorem parityPolynomial_eq_embDomain (e : Exponent3) (F : RealPoly3) :
    parityPolynomial e F = Finsupp.embDomain (parityEmbedding e) F := by
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
      rw [parityPolynomial, squareLift_monomial, MvPolynomial.monomial_mul]
      change MvPolynomial.monomial (e + (m + m)) (1 * a) =
        Finsupp.embDomain (parityEmbedding e) (Finsupp.single m a)
      rw [Finsupp.embDomain_single]
      simp only [one_mul]
      rfl
  | add F G hF hG =>
      simp only [parityPolynomial, map_add, mul_add] at hF hG ⊢
      rw [hF, hG, Finsupp.embDomain_add]

theorem parityPolynomial_coeff (e m : Exponent3) (F : RealPoly3) :
    MvPolynomial.coeff (parityEmbedding e m) (parityPolynomial e F) =
      MvPolynomial.coeff m F := by
  rw [parityPolynomial_eq_embDomain]
  exact Finsupp.embDomain_apply _ _ _

theorem parityPolynomial_coeff_zero (e m : Exponent3) (F : RealPoly3)
    (i : Fin 3) (h : m i % 2 ≠ e i % 2) :
    MvPolynomial.coeff m (parityPolynomial e F) = 0 := by
  rw [parityPolynomial_eq_embDomain]
  apply Finsupp.embDomain_notin_range
  rintro ⟨u, hu⟩
  apply h
  have hi := congrArg (fun v : Exponent3 => v i) hu
  simp only [parityEmbedding, Function.Embedding.coeFn_mk, Finsupp.add_apply] at hi
  omega

theorem parityPolynomial_coeff_disjoint (e f m : Exponent3) (F G : RealPoly3)
    (i : Fin 3) (h : e i % 2 ≠ f i % 2) :
    MvPolynomial.coeff m (parityPolynomial e F) *
      MvPolynomial.coeff m (parityPolynomial f G) = 0 := by
  by_cases hm : m i % 2 = e i % 2
  · rw [parityPolynomial_coeff_zero f m G i (hm ▸ h)]
    simp
  · rw [parityPolynomial_coeff_zero e m F i hm]
    simp

def boundedFischerNorm (k : ℕ) (F : RealPoly3) : ℝ :=
  ∑ α : Fin 3 → Fin (k + 1), colorWeight α *
    (MvPolynomial.coeff (indexExponent α) F)^2

theorem boundedFischerNorm_nonneg (k : ℕ) (F : RealPoly3) :
    0 ≤ boundedFischerNorm k F := by
  apply Finset.sum_nonneg
  intro α _
  apply mul_nonneg
  · unfold colorWeight
    exact Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)
  · exact sq_nonneg _

theorem boundedFischerNorm_add_disjoint (k : ℕ) (F G : RealPoly3)
    (h : ∀ m, MvPolynomial.coeff m F * MvPolynomial.coeff m G = 0) :
    boundedFischerNorm k (F + G) = boundedFischerNorm k F + boundedFischerNorm k G := by
  unfold boundedFischerNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [MvPolynomial.coeff_add]
  have hz := h (indexExponent α)
  have hs : (MvPolynomial.coeff (indexExponent α) F +
      MvPolynomial.coeff (indexExponent α) G)^2 =
      (MvPolynomial.coeff (indexExponent α) F)^2 +
      (MvPolynomial.coeff (indexExponent α) G)^2 := by nlinarith
  rw [hs, mul_add]

theorem parity_norm_add (k : ℕ) (e f : Exponent3) (F G : RealPoly3)
    (i : Fin 3) (h : e i % 2 ≠ f i % 2) :
    boundedFischerNorm k (parityPolynomial e F + parityPolynomial f G) =
      boundedFischerNorm k (parityPolynomial e F) +
      boundedFischerNorm k (parityPolynomial f G) :=
  boundedFischerNorm_add_disjoint k _ _
    (fun m => parityPolynomial_coeff_disjoint e f m F G i h)

def parity011 : Exponent3 := Finsupp.single 1 1 + Finsupp.single 2 1
def parity101 : Exponent3 := Finsupp.single 0 1 + Finsupp.single 2 1
def parity110 : Exponent3 := Finsupp.single 0 1 + Finsupp.single 1 1

@[simp] theorem parityPolynomial_zero (F : RealPoly3) :
    parityPolynomial 0 F = squareLift F := by simp [parityPolynomial]

@[simp] theorem parityPolynomial_011 (F : RealPoly3) :
    parityPolynomial parity011 F =
      MvPolynomial.X 1 * MvPolynomial.X 2 * squareLift F := by
  simp [parityPolynomial, parity011, MvPolynomial.X, MvPolynomial.monomial_mul]

@[simp] theorem parityPolynomial_101 (F : RealPoly3) :
    parityPolynomial parity101 F =
      MvPolynomial.X 0 * MvPolynomial.X 2 * squareLift F := by
  simp [parityPolynomial, parity101, MvPolynomial.X, MvPolynomial.monomial_mul]

@[simp] theorem parityPolynomial_110 (F : RealPoly3) :
    parityPolynomial parity110 F =
      MvPolynomial.X 0 * MvPolynomial.X 1 * squareLift F := by
  simp [parityPolynomial, parity110, MvPolynomial.X, MvPolynomial.monomial_mul]

def d2ProductNorm (k : ℕ) (S : D2State) : ℝ :=
  boundedFischerNorm k (squareLift S.F)

def d2ThreeNorm (k : ℕ) (S : D2State) : ℝ :=
  boundedFischerNorm k (parityPolynomial parity011 S.U01) +
  boundedFischerNorm k (squareLift S.U02) +
  boundedFischerNorm k (parityPolynomial parity110 S.U12)

def d2CorrectionNorm (k : ℕ) (S : D2State) : ℝ :=
  boundedFischerNorm k (parityPolynomial parity101 S.V01) +
  boundedFischerNorm k (squareLift S.V12)

theorem d2CorrectionNorm_nonneg (k : ℕ) (S : D2State) :
    0 ≤ d2CorrectionNorm k S :=
  add_nonneg (boundedFischerNorm_nonneg _ _) (boundedFischerNorm_nonneg _ _)

theorem d2_exact_endpoint {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (S : D2State) (h : D2Represents V S) :
    2 * qPermanentDerivative (V * V.transpose) 1 =
      (n.choose 2 : ℝ) * d2ProductNorm n S -
      (d2ThreeNorm (n - 2) S + d2CorrectionNorm (n - 2) S) := by
  rcases h with ⟨hF, h01, h02, h12⟩
  have hp01 := parity_norm_add (n - 2) parity011 parity101 S.U01 S.V01 1
    (by norm_num [parity011, parity101, Finsupp.single_apply, Fin.ext_iff])
  have hp12 := parity_norm_add (n - 2) parity110 0 S.U12 S.V12 1
    (by norm_num [parity110, Finsupp.single_apply, Fin.ext_iff])
  simp only [parityPolynomial_011, parityPolynomial_101] at hp01
  simp only [parityPolynomial_110, parityPolynomial_zero] at hp12
  rw [endpointDerivative_polynomial]
  simp only [wedgePolynomial3_coordinate, Fin.sum_univ_succ,
    wedgeCoordinateFirst, wedgeCoordinateSecond, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  change (n.choose 2 : ℝ) * boundedFischerNorm n (factorPolynomial V) -
    (boundedFischerNorm (n - 2) (coordinateWedgePolynomial V 0 1) +
      (boundedFischerNorm (n - 2) (coordinateWedgePolynomial V 0 2) +
        boundedFischerNorm (n - 2) (coordinateWedgePolynomial V 1 2))) = _
  rw [hF, h01, h02, h12]
  rw [hp01, hp12]
  simp only [d2ProductNorm, d2ThreeNorm, d2CorrectionNorm, parityPolynomial_zero,
    parityPolynomial_011, parityPolynomial_101, parityPolynomial_110]
  ring

theorem d2_negative_of_three_certificate {n : ℕ} (V : Matrix (Fin n) (Fin 3) ℝ)
    (S : D2State) (h : D2Represents V S)
    (hcert : (n.choose 2 : ℝ) * d2ProductNorm n S < d2ThreeNorm (n - 2) S) :
    qPermanentDerivative (V * V.transpose) 1 < 0 := by
  have hid := d2_exact_endpoint V S h
  have hc := d2CorrectionNorm_nonneg (n - 2) S
  linarith

theorem d2Word_negative_of_three_certificate (L : List (Fin 3 → ℝ))
    (hcert : ((d2WordSize L).choose 2 : ℝ) *
      d2ProductNorm (d2WordSize L) (d2Recurrence L) <
      d2ThreeNorm (d2WordSize L - 2) (d2Recurrence L)) :
    qPermanentDerivative (d2Word L * (d2Word L).transpose) 1 < 0 :=
  d2_negative_of_three_certificate _ _ (d2Recurrence_represents L) hcert

#print axioms parityPolynomial_eq_embDomain
#print axioms d2_exact_endpoint
#print axioms d2Word_negative_of_three_certificate

end
end QPermanentResearch
