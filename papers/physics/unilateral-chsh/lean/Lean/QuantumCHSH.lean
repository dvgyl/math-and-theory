import QuantumFilters

/-!
Actual qubit spin observables and the operator-to-correlation CHSH bridge.
The identities hold for arbitrary complex two-qubit matrices; positivity is
needed only when interpreting the matrix as a quantum state.  No target
expectation identity is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace UnilateralCHSH.Quantum

/-- The tensor product of two actual real Bloch spin observables. -/
def spinProduct (a b : Vec) : State := onAlice (realSpin a) * onBob (realSpin b)

/-- The usual, unnormalized Bell operator. Its classical bound is two. -/
def bellOperator (a₀ a₁ b₀ b₁ : Vec) : State :=
  spinProduct a₀ b₀ + spinProduct a₀ b₁ + spinProduct a₁ b₀ - spinProduct a₁ b₁

/-- CHSH expectation divided by two, so the classical bound is one. -/
def bellExpectation (ρ : State) (a₀ a₁ b₀ b₁ : Vec) : ℝ :=
  (Matrix.trace (ρ * bellOperator a₀ a₁ b₀ b₁)).re / 2

theorem realSpin_hermitian (u : Vec) : (realSpin u).IsHermitian := by
  have h := affineFilter_hermitian u 0 1
  simpa [affineFilter] using h

theorem realSpin_trace (u : Vec) : Matrix.trace (realSpin u) = 0 := by
  simp [realSpin, complexSpin, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem realSpin_square (u : Vec) :
    realSpin u * realSpin u = (normSq u : ℂ) • (1 : Matrix Q Q ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [realSpin, complexSpin, normSq, dot, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  all_goals ring

theorem unit_realSpin_involution (u : Vec) (hu : normSq u = 1) :
    realSpin u * realSpin u = 1 := by
  rw [realSpin_square, hu]
  simp

theorem unit_realSpin_observable (u : Vec) (hu : normSq u = 1) :
    (realSpin u).IsHermitian ∧ realSpin u * realSpin u = 1 ∧
      Matrix.trace (realSpin u) = 0 :=
  ⟨realSpin_hermitian u, unit_realSpin_involution u hu, realSpin_trace u⟩


/-- A nontrivial dichotomic qubit observable in matrix form. -/
def IsSpinObservable (O : Matrix Q Q ℂ) : Prop :=
  O.IsHermitian ∧ O * O = 1 ∧ Matrix.trace O = 0

theorem traceless_hermitian_realSpin (O : Matrix Q Q ℂ)
    (hO : O.IsHermitian) (htrace : Matrix.trace O = 0) :
    ∃ u : Vec, O = realSpin u := by
  let u : Vec := ![(O 0 1).re,-(O 0 1).im,(O 0 0).re]
  have hd₀ := congrArg Complex.im (hO.apply 0 0)
  have hd₁ := congrArg Complex.im (hO.apply 1 1)
  have hor := congrArg Complex.re (hO.apply 1 0)
  have hoi := congrArg Complex.im (hO.apply 1 0)
  have htr := congrArg Complex.re htrace
  have hti := congrArg Complex.im htrace
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at hd₀ hd₁ hor hoi
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Complex.add_re,
    Complex.add_im, Complex.zero_re, Complex.zero_im] at htr hti
  refine ⟨u, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [u,realSpin,complexSpin,Complex.mul_re,Complex.mul_im,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;> linarith

theorem isSpinObservable_iff_unit_realSpin (O : Matrix Q Q ℂ) :
    IsSpinObservable O ↔ ∃ u : Vec, normSq u=1 ∧ O=realSpin u := by
  constructor
  · rintro ⟨hO,hsquare,htrace⟩
    obtain ⟨u,hu⟩ := traceless_hermitian_realSpin O hO htrace
    refine ⟨u, ?_, hu⟩
    rw [hu,realSpin_square] at hsquare
    have h := congrArg (fun M : Matrix Q Q ℂ => (M 0 0).re) hsquare
    simpa using h
  · rintro ⟨u,hu,rfl⟩
    exact unit_realSpin_observable u hu

theorem onAlice_mul_onBob_apply (F G : Matrix Q Q ℂ) (p q : QQ) :
    (onAlice F * onBob G) p q = F p.1 q.1 * G p.2 q.2 := by
  simp [Matrix.mul_apply, onAlice, onBob, Fintype.sum_prod_type, ite_mul, mul_ite]

theorem spinProduct_apply (a b : Vec) (p q : QQ) :
    spinProduct a b p q = realSpin a p.1 q.1 * realSpin b p.2 q.2 :=
  onAlice_mul_onBob_apply _ _ p q

theorem spinProduct_hermitian (a b : Vec) : (spinProduct a b).IsHermitian := by
  change (spinProduct a b)ᴴ = spinProduct a b
  ext p q
  rw [Matrix.conjTranspose_apply, spinProduct_apply, spinProduct_apply, StarMul.star_mul]
  have ha := congrArg (fun M : Matrix Q Q ℂ => M p.1 q.1) (realSpin_hermitian a).eq
  have hb := congrArg (fun M : Matrix Q Q ℂ => M p.2 q.2) (realSpin_hermitian b).eq
  change star (realSpin a q.1 p.1) = realSpin a p.1 q.1 at ha
  change star (realSpin b q.2 p.2) = realSpin b p.2 q.2 at hb
  rw [ha, hb]
  ring

theorem bellOperator_hermitian (a₀ a₁ b₀ b₁ : Vec) :
    (bellOperator a₀ a₁ b₀ b₁).IsHermitian :=
  (((spinProduct_hermitian a₀ b₀).add (spinProduct_hermitian a₀ b₁)).add
    (spinProduct_hermitian a₁ b₀)).sub (spinProduct_hermitian a₁ b₁)

theorem spinProduct_pauli_expansion (a b : Vec) :
    spinProduct a b = ∑ i : Fin 3, ∑ j : Fin 3,
      ((a i * b j : ℝ) : ℂ) • pauliPair i j := by
  ext p q
  rw [spinProduct_apply]
  rcases p with ⟨p₀,p₁⟩
  rcases q with ⟨q₀,q₁⟩
  fin_cases p₀ <;> fin_cases p₁ <;> fin_cases q₀ <;> fin_cases q₁ <;> apply Complex.ext <;>
    simp [realSpin, complexSpin, pauliPair, pauli, Fin.sum_univ_three,
      Complex.mul_re, Complex.mul_im]
  all_goals ring

theorem spinProduct_expectation (ρ : State) (a b : Vec) :
    (Matrix.trace (ρ * spinProduct a b)).re = dot a (matVec (correlation ρ) b) := by
  rw [spinProduct_pauli_expansion]
  simp only [Finset.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  simp only [Fin.sum_univ_three, correlation, dot, matVec]
  ring

theorem bell_expectation_correlation (ρ : State) (a₀ a₁ b₀ b₁ : Vec) :
    bellExpectation ρ a₀ a₁ b₀ b₁ =
      (dot a₀ (matVec (correlation ρ) b₀) + dot a₀ (matVec (correlation ρ) b₁) +
        dot a₁ (matVec (correlation ρ) b₀) - dot a₁ (matVec (correlation ρ) b₁))/2 := by
  unfold bellExpectation bellOperator
  rw [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_add,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add]
  simp only [Complex.add_re, Complex.sub_re, spinProduct_expectation]

theorem hermitian_product_trace_real (ρ O : State)
    (hρ : ρ.IsHermitian) (hO : O.IsHermitian) :
    (Matrix.trace (ρ * O)).im = 0 := by
  have hs : star (Matrix.trace (ρ * O)) = Matrix.trace (ρ * O) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hO.eq, hρ.eq,
      Matrix.trace_mul_comm]
  have hi := congrArg Complex.im hs
  change -(Matrix.trace (ρ * O)).im = (Matrix.trace (ρ * O)).im at hi
  linarith

theorem bell_expectation_trace_real (ρ : State) (a₀ a₁ b₀ b₁ : Vec)
    (hρ : ρ.IsHermitian) :
    (Matrix.trace (ρ * bellOperator a₀ a₁ b₀ b₁)).im = 0 :=
  hermitian_product_trace_real ρ _ hρ (bellOperator_hermitian a₀ a₁ b₀ b₁)

end UnilateralCHSH.Quantum
