import QuantumCHSH

/-!
Complete Fano coordinates and actual partial traces for arbitrary two-qubit
matrices. The completeness theorem assumes only Hermiticity and trace one.
-/

set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 16000

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace UnilateralCHSH.Quantum

@[simp] theorem qq_zero_ne_01 : (0 : QQ) ≠ (0,1) := by decide
@[simp] theorem qq_zero_ne_10 : (0 : QQ) ≠ (1,0) := by decide
@[simp] theorem qq_one_ne_01 : (1 : QQ) ≠ (0,1) := by decide
@[simp] theorem qq_one_ne_10 : (1 : QQ) ≠ (1,0) := by decide

def aliceBloch (ρ : State) (i : Fin 3) : ℝ :=
  (Matrix.trace (ρ * onAlice (pauli i))).re

def bobBloch (ρ : State) (j : Fin 3) : ℝ :=
  (Matrix.trace (ρ * onBob (pauli j))).re

def marginalAlice (ρ : State) : Matrix Q Q ℂ :=
  fun i j => ∑ k : Q, ρ (i,k) (j,k)

def marginalBob (ρ : State) : Matrix Q Q ℂ :=
  fun i j => ∑ k : Q, ρ (k,i) (k,j)

def fanoComplex (ρ : State) : State := fun p q =>
  (1/4:ℂ) * (Matrix.trace ρ * (if p=q then 1 else 0) +
    (∑ i : Fin 3, Matrix.trace (ρ * onAlice (pauli i)) * onAlice (pauli i) p q) +
    (∑ j : Fin 3, Matrix.trace (ρ * onBob (pauli j)) * onBob (pauli j) p q) +
    ∑ i : Fin 3, ∑ j : Fin 3, Matrix.trace (ρ * pauliPair i j) * pauliPair i j p q)

theorem fano_complex_complete (ρ : State) : ρ=fanoComplex ρ := by
  ext p q
  rcases p with ⟨p₀,p₁⟩
  rcases q with ⟨q₀,q₁⟩
  fin_cases p₀ <;> fin_cases p₁ <;> fin_cases q₀ <;> fin_cases q₁ <;>
    apply Complex.ext <;>
    simp [fanoComplex,onAlice,onBob,pauliPair,pauli,Matrix.trace,Matrix.diag,
      Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_three,
      Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem pauli_hermitian (i : Fin 3) : (pauli i).IsHermitian := by
  change (pauli i)ᴴ=pauli i
  ext p q
  fin_cases i <;> fin_cases p <;> fin_cases q <;> apply Complex.ext <;>
    simp [pauli,Matrix.conjTranspose_apply,Complex.star_def]

theorem pauli_trace (i : Fin 3) : Matrix.trace (pauli i)=0 := by
  fin_cases i <;> simp [pauli,Matrix.trace,Matrix.diag,Fin.sum_univ_two]

theorem fano_onAlice_hermitian (F : Matrix Q Q ℂ) (hF : F.IsHermitian) :
    (onAlice F).IsHermitian := by
  change (onAlice F)ᴴ=onAlice F
  ext p q
  by_cases h : p.2=q.2
  · simp only [Matrix.conjTranspose_apply,onAlice,if_pos h,if_pos h.symm]
    exact hF.apply p.1 q.1
  · simp [Matrix.conjTranspose_apply,onAlice,h,Ne.symm h]

theorem fano_onBob_hermitian (F : Matrix Q Q ℂ) (hF : F.IsHermitian) :
    (onBob F).IsHermitian := by
  change (onBob F)ᴴ=onBob F
  ext p q
  by_cases h : p.1=q.1
  · simp only [Matrix.conjTranspose_apply,onBob,if_pos h,if_pos h.symm]
    exact hF.apply p.2 q.2
  · simp [Matrix.conjTranspose_apply,onBob,h,Ne.symm h]

theorem pauliPair_hermitian (i j : Fin 3) : (pauliPair i j).IsHermitian := by
  change (pauliPair i j)ᴴ=pauliPair i j
  ext p q
  simp only [Matrix.conjTranspose_apply,pauliPair,StarMul.star_mul]
  rw [(pauli_hermitian i).apply p.1 q.1,(pauli_hermitian j).apply p.2 q.2]
  ring

theorem hermitian_product_trace_ofReal (ρ O : State)
    (hρ : ρ.IsHermitian) (hO : O.IsHermitian) :
    Matrix.trace (ρ*O)=((Matrix.trace (ρ*O)).re:ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using hermitian_product_trace_real ρ O hρ hO

/-- Every Hermitian trace-one two-qubit matrix has exactly its real Fano
coordinates. This is proved by a complete complex Pauli-basis identity. -/
theorem fano_complete (ρ : State) (hρ : ρ.IsHermitian) (ht : Matrix.trace ρ=1) :
    ρ=blochState (aliceBloch ρ) (bobBloch ρ) (correlation ρ) := by
  have ha (i : Fin 3) : Matrix.trace (ρ*onAlice (pauli i))=(aliceBloch ρ i:ℂ) :=
    hermitian_product_trace_ofReal ρ _ hρ (fano_onAlice_hermitian _ (pauli_hermitian i))
  have hb (j : Fin 3) : Matrix.trace (ρ*onBob (pauli j))=(bobBloch ρ j:ℂ) :=
    hermitian_product_trace_ofReal ρ _ hρ (fano_onBob_hermitian _ (pauli_hermitian j))
  have hD (i j : Fin 3) : Matrix.trace (ρ*pauliPair i j)=(correlation ρ i j:ℂ) :=
    hermitian_product_trace_ofReal ρ _ hρ (pauliPair_hermitian i j)
  calc
    ρ=fanoComplex ρ := fano_complex_complete ρ
    _=blochState (aliceBloch ρ) (bobBloch ρ) (correlation ρ) := by
      ext p q
      simp only [fanoComplex,blochState,ht,one_mul,ha,hb,hD,pauliPair,mul_assoc]

theorem blochState_trace (a b : Vec) (T : Mat3) : Matrix.trace (blochState a b T)=1 := by
  apply Complex.ext <;>
    simp [blochState,onAlice,onBob,pauli,Matrix.trace,Matrix.diag,
      Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_three,
      Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem aliceBloch_blochState (a b : Vec) (T : Mat3) (i : Fin 3) :
    aliceBloch (blochState a b T) i=a i := by
  fin_cases i <;>
    simp [aliceBloch,blochState,onAlice,onBob,pauli,Matrix.trace,Matrix.diag,
      Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_three,
      Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem bobBloch_blochState (a b : Vec) (T : Mat3) (j : Fin 3) :
    bobBloch (blochState a b T) j=b j := by
  fin_cases j <;>
    simp [bobBloch,blochState,onAlice,onBob,pauli,Matrix.trace,Matrix.diag,
      Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_three,
      Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem correlation_blochState (a b : Vec) (T : Mat3) (i j : Fin 3) :
    correlation (blochState a b T) i j=T i j := by
  fin_cases i <;> fin_cases j <;>
    simp [correlation,blochState,onAlice,onBob,pauliPair,pauli,Matrix.trace,Matrix.diag,
      Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_three,
      Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem trace_marginalAlice (ρ : State) : Matrix.trace (marginalAlice ρ)=Matrix.trace ρ := by
  simp [marginalAlice,Matrix.trace,Matrix.diag,Fintype.sum_prod_type]

theorem trace_marginalBob (ρ : State) : Matrix.trace (marginalBob ρ)=Matrix.trace ρ := by
  simp only [marginalBob,Matrix.trace,Matrix.diag,Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem marginalAlice_blochState (a b : Vec) (T : Mat3) :
    marginalAlice (blochState a b T)=(1/2:ℂ) • (1+realSpin a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [marginalAlice,blochState,onAlice,onBob,pauli,realSpin,complexSpin,
      Matrix.one_apply,Fin.sum_univ_two,Fin.sum_univ_three,Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem marginalBob_blochState (a b : Vec) (T : Mat3) :
    marginalBob (blochState a b T)=(1/2:ℂ) • (1+realSpin b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [marginalBob,blochState,onAlice,onBob,pauli,realSpin,complexSpin,
      Matrix.one_apply,Fin.sum_univ_two,Fin.sum_univ_three,Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem trace_onAlice (ρ : State) (F : Matrix Q Q ℂ) :
    Matrix.trace (ρ*onAlice F)=Matrix.trace (marginalAlice ρ*F) := by
  simp [marginalAlice,onAlice,Matrix.trace,Matrix.diag,Matrix.mul_apply,
    Fintype.sum_prod_type,Fin.sum_univ_two]
  ring

theorem trace_onBob (ρ : State) (F : Matrix Q Q ℂ) :
    Matrix.trace (ρ*onBob F)=Matrix.trace (marginalBob ρ*F) := by
  simp [marginalBob,onBob,Matrix.trace,Matrix.diag,Matrix.mul_apply,
    Fintype.sum_prod_type,Fin.sum_univ_two]
  ring

theorem aliceBloch_marginal (ρ : State) (i : Fin 3) :
    aliceBloch ρ i=(Matrix.trace (marginalAlice ρ*pauli i)).re := by
  rw [aliceBloch,trace_onAlice]

theorem bobBloch_marginal (ρ : State) (j : Fin 3) :
    bobBloch ρ j=(Matrix.trace (marginalBob ρ*pauli j)).re := by
  rw [bobBloch,trace_onBob]

theorem marginalAlice_filtered (ρ : State) (F : Matrix Q Q ℂ) :
    marginalAlice (filtered ρ F)=F*marginalAlice ρ*Fᴴ := by
  ext i j
  simp [marginalAlice,filtered,onAlice,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,Fin.sum_univ_two,Complex.star_def]
  ring

theorem aliceBloch_zero_of_marginal (ρ : State)
    (h : marginalAlice ρ=(1/2:ℂ) • (1 : Matrix Q Q ℂ)) :
    aliceBloch ρ=0 := by
  funext i
  rw [aliceBloch_marginal,h,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_smul,pauli_trace]
  simp

theorem canonical_of_marginal (ρ : State) (hρ : ρ.IsHermitian)
    (h : marginalAlice ρ=(1/2:ℂ) • (1 : Matrix Q Q ℂ)) :
    ρ=canonical (bobBloch ρ) (correlation ρ) := by
  have ht : Matrix.trace ρ=1 := by
    rw [←trace_marginalAlice,h]
    simp [Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  have he := fano_complete ρ hρ ht
  rw [aliceBloch_zero_of_marginal ρ h] at he
  exact he


theorem marginalAlice_posSemidef {ρ : State} (hρ : ρ.PosSemidef) :
    (marginalAlice ρ).PosSemidef := by
  have h₀ := hρ.submatrix (fun i : Q => (i,(0:Q)))
  have h₁ := hρ.submatrix (fun i : Q => (i,(1:Q)))
  have he : marginalAlice ρ =
      ρ.submatrix (fun i : Q => (i,0)) (fun i : Q => (i,0)) +
      ρ.submatrix (fun i : Q => (i,1)) (fun i : Q => (i,1)) := by
    ext i j
    change (∑ k : Q, ρ (i,k) (j,k))=ρ (i,0) (j,0)+ρ (i,1) (j,1)
    exact Fin.sum_univ_two _
  rw [he]
  exact h₀.add h₁

theorem marginalBob_posSemidef {ρ : State} (hρ : ρ.PosSemidef) :
    (marginalBob ρ).PosSemidef := by
  have h₀ := hρ.submatrix (fun i : Q => ((0:Q),i))
  have h₁ := hρ.submatrix (fun i : Q => ((1:Q),i))
  have he : marginalBob ρ =
      ρ.submatrix (fun i : Q => (0,i)) (fun i : Q => (0,i)) +
      ρ.submatrix (fun i : Q => (1,i)) (fun i : Q => (1,i)) := by
    ext i j
    change (∑ k : Q, ρ (k,i) (k,j))=ρ (0,i) (0,j)+ρ (1,i) (1,j)
    exact Fin.sum_univ_two _
  rw [he]
  exact h₀.add h₁

theorem bloch_alice_effect_posSemidef (a b : Vec) (T : Mat3)
    (hρ : (blochState a b T).PosSemidef) :
    (1+realSpin a).PosSemidef := by
  have h := marginalAlice_posSemidef hρ
  have he : marginalAlice (blochState a b T)+marginalAlice (blochState a b T)=
      1+realSpin a := by
    rw [marginalAlice_blochState,←add_smul]
    norm_num
  rw [←he]
  exact h.add h

theorem bloch_bob_effect_posSemidef (a b : Vec) (T : Mat3)
    (hρ : (blochState a b T).PosSemidef) :
    (1+realSpin b).PosSemidef := by
  have h := marginalBob_posSemidef hρ
  have he : marginalBob (blochState a b T)+marginalBob (blochState a b T)=
      1+realSpin b := by
    rw [marginalBob_blochState,←add_smul]
    norm_num
  rw [←he]
  exact h.add h

end UnilateralCHSH.Quantum
