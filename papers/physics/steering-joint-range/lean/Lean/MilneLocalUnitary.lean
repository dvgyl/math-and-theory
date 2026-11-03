import MilneAlignedState

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 2000
noncomputable section
namespace Milne

theorem rigidity_unitary_mul_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    (U : Matrix ι ι ℂ)*(U : Matrix ι ι ℂ)ᴴ = 1 := by
  simpa only [← Matrix.star_eq_conjTranspose] using unitary.coe_mul_star_self U


theorem rigidity_unitary_adjoint_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    (U : Matrix ι ι ℂ)ᴴ*(U : Matrix ι ι ℂ) = 1 := by
  simpa only [← Matrix.star_eq_conjTranspose] using unitary.coe_star_mul_self U


def rigidityConj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (U : Matrix ι ι ℂ)*A*(U : Matrix ι ι ℂ)ᴴ


theorem rigidityConj_hermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (rigidityConj U A).IsHermitian := by
  change (rigidityConj U A)ᴴ = rigidityConj U A
  simp [rigidityConj,Matrix.conjTranspose_mul,hA.eq,mul_assoc]


theorem rigidityConj_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    Matrix.trace (rigidityConj U A) = Matrix.trace A := by
  rw [rigidityConj,Matrix.trace_mul_cycle,rigidity_unitary_adjoint_mul,one_mul]


theorem rigidityConj_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    rigidityConj (U*V) A = rigidityConj U (rigidityConj V A) := by
  simp only [rigidityConj,Matrix.UnitaryGroup.mul_val,Matrix.conjTranspose_mul]
  noncomm_ring


theorem rigidityConj_trace_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    Matrix.trace (rigidityConj U A*rigidityConj U A) = Matrix.trace (A*A) := by
  have hm : rigidityConj U A*rigidityConj U A = rigidityConj U (A*A) := by
    unfold rigidityConj
    calc
      ((U:Matrix ι ι ℂ)*A*(U:Matrix ι ι ℂ)ᴴ)*
          ((U:Matrix ι ι ℂ)*A*(U:Matrix ι ι ℂ)ᴴ) =
        (U:Matrix ι ι ℂ)*A*((U:Matrix ι ι ℂ)ᴴ*(U:Matrix ι ι ℂ))*A*
          (U:Matrix ι ι ℂ)ᴴ := by noncomm_ring
      _ = (U:Matrix ι ι ℂ)*(A*A)*(U:Matrix ι ι ℂ)ᴴ := by
        rw [rigidity_unitary_adjoint_mul]
        noncomm_ring
  rw [hm,rigidityConj_trace]


theorem rigidityConj_blochSq (U : Matrix.unitaryGroup Q ℂ)
    {A : Matrix Q Q ℂ} (hA : A.IsHermitian) :
    blochSq (rigidityConj U A) = blochSq A := by
  rw [blochSq_trace_identity (rigidityConj_hermitian U hA),
    blochSq_trace_identity hA,rigidityConj_trace_square,rigidityConj_trace]


theorem onAlice_one : onAlice (1 : Matrix Q Q ℂ) = (1 : CMatrix) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [onAlice,Matrix.one_apply,Prod.ext_iff]


theorem onAlice_mul (F G : Matrix Q Q ℂ) :
    onAlice (F*G) = onAlice F*onAlice G := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [onAlice,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two]


theorem onAlice_conjTranspose (F : Matrix Q Q ℂ) :
    onAlice Fᴴ = (onAlice F)ᴴ := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [onAlice,Matrix.conjTranspose_apply]


theorem onAlice_onBob_commute (F G : Matrix Q Q ℂ) :
    onAlice F*onBob G = onBob G*onAlice F := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [onAlice,onBob,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two]
  all_goals ring


def aliceUnitary (U : Matrix.unitaryGroup Q ℂ) : Matrix.unitaryGroup QQ ℂ :=
  ⟨onAlice (U:Matrix Q Q ℂ), Matrix.mem_unitaryGroup_iff.mpr (by
    change onAlice (U:Matrix Q Q ℂ)*(onAlice (U:Matrix Q Q ℂ))ᴴ = 1
    rw [← onAlice_conjTranspose,← onAlice_mul,rigidity_unitary_mul_adjoint,onAlice_one])⟩


def bobUnitary (V : Matrix.unitaryGroup Q ℂ) : Matrix.unitaryGroup QQ ℂ :=
  ⟨onBob (V:Matrix Q Q ℂ), Matrix.mem_unitaryGroup_iff.mpr (by
    change onBob (V:Matrix Q Q ℂ)*(onBob (V:Matrix Q Q ℂ))ᴴ = 1
    rw [← onBob_conjTranspose,← onBob_mul,rigidity_unitary_mul_adjoint,onBob_one])⟩


theorem aliceUnitary_mul (U V : Matrix.unitaryGroup Q ℂ) :
    aliceUnitary (U*V) = aliceUnitary U*aliceUnitary V := by
  apply Subtype.ext
  exact onAlice_mul _ _


theorem bobUnitary_mul (U V : Matrix.unitaryGroup Q ℂ) :
    bobUnitary (U*V) = bobUnitary U*bobUnitary V := by
  apply Subtype.ext
  exact onBob_mul _ _


theorem aliceUnitary_bobUnitary_commute (U V : Matrix.unitaryGroup Q ℂ) :
    aliceUnitary U*bobUnitary V = bobUnitary V*aliceUnitary U := by
  apply Subtype.ext
  exact onAlice_onBob_commute _ _


def localConjugate (U V : Matrix.unitaryGroup Q ℂ) (M : CMatrix) : CMatrix :=
  rigidityConj (aliceUnitary U*bobUnitary V) M


theorem localConjugate_alice_bob (U V : Matrix.unitaryGroup Q ℂ) (M : CMatrix) :
    localConjugate U V M =
      onAlice (U:Matrix Q Q ℂ)*(onBob (V:Matrix Q Q ℂ)*M*onBob (V:Matrix Q Q ℂ)ᴴ)*
        onAlice (U:Matrix Q Q ℂ)ᴴ := by
  rw [localConjugate,rigidityConj_mul]
  simp only [rigidityConj,aliceUnitary,bobUnitary,← onAlice_conjTranspose,
    ← onBob_conjTranspose]


theorem localConjugate_bob_alice (U V : Matrix.unitaryGroup Q ℂ) (M : CMatrix) :
    localConjugate U V M =
      onBob (V:Matrix Q Q ℂ)*(onAlice (U:Matrix Q Q ℂ)*M*onAlice (U:Matrix Q Q ℂ)ᴴ)*
        onBob (V:Matrix Q Q ℂ)ᴴ := by
  rw [localConjugate,aliceUnitary_bobUnitary_commute,rigidityConj_mul]
  simp only [rigidityConj,aliceUnitary,bobUnitary,← onAlice_conjTranspose,
    ← onBob_conjTranspose]


theorem localConjugate_comp (U V U' V' : Matrix.unitaryGroup Q ℂ) (M : CMatrix) :
    localConjugate U' V' (localConjugate U V M) =
      localConjugate (U'*U) (V'*V) M := by
  have hg : (aliceUnitary U'*bobUnitary V')*(aliceUnitary U*bobUnitary V) =
      aliceUnitary (U'*U)*bobUnitary (V'*V) := by
    calc
      _ = aliceUnitary U'*(bobUnitary V'*aliceUnitary U)*bobUnitary V := by simp [mul_assoc]
      _ = aliceUnitary U'*(aliceUnitary U*bobUnitary V')*bobUnitary V := by
        rw [← aliceUnitary_bobUnitary_commute U V']
      _ = (aliceUnitary U'*aliceUnitary U)*(bobUnitary V'*bobUnitary V) := by simp [mul_assoc]
      _ = _ := by rw [← aliceUnitary_mul,← bobUnitary_mul]
  unfold localConjugate
  rw [← rigidityConj_mul,hg]


theorem partialA_alice_filter (M : CMatrix) (F G : Matrix Q Q ℂ) :
    partialA (onAlice F*M*onAlice G) = F*partialA M*G := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialA,onAlice,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two]
  all_goals ring


theorem localConjugate_partialA (U V : Matrix.unitaryGroup Q ℂ) (M : CMatrix) :
    partialA (localConjugate U V M) = rigidityConj U (partialA M) := by
  rw [localConjugate_alice_bob,partialA_alice_filter,partialA_bob_cycle,
    rigidity_unitary_adjoint_mul,onBob_one,mul_one]
  rfl


theorem localConjugate_partialB (U V : Matrix.unitaryGroup Q ℂ) (M : CMatrix) :
    partialB (localConjugate U V M) = rigidityConj V (partialB M) := by
  rw [localConjugate_alice_bob,partialB_alice_cycle,
    rigidity_unitary_adjoint_mul,onAlice_one,mul_one,partialB_filter]
  rfl


theorem localConjugate_density (U V : Matrix.unitaryGroup Q ℂ)
    (M : CMatrix) (hM : Density M) : Density (localConjugate U V M) := by
  refine ⟨hM.1.mul_mul_conjTranspose_same
    ((aliceUnitary U*bobUnitary V : Matrix.unitaryGroup QQ ℂ):CMatrix),?_⟩
  rw [localConjugate,rigidityConj_trace,hM.2]


theorem localConjugate_canonical (U V : Matrix.unitaryGroup Q ℂ)
    (M : CMatrix) (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ)) :
    partialB (localConjugate U V M) = (1/2:ℂ) • (1 : Matrix Q Q ℂ) := by
  rw [localConjugate_partialB,hB,rigidityConj]
  simp [Matrix.mul_smul,Matrix.smul_mul,rigidity_unitary_mul_adjoint]


theorem localConjugate_center (U V : Matrix.unitaryGroup Q ℂ)
    (M : CMatrix) (hM : Density M) : center (localConjugate U V M) = center M := by
  rw [center,center,localConjugate_partialA,
    rigidityConj_blochSq U (partialA_psd hM.1).1]


theorem localConjugate_correlationSq (U V : Matrix.unitaryGroup Q ℂ)
    (M : CMatrix) (hM : Density M) :
    correlationSq (localConjugate U V M) = correlationSq M := by
  have hN := localConjugate_density U V M hM
  rw [correlationSq_bloch _ hN,correlationSq_bloch M hM,
    localConjugate_partialA,localConjugate_partialB,
    rigidityConj_blochSq U (partialA_psd hM.1).1,
    rigidityConj_blochSq V (partialB_psd hM.1).1]
  change 4*(Matrix.trace (rigidityConj (aliceUnitary U*bobUnitary V) M*
    rigidityConj (aliceUnitary U*bobUnitary V) M)).re-1-
      blochSq (partialA M)-blochSq (partialB M) = _
  rw [rigidityConj_trace_square]

end Milne

#print axioms Milne.localConjugate_density
#print axioms Milne.localConjugate_center
#print axioms Milne.localConjugate_correlationSq
