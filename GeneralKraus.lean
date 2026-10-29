module
public import ConditionalHockey
public import Mathlib.Data.Matrix.Basis


@[expose] public section

/-! Finite rectangular Kraus families define actual CPTP maps. -/
open Matrix
open scoped BigOperators ComplexOrder
open ConditionalHockey

namespace GeneralKraus
noncomputable section

variable {A B C R ι κ : Type}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
  [Fintype ι] [Fintype κ]

def krausMap (K : ι → Matrix B A ℂ) : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ where
  toFun X := ∑ i, K i * X * (K i)ᴴ
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' z X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
    rfl

omit [DecidableEq A] [Fintype B] [DecidableEq B] in
@[simp] theorem krausMap_apply [DecidableEq A] [Fintype B] [DecidableEq B] (K : ι → Matrix B A ℂ) (X : Matrix A A ℂ) :
    krausMap K X = ∑ i, K i * X * (K i)ᴴ := rfl

/-- The identity-reference lift of a rectangular matrix. -/
def lift (K : Matrix B A ℂ) : Matrix (R × B) (R × A) ℂ :=
  fun r s => if r.1 = s.1 then K r.2 s.2 else 0

def block (X : Matrix (R × A) (R × A) ℂ) (r s : R) : Matrix A A ℂ :=
  fun a b => X (r,a) (s,b)

omit [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem lift_sandwich_entry [DecidableEq A] [Fintype B] [DecidableEq B] (K : Matrix B A ℂ)
    (X : Matrix (R × A) (R × A) ℂ) (r s : R × B) :
    (lift (R:=R) K * X * (lift (R:=R) K)ᴴ) r s =
      (K * block X r.1 s.1 * Kᴴ) r.2 s.2 := by
  simp [lift, block, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
    apply_ite, Finset.sum_add_distrib]

theorem amplify_kraus (K : ι → Matrix B A ℂ)
    (X : Matrix (R × A) (R × A) ℂ) :
    amplify (krausMap K) X = ∑ i, lift (R:=R) (K i) * X * (lift (R:=R) (K i))ᴴ := by
  ext r s
  change krausMap K (block X r.1 s.1) r.2 s.2 = _
  rw [krausMap_apply]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (lift_sandwich_entry (K i) X r s).symm

theorem completely_positive (K : ι → Matrix B A ℂ)
    (X : Matrix (R × A) (R × A) ℂ) (hX : X.PosSemidef) :
    (amplify (krausMap K) X).PosSemidef := by
  rw [amplify_kraus]
  exact Finset.sum_induction _ _ (fun P Q hP hQ => hP.add hQ)
    Matrix.PosSemidef.zero (fun i _ => hX.mul_mul_conjTranspose_same (lift (K i)))

omit [DecidableEq B] in
theorem trace_preserving [DecidableEq B] (K : ι → Matrix B A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (X : Matrix A A ℂ) :
    (krausMap K X).trace = X.trace := by
  simp only [krausMap_apply, Matrix.trace_sum]
  calc
    (∑ i, (K i * X * (K i)ᴴ).trace) =
        ∑ i, ((K i)ᴴ * K i * X).trace := by
      apply Finset.sum_congr rfl
      intro i _
      exact Matrix.trace_mul_cycle (K i) X (K i)ᴴ
    _ = ((∑ i, (K i)ᴴ * K i) * X).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = X.trace := by rw [hK, Matrix.one_mul]

/-- A genuine CPTP map, with complete positivity checked at every finite reference. -/
def channel (K : ι → Matrix B A ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) : QuantumChannel A B where
  map := krausMap K
  trace_preserving := trace_preserving K hK
  completely_positive := by
    intro S _ _ X hX
    exact completely_positive K X hX

@[simp] theorem channel_map (K : ι → Matrix B A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (X : Matrix A A ℂ) :
    (channel K hK).map X = ∑ i, K i * X * (K i)ᴴ := rfl

omit [Fintype A] [DecidableEq C] in
theorem compose_complete [Fintype A] [DecidableEq C] (K : ι → Matrix B A ℂ) (L : κ → Matrix C B ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (hL : ∑ j, (L j)ᴴ * L j = 1) :
    ∑ p : κ × ι, (L p.1 * K p.2)ᴴ * (L p.1 * K p.2) = 1 := by
  simp only [Fintype.sum_prod_type, Matrix.conjTranspose_mul]
  rw [Finset.sum_comm]
  have h : ∀ i, (∑ j, (K i)ᴴ * (L j)ᴴ * (L j * K i)) = (K i)ᴴ * K i := by
    intro i
    simp only [← Matrix.mul_assoc]
    rw [← Matrix.sum_mul]
    simp_rw [Matrix.mul_assoc (K i)ᴴ]
    rw [← Matrix.mul_sum, hL, Matrix.mul_one]
  simp_rw [h]
  exact hK

omit [DecidableEq A] [DecidableEq B] [Fintype C] [DecidableEq C] in
theorem krausMap_compose [DecidableEq A] [DecidableEq B] [Fintype C] [DecidableEq C] (K : ι → Matrix B A ℂ) (L : κ → Matrix C B ℂ)
    (X : Matrix A A ℂ) :
    krausMap L (krausMap K X) = krausMap (fun p : κ × ι => L p.1 * K p.2) X := by
  simp only [krausMap_apply, Fintype.sum_prod_type, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

end
end GeneralKraus
