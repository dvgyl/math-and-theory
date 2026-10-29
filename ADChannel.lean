module
public import SpectralEntropy
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination


@[expose] public section

open Matrix
open scoped ComplexOrder

namespace ADSeparation
noncomputable section

abbrev Q := Fin 2
abbrev Ref := Fin 3
abbrev Composite := Ref × Q
abbrev CMat (m n : Type*) := Matrix m n ℂ

/-- Amplitude damping with survival probability one quarter. -/
def adChannel (X : CMat Q Q) : CMat Q Q :=
  !![X 0 0 + 3 * X 1 1 / 4, X 0 1 / 2; X 1 0 / 2, X 1 1 / 4]

/-- Four rational Kraus operators; the last three are identical. -/
def adK (k : Fin 4) : CMat Q Q :=
  if k = 0 then !![1, 0; 0, (1:ℂ)/2] else !![0, (1:ℂ)/2; 0, 0]

lemma ad_kraus_complete : (∑ k : Fin 4, (adK k)ᴴ * adK k) = (1 : CMat Q Q) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [adK, Fin.sum_univ_succ, map_ofNat]

lemma ad_kraus (X : CMat Q Q) : adChannel X = ∑ k : Fin 4, adK k * X * (adK k)ᴴ := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [adChannel, adK, Fin.sum_univ_succ, map_ofNat] <;> ring

lemma ad_trace (X : CMat Q Q) : (adChannel X).trace = X.trace := by
  simp [adChannel, Matrix.trace, Fin.sum_univ_succ]
  ring

lemma ad_add (X Y : CMat Q Q) : adChannel (X+Y) = adChannel X + adChannel Y := by
  simp only [ad_kraus, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

lemma ad_smul (z : ℂ) (X : CMat Q Q) : adChannel (z • X) = z • adChannel X := by
  simp only [ad_kraus, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

def adLinearMap : CMat Q Q →ₗ[ℂ] CMat Q Q where
  toFun := adChannel
  map_add' := ad_add
  map_smul' := ad_smul

lemma ad_sub (X Y : CMat Q Q) : adChannel (X-Y) = adChannel X - adChannel Y :=
  adLinearMap.map_sub X Y

lemma ad_hermitian (X : CMat Q Q) (hX : X.IsHermitian) : (adChannel X).IsHermitian := by
  rw [ad_kraus]
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hX.eq, Matrix.mul_assoc]

def adAmplified {m : Type*} (X : CMat (m×Q) (m×Q)) : CMat (m×Q) (m×Q) :=
  fun r c => adChannel (fun a b => X (r.1,a) (c.1,b)) r.2 c.2

def partialTraceQ {m : Type*} (X : CMat (m×Q) (m×Q)) : CMat m m :=
  fun r c => ∑ i : Q, X (r,i) (c,i)

lemma partialTraceQ_sub {m : Type*} (X Y : CMat (m×Q) (m×Q)) :
    partialTraceQ (X-Y) = partialTraceQ X - partialTraceQ Y := by
  ext r c
  simp [partialTraceQ, Finset.sum_sub_distrib]

lemma partialTraceQ_hermitian {m : Type*} (X : CMat (m×Q) (m×Q))
    (hX : X.IsHermitian) : (partialTraceQ X).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro r c
  simp only [partialTraceQ, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact hX.apply (r,i) (c,i)

lemma adAmplified_add {m : Type*} (X Y : CMat (m×Q) (m×Q)) :
    adAmplified (X+Y) = adAmplified X + adAmplified Y := by
  ext r c
  exact congrArg (fun M : CMat Q Q => M r.2 c.2)
    (ad_add (fun a b => X (r.1,a) (c.1,b)) (fun a b => Y (r.1,a) (c.1,b)))

lemma adAmplified_smul {m : Type*} (z : ℂ) (X : CMat (m×Q) (m×Q)) :
    adAmplified (z • X) = z • adAmplified X := by
  ext r c
  exact congrArg (fun M : CMat Q Q => M r.2 c.2)
    (ad_smul z (fun a b => X (r.1,a) (c.1,b)))

def adAmplifiedLinearMap {m : Type*} : CMat (m×Q) (m×Q) →ₗ[ℂ] CMat (m×Q) (m×Q) where
  toFun := adAmplified
  map_add' := adAmplified_add
  map_smul' := adAmplified_smul

def liftedQ {m : Type*} [DecidableEq m] (U : CMat Q Q) : CMat (m×Q) (m×Q) :=
  fun r c => if r.1 = c.1 then U r.2 c.2 else 0

def conjugateQ {m : Type*} [Fintype m] [DecidableEq m]
    (U : CMat Q Q) (X : CMat (m×Q) (m×Q)) : CMat (m×Q) (m×Q) :=
  liftedQ U * X * (liftedQ U)ᴴ

def blockQ {m : Type*} (X : CMat (m×Q) (m×Q)) (r c : m) : CMat Q Q :=
  fun a b => X (r,a) (c,b)

lemma conjugateQ_entry {m : Type*} [Fintype m] [DecidableEq m]
    (U : CMat Q Q) (X : CMat (m×Q) (m×Q)) (r c : m×Q) :
    conjugateQ U X r c =
      (U * blockQ X r.1 c.1 * Uᴴ) r.2 c.2 := by
  simp [conjugateQ, liftedQ, blockQ, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
    apply_ite, Finset.sum_add_distrib]

lemma adAmplified_kraus {m : Type*} [Fintype m] [DecidableEq m]
    (X : CMat (m×Q) (m×Q)) : adAmplified X = ∑ k : Fin 4, conjugateQ (adK k) X := by
  ext r c
  change adChannel (blockQ X r.1 c.1) r.2 c.2 =
    (∑ k : Fin 4, conjugateQ (adK k) X) r c
  simp only [ad_kraus, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact (conjugateQ_entry (adK k) X r c).symm

/-- Positivity is preserved for every finite ancillary space. -/
theorem ad_completely_positive {m : Type*} [Fintype m] [DecidableEq m]
    (X : CMat (m×Q) (m×Q)) (hX : X.PosSemidef) : (adAmplified X).PosSemidef := by
  rw [adAmplified_kraus]
  exact Finset.sum_induction _ _ (fun A B hA hB => hA.add hB)
    Matrix.PosSemidef.zero (fun k _ => hX.mul_mul_conjTranspose_same (liftedQ (adK k)))

lemma adAmplified_hermitian {m : Type*} [Fintype m] [DecidableEq m]
    (X : CMat (m×Q) (m×Q)) (hX : X.IsHermitian) : (adAmplified X).IsHermitian := by
  rw [adAmplified_kraus]
  simp only [Matrix.IsHermitian, conjugateQ, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hX.eq, Matrix.mul_assoc]

lemma adAmplified_sub {m : Type*} (X Y : CMat (m×Q) (m×Q)) :
    adAmplified (X-Y) = adAmplified X - adAmplified Y := by
  ext r c
  exact congrArg (fun M : CMat Q Q => M r.2 c.2)
    (ad_sub (fun a b => X (r.1,a) (c.1,b)) (fun a b => Y (r.1,a) (c.1,b)))

lemma adAmplified_trace {m : Type*} [Fintype m] (X : CMat (m×Q) (m×Q)) :
    (adAmplified X).trace = X.trace := by
  simp only [Matrix.trace, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  exact ad_trace (fun a b => X (r,a) (r,b))

def pauliX : CMat Q Q := !![0, 1; 1, 0]
def pauliY : CMat Q Q := !![0, -Complex.I; Complex.I, 0]
def pauliZ : CMat Q Q := !![1, 0; 0, -1]

lemma pauliX_left : pauliXᴴ * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
lemma pauliX_right : pauliX * pauliXᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
lemma pauliY_left : pauliYᴴ * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliY, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
lemma pauliY_right : pauliY * pauliYᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliY, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

lemma pauliZ_left : pauliZᴴ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
lemma pauliZ_right : pauliZ * pauliZᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

lemma liftedQ_mul {m : Type*} [Fintype m] [DecidableEq m] (U V : CMat Q Q) :
    liftedQ U * liftedQ (m:=m) V = liftedQ (U*V) := by
  ext r c
  by_cases h : r.1 = c.1
  · simp [liftedQ, Matrix.mul_apply, Fintype.sum_prod_type, h, apply_ite, Finset.sum_mul]
  · simp [liftedQ, Matrix.mul_apply, Fintype.sum_prod_type, h, Ne.symm h, apply_ite, Finset.sum_mul]

lemma liftedQ_conjTranspose {m : Type*} [DecidableEq m] (U : CMat Q Q) :
    (liftedQ (m:=m) U)ᴴ = liftedQ Uᴴ := by
  ext r c
  simp only [Matrix.conjTranspose_apply, liftedQ]
  by_cases h : r.1 = c.1
  · simp only [if_pos h, if_pos h.symm]
  · simp only [if_neg h, if_neg (Ne.symm h), map_zero, star_zero]

lemma liftedQ_one {m : Type*} [DecidableEq m] : liftedQ (m:=m) (1 : CMat Q Q) = 1 := by
  ext r c
  simp [liftedQ, Matrix.one_apply, Prod.ext_iff, ite_and]

lemma liftedQ_left {m : Type*} [Fintype m] [DecidableEq m]
    (U : CMat Q Q) (hU : Uᴴ * U = 1) : (liftedQ (m:=m) U)ᴴ * liftedQ U = 1 := by
  rw [liftedQ_conjTranspose, liftedQ_mul, hU, liftedQ_one]

lemma liftedQ_right {m : Type*} [Fintype m] [DecidableEq m]
    (U : CMat Q Q) (hU : U * Uᴴ = 1) : liftedQ (m:=m) U * (liftedQ U)ᴴ = 1 := by
  rw [liftedQ_conjTranspose, liftedQ_mul, hU, liftedQ_one]

/-- On the trace-zero subspace, damping is a difference of two unitary conjugations. -/
lemma adChannel_zero_trace (X : CMat Q Q) (h : X.trace = 0) :
    adChannel X = (3/8:ℝ) • X - (1/8:ℝ) • (pauliZ * X * pauliZᴴ) := by
  have ht : X 0 0 + X 1 1 = 0 := by simpa [Matrix.trace, Fin.sum_univ_succ] using h
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j
  all_goals norm_num [adChannel, pauliZ, Fin.sum_univ_succ, Complex.real_smul]
  all_goals ring_nf
  all_goals linear_combination (3/4:ℂ) * ht

/-- The exact decomposition for every reference space, restricted only by its zero marginal. -/
theorem adAmplified_mixture {m : Type*} [Fintype m] [DecidableEq m]
    (X : CMat (m×Q) (m×Q)) (h : partialTraceQ X = 0) :
    adAmplified X = (3/8:ℝ) • X - (1/8:ℝ) • conjugateQ pauliZ X := by
  ext r c
  have ht : (blockQ X r.1 c.1).trace = 0 := by
    exact congrArg (fun M : CMat m m => M r.1 c.1) h
  have hm := congrArg (fun M : CMat Q Q => M r.2 c.2)
    (adChannel_zero_trace (blockQ X r.1 c.1) ht)
  simpa only [adAmplified, Matrix.sub_apply, Matrix.smul_apply, conjugateQ_entry, blockQ] using hm

end
end ADSeparation
