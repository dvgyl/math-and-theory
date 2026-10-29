module
public import ReplacerBounds
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NoncommRing


@[expose] public section

/-! Exact all-reference upper bound for negative qubit depolarization.

The central matrix interpolation estimate is proved as a sum of three explicit
positive semidefinite sandwiches, so it uses no unproved operator-monotonicity
claim and makes no commutativity assumption about the measurement effect.
-/
open Matrix
open scoped BigOperators ComplexOrder Kronecker
open CMICounterexample ConditionalHockey GeneralContraction ReplacerBounds

namespace NegativeDepolarizingBounds
noncomputable section
variable {n R A : Type} [Fintype n] [DecidableEq n]
  [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]

set_option maxRecDepth 1500
set_option maxHeartbeats 1000000

/-- Scalar value of the sharp bound. -/
def sharpBound (s : ℝ) : ℝ := s * (1 + 3*s) / (1-s)

/-- Real functional calculus in a fixed orthonormal basis. -/
def spectral (U : Matrix n n ℂ) (d : n → ℝ) : Matrix n n ℂ :=
  U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ

theorem spectral_hermitian (U : Matrix n n ℂ) (d : n → ℝ) :
    (spectral U d).IsHermitian := by
  apply Matrix.isHermitian_mul_mul_conjTranspose
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [_root_.IsSelfAdjoint]

theorem spectral_positive (U : Matrix n n ℂ) (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (spectral U d).PosSemidef := by
  exact (Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr (hd i))).mul_mul_conjTranspose_same U

theorem spectral_add (U : Matrix n n ℂ) (d e : n → ℝ) :
    spectral U (fun i => d i + e i) = spectral U d + spectral U e := by
  unfold spectral
  have h : Matrix.diagonal (fun i => ((d i + e i : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => (d i : ℂ)) + Matrix.diagonal (fun i => (e i : ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp
    · simp [Matrix.diagonal, hij]
  rw [h, Matrix.mul_add, Matrix.add_mul]

theorem spectral_sub (U : Matrix n n ℂ) (d e : n → ℝ) :
    spectral U (fun i => d i - e i) = spectral U d - spectral U e := by
  unfold spectral
  have h : Matrix.diagonal (fun i => ((d i - e i : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => (d i : ℂ)) - Matrix.diagonal (fun i => (e i : ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp
    · simp [Matrix.diagonal, hij]
  rw [h, Matrix.mul_sub, Matrix.sub_mul]

theorem spectral_smul (U : Matrix n n ℂ) (d : n → ℝ) (t : ℝ) :
    spectral U (fun i => t * d i) = t • spectral U d := by
  unfold spectral
  have h : Matrix.diagonal (fun i => ((t * d i : ℝ) : ℂ)) =
      t • Matrix.diagonal (fun i => (d i : ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Complex.real_smul]
    · simp [Matrix.diagonal, hij]
  rw [h, Matrix.mul_smul, Matrix.smul_mul]

theorem spectral_const (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) (t : ℝ) :
    spectral U (fun _ => t) = t • (1 : Matrix n n ℂ) := by
  unfold spectral
  have h : Matrix.diagonal (fun _ : n => (t : ℂ)) = t • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Complex.real_smul]
    · simp [Matrix.diagonal, Matrix.one_apply, hij]
  rw [h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]

theorem spectral_mul (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) (d e : n → ℝ) :
    spectral U d * spectral U e = spectral U (fun i => d i * e i) := by
  unfold spectral
  calc
    (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) *
        (U * Matrix.diagonal (fun i => (e i : ℂ)) * Uᴴ) =
      U * (Matrix.diagonal (fun i => (d i : ℂ)) *
        Matrix.diagonal (fun i => (e i : ℂ))) * Uᴴ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
    _ = _ := by
      simp only [Matrix.diagonal_mul_diagonal, Complex.ofReal_mul]

theorem spectral_difference_positive (U : Matrix n n ℂ) (d e : n → ℝ)
    (h : ∀ i, d i ≤ e i) : (spectral U e - spectral U d).PosSemidef := by
  rw [← spectral_sub]
  exact spectral_positive U _ (fun i => sub_nonneg.mpr (h i))

omit [DecidableEq n] in
/-- Weighted variance identity for matrix sandwiches. -/
theorem weighted_sandwich_identity [DecidableEq n] (M C H : Matrix n n ℂ) (t : ℝ) :
    t • (C*M*C) + (1-t) • (H*M*H) =
      (t • C + (1-t) • H) * M * (t • C + (1-t) • H) +
        (t*(1-t)) • ((C-H)*M*(C-H)) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, smul_smul]
  module

/-- A harmonic interpolant dominates every positive common lower bound of `S`
and the identity. Its certificate is a sum of explicit PSD sandwiches. -/
theorem harmonic_dominates (M S C H : Matrix n n ℂ) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hM : M.PosSemidef) (hSM : (S-M).PosSemidef) (hIM : (1-M).PosSemidef)
    (hC : C.IsHermitian) (hH : H.IsHermitian)
    (hlinear : t • C + (1-t) • H = 1)
    (hquad : t • (C*S*C) + (1-t) • (H*H) = H) :
    (H-M).PosSemidef := by
  have hp₁ := posSemidef_real_smul _ (hSM.mul_mul_conjTranspose_same C) t ht
  have hp₂ := posSemidef_real_smul _ (hIM.mul_mul_conjTranspose_same H) (1-t) (sub_nonneg.mpr ht1)
  have hp₃ := posSemidef_real_smul _ (hM.mul_mul_conjTranspose_same (C-H))
    (t*(1-t)) (mul_nonneg ht (sub_nonneg.mpr ht1))
  rw [hC.eq] at hp₁
  rw [hH.eq] at hp₂
  rw [(hC.sub hH).eq] at hp₃
  have hid := weighted_sandwich_identity M C H t
  rw [hlinear, Matrix.one_mul, Matrix.mul_one] at hid
  have heq : t • (C*(S-M)*C) + (1-t) • (H*(1-M)*H) +
      (t*(1-t)) • ((C-H)*M*(C-H)) = H-M := by
    calc
      _ = (t • (C*S*C) + (1-t) • (H*H)) -
          (t • (C*M*C) + (1-t) • (H*M*H)) +
          (t*(1-t)) • ((C-H)*M*(C-H)) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, smul_sub]
        abel
      _ = H - (M + (t*(1-t)) • ((C-H)*M*(C-H))) +
          (t*(1-t)) • ((C-H)*M*(C-H)) := by rw [hquad, hid]
      _ = H-M := by abel
  rw [← heq]
  exact (hp₁.add hp₂).add hp₃


/-- Scalar harmonic interpolation functions in the negative-depolarizing parameter. -/
def denom (s x : ℝ) : ℝ := 4*s + (1-3*s)*x
def harmonic (s x : ℝ) : ℝ := (1+s)*x / denom s x
def reciprocal (s x : ℝ) : ℝ := (1+s) / denom s x
def weight (s : ℝ) : ℝ := 4*s/(1+s)
def prefactor (s : ℝ) : ℝ := (1+s)/4
def spread (s : ℝ) : ℝ := (1+3*s)/(1-s)

theorem sharpBound_eq (s : ℝ) : sharpBound s = s * spread s := by
  unfold sharpBound spread
  ring

theorem weight_bounds (s : ℝ) (hs : 0 < s) (hs3 : s < 1/3) :
    0 < weight s ∧ weight s < 1 := by
  have h : 0 < 1+s := by linarith
  unfold weight
  constructor
  · exact div_pos (by linarith) h
  · apply (div_lt_iff₀ h).mpr
    linarith

theorem sharpBound_bounds (s : ℝ) (hs : 0 < s) (hs3 : s < 1/3) :
    0 < sharpBound s ∧ sharpBound s < 1 := by
  have hd : 0 < 1-s := by linarith
  unfold sharpBound
  constructor
  · exact div_pos (mul_pos hs (by linarith)) hd
  · apply (div_lt_iff₀ hd).mpr
    have hp : 0 < (1-3*s)*(1+s) := mul_pos (by linarith) (by linarith)
    nlinarith

theorem denom_pos (s x : ℝ) (hs : 0 < s) (hs3 : s < 1/3) (hx : 0 ≤ x) :
    0 < denom s x := by
  unfold denom
  have hp : 0 ≤ (1-3*s)*x := mul_nonneg (by linarith) hx
  linarith

theorem scalar_interpolation_linear (s x : ℝ) (hs : 0 < s) (hs3 : s < 1/3)
    (hx : 0 ≤ x) : weight s * reciprocal s x + (1-weight s) * harmonic s x = 1 := by
  have hd := ne_of_gt (denom_pos s x hs hs3 hx)
  have hp : 1+s ≠ 0 := ne_of_gt (by linarith : 0 < 1+s)
  unfold weight reciprocal harmonic
  field_simp
  unfold denom
  ring

theorem scalar_interpolation_quad (s x : ℝ) (hs : 0 < s) (hs3 : s < 1/3)
    (hx : 0 ≤ x) :
    weight s * (reciprocal s x * x * reciprocal s x) +
      (1-weight s) * (harmonic s x * harmonic s x) = harmonic s x := by
  have hd := ne_of_gt (denom_pos s x hs hs3 hx)
  have hp : 1+s ≠ 0 := ne_of_gt (by linarith : 0 < 1+s)
  unfold weight reciprocal harmonic
  field_simp
  unfold denom
  ring

theorem harmonic_le_linear (s x : ℝ) (hs : 0 < s) (hs3 : s < 1/3)
    (hx : 0 ≤ x) : s * harmonic s x ≤ prefactor s * x := by
  have hd := denom_pos s x hs hs3 hx
  unfold harmonic prefactor
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hd).mpr
  unfold denom
  have hp : 0 ≤ (1+s)*(1-3*s)*x^2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg x)
  nlinarith

theorem harmonic_pair_bound (s x : ℝ) (hs : 0 < s) (hs3 : s < 1/3)
    (hx : 0 ≤ x) (hx4 : x ≤ 4) :
    harmonic s x + harmonic s (4-x) ≤ 1 + spread s := by
  have hd := denom_pos s x hs hs3 hx
  have he := denom_pos s (4-x) hs hs3 (by linarith)
  have hc : 0 < 1-s := by linarith
  have hid : 1 + spread s - (harmonic s x + harmonic s (4-x)) =
      (4*s*(1+s)*(1-3*s)*(x-2)^2) /
        ((1-s)*denom s x*denom s (4-x)) := by
    unfold harmonic spread
    field_simp
    unfold denom
    ring
  have hn : 0 ≤ (4*s*(1+s)*(1-3*s)*(x-2)^2) /
      ((1-s)*denom s x*denom s (4-x)) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs.le)
      (by linarith)) (by linarith)) (sq_nonneg (x-2)))
      (mul_nonneg (mul_nonneg hc.le hd.le) he.le)
  linarith [hid]

/-- The scalar maximum is taken inside one commuting functional calculus. -/
def upperEnvelope (s x : ℝ) : ℝ :=
  max (harmonic s x) ((prefactor s * x - (1-sharpBound s))/s)

theorem upperEnvelope_bounds (s x : ℝ) (hs : 0 < s) (hs3 : s < 1/3)
    (hx : 0 ≤ x) (hx4 : x ≤ 4) :
    harmonic s x ≤ upperEnvelope s x ∧
    upperEnvelope s x ≤ 1 - harmonic s (4-x) + spread s ∧
    0 ≤ prefactor s*x - s*upperEnvelope s x ∧
    prefactor s*x - s*upperEnvelope s x ≤ 1-sharpBound s := by
  have hp := sharpBound_bounds s hs hs3
  have hb := harmonic_pair_bound s x hs hs3 hx hx4
  have hf := harmonic_le_linear s x hs hs3 hx
  have hg := harmonic_le_linear s (4-x) hs hs3 (by linarith)
  have hfour : 4*prefactor s = 1+s := by unfold prefactor; ring
  have hpq := sharpBound_eq s
  refine ⟨le_max_left _ _, ?_, ?_, ?_⟩
  · apply max_le
    · linarith
    · apply (div_le_iff₀ hs).mpr
      nlinarith
  · have hz : upperEnvelope s x ≤ prefactor s*x/s := by
      apply max_le
      · apply (le_div_iff₀ hs).mpr
        nlinarith
      · apply (div_le_div_iff_of_pos_right hs).mpr
        linarith
    have hz' := (le_div_iff₀ hs).mp hz
    nlinarith
  · have hz : (prefactor s*x-(1-sharpBound s))/s ≤ upperEnvelope s x :=
      le_max_right _ _
    have hz' := (div_le_iff₀ hs).mp hz
    nlinarith


/-- Operator interpolation inequality, proved for every matrix size. -/
theorem spectral_harmonic_dominates (U : Matrix n n ℂ)
    (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1) (d : n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (M : Matrix n n ℂ) (hM : M.PosSemidef) (hIM : (1-M).PosSemidef)
    (hSM : (spectral U d-M).PosSemidef)
    (s : ℝ) (hs : 0<s) (hs3 : s<1/3) :
    (spectral U (fun i => harmonic s (d i)) - M).PosSemidef := by
  have hw := weight_bounds s hs hs3
  apply harmonic_dominates M (spectral U d)
    (spectral U (fun i => reciprocal s (d i))) _ (weight s)
    hw.1.le hw.2.le hM hSM hIM (spectral_hermitian U _) (spectral_hermitian U _)
  · rw [← spectral_smul, ← spectral_smul, ← spectral_add]
    have hf : (fun i => weight s * reciprocal s (d i) +
        (1-weight s)*harmonic s (d i)) = fun _ : n => 1 := by
      funext i
      exact scalar_interpolation_linear s (d i) hs hs3 (hd i)
    rw [hf, spectral_const U hU' 1, one_smul]
  · simp only [spectral_mul U hU]
    rw [← spectral_smul, ← spectral_smul, ← spectral_add]
    exact congrArg (spectral U) (funext fun i =>
      scalar_interpolation_quad s (d i) hs hs3 (hd i))

def reserve (s x : ℝ) : ℝ := prefactor s*x - s*upperEnvelope s x

/-- A complete effect decomposition in a single spectral algebra. The measurement
matrix M need not commute with that algebra. -/
theorem spectral_effect_split (U : Matrix n n ℂ)
    (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1) (d : n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hd4 : ∀ i, d i ≤ 4)
    (M : Matrix n n ℂ) (hM : M.PosSemidef) (hIM : (1-M).PosSemidef)
    (hSM : (spectral U d-M).PosSemidef)
    (hcomp : ((4:ℝ) • (1:Matrix n n ℂ) - spectral U d - (1-M)).PosSemidef)
    (s : ℝ) (hs : 0<s) (hs3 : s<1/3) :
    (spectral U (fun i => reserve s (d i))).PosSemidef ∧
    ((1-sharpBound s) • (1:Matrix n n ℂ) - spectral U (fun i => reserve s (d i))).PosSemidef ∧
    (prefactor s • spectral U d - s • M - spectral U (fun i => reserve s (d i))).PosSemidef ∧
    (sharpBound s • (1:Matrix n n ℂ) -
      (prefactor s • spectral U d - s • M - spectral U (fun i => reserve s (d i)))).PosSemidef := by
  have hb := fun i => upperEnvelope_bounds s (d i) hs hs3 (hd i) (hd4 i)
  have hF := spectral_harmonic_dominates U hU hU' d hd M hM hIM hSM s hs hs3
  have hcomp' : (spectral U (fun i => 4-d i) - (1-M)).PosSemidef := by
    simpa only [spectral_sub, spectral_const U hU' 4] using hcomp
  have hG := spectral_harmonic_dominates U hU hU' (fun i => 4-d i)
    (fun i => sub_nonneg.mpr (hd4 i)) (1-M) hIM
    (by simpa only [sub_sub_cancel] using hM) hcomp' s hs hs3
  let Z := spectral U (fun i => upperEnvelope s (d i))
  have hZM : (Z-M).PosSemidef := by
    have hz := spectral_difference_positive U (fun i => harmonic s (d i))
      (fun i => upperEnvelope s (d i)) (fun i => (hb i).1)
    have hh := hz.add hF
    simpa only [sub_add_sub_cancel] using hh
  have hcap : (spread s • (1:Matrix n n ℂ) - (Z-M)).PosSemidef := by
    have hz := spectral_difference_positive U (fun i => upperEnvelope s (d i))
      (fun i => 1-harmonic s (4-d i)+spread s) (fun i => (hb i).2.1)
    rw [spectral_add, spectral_sub, spectral_const U hU' 1, one_smul,
      spectral_const U hU' (spread s)] at hz
    have hh := hz.add hG
    convert hh using 1
    dsimp [Z]
    abel
  have heq : spectral U (fun i => reserve s (d i)) =
      prefactor s • spectral U d - s • Z := by
    unfold reserve
    rw [spectral_sub, spectral_smul, spectral_smul]
  have hres : prefactor s • spectral U d - s • M -
      spectral U (fun i => reserve s (d i)) = s • (Z-M) := by
    rw [heq, smul_sub]
    abel
  refine ⟨spectral_positive U _ (fun i => (hb i).2.2.1), ?_, ?_, ?_⟩
  · rw [← spectral_const U hU' (1-sharpBound s)]
    exact spectral_difference_positive U _ _ (fun i => (hb i).2.2.2)
  · rw [hres]
    exact posSemidef_real_smul _ hZM s hs.le
  · rw [hres, sharpBound_eq]
    have hh := posSemidef_real_smul _ hcap s hs.le
    simpa only [smul_sub, smul_smul] using hh

/-- Positivity of a diagonalized matrix implies pointwise nonnegative eigenvalues. -/
theorem nonneg_of_spectral_positive (U : Matrix n n ℂ) (hU : Uᴴ*U=1)
    (d : n → ℝ) (h : (spectral U d).PosSemidef) : ∀ i, 0 ≤ d i := by
  have hp := h.mul_mul_conjTranspose_same Uᴴ
  rw [Matrix.conjTranspose_conjTranspose] at hp
  have heq : Uᴴ * spectral U d * U = Matrix.diagonal (fun i => (d i : ℂ)) :=
    unitary_conj_cancel _ U hU
  rw [heq] at hp
  intro i
  have hi := posSemidef_diagonal_re _ hp i
  simpa using hi

/-- Lift an operator on the reference by the identity on the system. -/
def referenceLift (D : Matrix R R ℂ) : Matrix (R×A) (R×A) ℂ := D ⊗ₖ 1

omit [DecidableEq R] in
theorem referenceLift_mul [DecidableEq R] (D E : Matrix R R ℂ) :
    referenceLift (A:=A) D * referenceLift E = referenceLift (D*E) := by
  unfold referenceLift
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem referenceLift_star (D : Matrix R R ℂ) :
    (referenceLift (A:=A) D)ᴴ = referenceLift Dᴴ := by
  unfold referenceLift
  rw [kronecker_conjTranspose, Matrix.conjTranspose_one]

omit [Fintype R] [Fintype A] in
theorem referenceLift_one [Fintype R] [Fintype A] : referenceLift (R:=R) (A:=A) (1:Matrix R R ℂ) = 1 :=
  Matrix.one_kronecker_one

theorem referenceLift_spectral (U : Matrix R R ℂ) (d : R → ℝ) :
    spectral (referenceLift (A:=A) U) (fun i => d i.1) = referenceLift (spectral U d) := by
  have hdiag : Matrix.diagonal (fun i : R×A => (d i.1 : ℂ)) =
      referenceLift (Matrix.diagonal (fun i => (d i : ℂ))) := by
    unfold referenceLift
    rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
    simp only [mul_one]
  unfold spectral
  rw [hdiag, referenceLift_star, referenceLift_mul, referenceLift_mul]

/-- Every effect satisfying the two dimension-two domination inequalities has an
actual reference-only reserve and a residual effect bounded by the sharp factor. -/
theorem reference_effect_split (D : Matrix R R ℂ) (hD : D.PosSemidef)
    (hD4 : ((4:ℝ) • (1:Matrix R R ℂ)-D).PosSemidef)
    (M : Matrix (R×A) (R×A) ℂ) (hM : M.PosSemidef) (hIM : (1-M).PosSemidef)
    (hDM : (referenceLift D-M).PosSemidef)
    (hcomp : ((4:ℝ) • (1:Matrix (R×A) (R×A) ℂ)-referenceLift D-(1-M)).PosSemidef)
    (s : ℝ) (hs : 0<s) (hs3 : s<1/3) :
    ∃ H : Matrix R R ℂ, H.PosSemidef ∧
      ((1-sharpBound s) • (1:Matrix R R ℂ)-H).PosSemidef ∧
      (prefactor s • referenceLift D-s • M-referenceLift H).PosSemidef ∧
      (sharpBound s • (1:Matrix (R×A) (R×A) ℂ)-
        (prefactor s • referenceLift D-s • M-referenceLift H)).PosSemidef := by
  let U := hD.1.eigenvectorUnitary.1
  let d := hD.1.eigenvalues
  have hU : Uᴴ*U=1 := unitary.coe_star_mul_self hD.1.eigenvectorUnitary
  have hU' : U*Uᴴ=1 := unitary.coe_mul_star_self hD.1.eigenvectorUnitary
  have hspec : spectral U d = D := hD.1.spectral_theorem.symm
  have hd : ∀ i, 0 ≤ d i := hD.eigenvalues_nonneg
  have hd4 : ∀ i, d i ≤ 4 := by
    have hp : (spectral U (fun i => 4-d i)).PosSemidef := by
      simpa only [spectral_sub, spectral_const U hU' 4, hspec] using hD4
    have hh := nonneg_of_spectral_positive U hU _ hp
    intro i
    exact sub_nonneg.mp (hh i)
  have hV : (referenceLift (A:=A) U)ᴴ * referenceLift U = 1 := by
    rw [referenceLift_star, referenceLift_mul, hU, referenceLift_one]
  have hV' : referenceLift (A:=A) U * (referenceLift U)ᴴ = 1 := by
    rw [referenceLift_star, referenceLift_mul, hU', referenceLift_one]
  have hvd : spectral (referenceLift (A:=A) U) (fun i => d i.1) = referenceLift D := by
    rw [referenceLift_spectral, hspec]
  have hh := spectral_effect_split (referenceLift (A:=A) U) hV hV' (fun i => d i.1)
    (fun i => hd i.1) (fun i => hd4 i.1) M hM hIM
    (by simpa only [hvd] using hDM) (by simpa only [hvd] using hcomp) s hs hs3
  have hreserve : spectral (referenceLift (A:=A) U) (fun i => reserve s (d i.1)) =
      referenceLift (spectral U (fun i => reserve s (d i))) :=
    referenceLift_spectral U (fun i => reserve s (d i))
  refine ⟨spectral U (fun i => reserve s (d i)), ?_, ?_, ?_, ?_⟩
  · exact spectral_positive U _ (fun i => (upperEnvelope_bounds s (d i) hs hs3 (hd i) (hd4 i)).2.2.1)
  · rw [← spectral_const U hU' (1-sharpBound s)]
    exact spectral_difference_positive U _ _
      (fun i => (upperEnvelope_bounds s (d i) hs hs3 (hd i) (hd4 i)).2.2.2)
  · simpa only [hreserve, referenceLift_spectral, hspec] using hh.2.2.1
  · simpa only [hreserve, referenceLift_spectral, hspec] using hh.2.2.2


end
end NegativeDepolarizingBounds
