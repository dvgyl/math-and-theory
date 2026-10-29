module
public import GeneralKraus
public import KrausSupport
public import KrausSaturation
public import KrausChannelSaturation
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp


@[expose] public section

/-! A concrete rational simplex preparation with an erased reference cross term. -/
open Matrix
open scoped BigOperators ComplexOrder
open ConditionalHockey

namespace SimplexPreparation
noncomputable section

variable {m : Type} [Fintype m] [DecidableEq m]
abbrev Q := Fin 2
abbrev Ref (m : Type) := Option m
abbrev Label (m : Type) := Option m

def flag (s : Ref m) : ℂ := if s = none then 1 else 0

def simplex (i : Label m) (s : Ref m) : ℂ :=
  match i, s with
  | _, none => 0
  | none, some _ => -1
  | some j, some r => if j = r then 1 else 0

omit [Fintype m] in
@[simp] theorem flag_none [Fintype m] : flag (m:=m) none = 1 := by simp [flag]
omit [Fintype m] in
@[simp] theorem flag_some [Fintype m] (j : m) : flag (some j) = 0 := by simp [flag]
omit [Fintype m] in
@[simp] theorem simplex_none_right [Fintype m] (i : Label m) : simplex i none = 0 := by cases i <;> rfl
omit [Fintype m] in
@[simp] theorem simplex_none_some [Fintype m] (j : m) : simplex none (some j) = -1 := rfl
omit [Fintype m] in
@[simp] theorem simplex_some_some [Fintype m] (i j : m) : simplex (some i) (some j) = if i=j then 1 else 0 := rfl

theorem simplex_sum (s : Ref m) : ∑ i : Label m, simplex i s = 0 := by
  cases s with
  | none => simp
  | some r => simp [Fintype.sum_option]

theorem flag_norm : ∑ s : Ref m, star (flag s) * flag s = 1 := by
  simp [Fintype.sum_option]

theorem flag_simplex_orthogonal (i : Label m) :
    ∑ s : Ref m, star (flag s) * simplex i s = 0 := by
  simp [Fintype.sum_option]

theorem simplex_flag_orthogonal (i : Label m) :
    ∑ s : Ref m, star (simplex i s) * flag s = 0 := by
  simp [Fintype.sum_option]

theorem simplex_total_norm :
    ∑ i : Label m, ∑ s : Ref m, star (simplex i s) * simplex i s =
      (2 * Fintype.card m : ℂ) := by
  simp [Fintype.sum_option, apply_ite]
  ring

def column (a b : ℂ) (i : Label m) (s : Ref m) (q : Q) : ℂ :=
  if q = 0 then a * flag s else b * simplex i s

/-- Each Kraus operator prepares one classical label and a simplex reference vector. -/
def prepK (a b : ℂ) (i : Label m) : Matrix (Ref m × Label m) Q ℂ :=
  fun r q => if r.2 = i then column a b i r.1 q else 0

theorem prepK_gram_entry (a b : ℂ) (i : Label m) (p q : Q) :
    ((prepK a b i)ᴴ * prepK a b i) p q =
      ∑ s : Ref m, star (column a b i s p) * column a b i s q := by
  simp [prepK, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, apply_ite]

theorem prepK_complete (a b : ℂ)
    (ha : ((Fintype.card m : ℂ)+1) * (star a * a) = 1)
    (hb : (2 * Fintype.card m : ℂ) * (star b * b) = 1) :
    ∑ i : Label m, (prepK a b i)ᴴ * prepK a b i = 1 := by
  ext p q
  simp only [Matrix.sum_apply, prepK_gram_entry]
  fin_cases p <;> fin_cases q
  · simpa [column, Fintype.sum_option, flag, Matrix.one_apply, mul_assoc,
      ← Finset.mul_sum, ← Finset.sum_mul, add_mul] using ha
  · simp [column, Fintype.sum_option, flag, Matrix.one_apply]
  · simp [column, Fintype.sum_option, flag, Matrix.one_apply]
  · convert hb using 1
    · simp [column, Fintype.sum_option, simplex, Matrix.one_apply, apply_ite,
        mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, two_mul]
      ring
    · simp [Matrix.one_apply]

/-- Constructor before choosing the positive normalization constants. -/
def channelWith (a b : ℂ)
    (ha : ((Fintype.card m : ℂ)+1) * (star a * a) = 1)
    (hb : (2 * Fintype.card m : ℂ) * (star b * b) = 1) :
    QuantumChannel Q (Ref m × Label m) :=
  GeneralKraus.channel (prepK a b) (prepK_complete a b ha hb)

theorem cross_partialTrace (a b : ℂ)
    (ha : ((Fintype.card m : ℂ)+1) * (star a * a) = 1)
    (hb : (2 * Fintype.card m : ℂ) * (star b * b) = 1) :
    CMICounterexample.partialTraceMatrix
      ((channelWith a b ha hb).map (Matrix.single (0 : Q) (1 : Q) (1 : ℂ))) = 0 := by
  ext r s
  change (∑ j : Label m, (∑ i : Label m,
    prepK a b i * Matrix.single (0 : Q) (1 : Q) (1 : ℂ) * (prepK a b i)ᴴ)
      (r,j) (s,j)) = 0
  simp only [Matrix.sum_apply]
  simp_rw [KrausSaturation.matrixUnit_sandwich_entry]
  cases r <;> cases s <;>
    simp [prepK, column, flag, simplex, Fintype.sum_option, apply_ite,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]

def invSqrt (r : ℝ) : ℂ := (Real.sqrt r : ℂ)⁻¹

theorem invSqrt_normalized (r : ℝ) (hr : 0 < r) :
    (r : ℂ) * (star (invSqrt r) * invSqrt r) = 1 := by
  have hs : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hr.le
  have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simp only [invSqrt, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [← _root_.mul_inv_rev, hs, mul_inv_cancel₀ hn]

def smallCoeff (m : Type) [Fintype m] : ℂ := invSqrt ((Fintype.card m : ℝ)+1)
def largeCoeff (m : Type) [Fintype m] : ℂ := invSqrt (2*(Fintype.card m : ℝ))

omit [DecidableEq m] in
theorem smallCoeff_normalized [DecidableEq m] :
    ((Fintype.card m : ℂ)+1) * (star (smallCoeff m) * smallCoeff m) = 1 := by
  have hpos : 0 < (Fintype.card m : ℝ)+1 := by positivity
  simpa [smallCoeff] using invSqrt_normalized ((Fintype.card m : ℝ)+1) hpos

omit [DecidableEq m] in
theorem largeCoeff_normalized [DecidableEq m] [Nonempty m] :
    (2 * Fintype.card m : ℂ) * (star (largeCoeff m) * largeCoeff m) = 1 := by
  have hc : 0 < (Fintype.card m : ℝ) := by exact_mod_cast Fintype.card_pos (α:=m)
  have hpos : 0 < 2*(Fintype.card m : ℝ) := by positivity
  simpa [largeCoeff] using invSqrt_normalized (2*(Fintype.card m : ℝ)) hpos

/-- The normalized simplex preparation, with explicit verified constants. -/
def channel (m : Type) [Fintype m] [DecidableEq m] [Nonempty m] :
    QuantumChannel Q (Ref m × Label m) :=
  channelWith (smallCoeff m) (largeCoeff m) smallCoeff_normalized largeCoeff_normalized

theorem channel_cross_partialTrace [Nonempty m] :
    CMICounterexample.partialTraceMatrix
      ((channel m).map (Matrix.single (0 : Q) (1 : Q) (1 : ℂ))) = 0 :=
  cross_partialTrace (smallCoeff m) (largeCoeff m) smallCoeff_normalized largeCoeff_normalized

section Decoder
variable {B J : Type} [Fintype B] [DecidableEq B] [Fintype J] [DecidableEq J]

def simplexColumns (V : Label m → Matrix B J ℂ) : Matrix (m × B) (Label m × J) ℂ :=
  fun r c => simplex c.1 (some r.1) * V c.1 r.2 c.2

def plainColumns (V : Label m → Matrix B J ℂ) : Matrix B (Label m × J) ℂ :=
  fun b c => V c.1 b c.2

omit [Fintype B] [DecidableEq B] [DecidableEq J] in
theorem simplexColumns_mulVec [Fintype B] [DecidableEq B] [DecidableEq J] (V : Label m → Matrix B J ℂ)
    (x : Label m × J → ℂ) (r : m) (b : B) :
    (simplexColumns V *ᵥ x) (r,b) =
      (V (some r) *ᵥ (fun j => x (some r,j))) b -
      (V none *ᵥ (fun j => x (none,j))) b := by
  simp [simplexColumns, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_option, simplex, Finset.sum_add_distrib, sub_eq_add_neg]
  ring

omit [DecidableEq m] [Fintype B] [DecidableEq B] [DecidableEq J] in
theorem plainColumns_mulVec [DecidableEq m] [Fintype B] [DecidableEq B] [DecidableEq J] (V : Label m → Matrix B J ℂ)
    (x : Label m × J → ℂ) (b : B) :
    (plainColumns V *ᵥ x) b =
      ∑ i : Label m, (V i *ᵥ (fun j => x (i,j))) b := by
  simp [plainColumns, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

/-- Zero common output-column range gives an actual linear simplex decoder. -/
theorem exists_decoder (V : Label m → Matrix B J ℂ)
    (hzero : ∀ w : B → ℂ, (∀ i, w ∈ LinearMap.range (V i).toLin') → w = 0) :
    ∃ L : Matrix B (m × B) ℂ, L * simplexColumns V = plainColumns V := by
  apply KrausSupport.exists_leftFactor_of_ker_le
  intro x hx
  change simplexColumns V *ᵥ x = 0 at hx
  have heq : ∀ i : Label m,
      V i *ᵥ (fun j => x (i,j)) = V none *ᵥ (fun j => x (none,j)) := by
    intro i
    cases i with
    | none => rfl
    | some r =>
      ext b
      have hh := congrFun hx (r,b)
      rw [simplexColumns_mulVec] at hh
      exact sub_eq_zero.mp hh
  have hz : V none *ᵥ (fun j => x (none,j)) = 0 := by
    apply hzero
    intro i
    refine ⟨fun j => x (i,j), ?_⟩
    exact heq i
  change plainColumns V *ᵥ x = 0
  ext b
  rw [plainColumns_mulVec]
  simp_rw [heq, hz]
  simp

omit [DecidableEq B] [Fintype J] [DecidableEq J] in
theorem decoder_column [DecidableEq B] [Fintype J] [DecidableEq J] (V : Label m → Matrix B J ℂ)
    (L : Matrix B (m × B) ℂ) (hL : L * simplexColumns V = plainColumns V)
    (i : Label m) (j : J) :
    L *ᵥ (fun r => simplex i (some r.1) * V i r.2 j) = fun b => V i b j := by
  ext b
  exact congrArg (fun M : Matrix B (Label m × J) ℂ => M b (i,j)) hL

end Decoder

section Prepared
variable {B J : Type} [Fintype B] [DecidableEq B] [Fintype J] [DecidableEq J]

/-- A factor family prepares one density matrix for each classical label. -/
def FactorNormalized (V : Label m → Matrix B J ℂ) : Prop :=
  ∀ i, ∑ j, ∑ x, star (V i x j) * V i x j = 1

omit [Fintype m] [DecidableEq m] [DecidableEq B] [DecidableEq J] in
theorem factorNormalized_of_trace [Fintype m] [DecidableEq m] [DecidableEq B] [DecidableEq J] (V : Label m → Matrix B J ℂ)
    (hV : ∀ i, (V i * (V i)ᴴ).trace = 1) : FactorNormalized V := by
  intro i
  rw [Finset.sum_comm]
  simpa only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, mul_comm] using hV i

/-- Kraus operators for simplex preparation followed by the prepared states. -/
def phaseK (a b : ℂ) (V : Label m → Matrix B J ℂ) (p : Label m × J) :
    Matrix (Ref m × B) Q ℂ :=
  fun r q => column a b p.1 r.1 q * V p.1 r.2 p.2

omit [DecidableEq B] [DecidableEq J] in
theorem phaseK_gram_entry [DecidableEq B] [DecidableEq J] (a b : ℂ) (V : Label m → Matrix B J ℂ)
    (hV : FactorNormalized V) (i : Label m) (p q : Q) :
    (∑ j, ((phaseK a b V (i,j))ᴴ * phaseK a b V (i,j))) p q =
      ((prepK a b i)ᴴ * prepK a b i) p q := by
  rw [prepK_gram_entry]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    phaseK, Fintype.sum_prod_type, star_mul']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  calc
    (∑ j, ∑ x, star (column a b i s p) * star (V i x j) *
        (column a b i s q * V i x j)) =
      (star (column a b i s p) * column a b i s q) *
        (∑ j, ∑ x, star (V i x j) * V i x j) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = star (column a b i s p) * column a b i s q := by rw [hV i, mul_one]

theorem phaseK_complete (a b : ℂ) (V : Label m → Matrix B J ℂ)
    (ha : ((Fintype.card m : ℂ)+1) * (star a * a) = 1)
    (hb : (2 * Fintype.card m : ℂ) * (star b * b) = 1)
    (hV : FactorNormalized V) :
    ∑ p : Label m × J, (phaseK a b V p)ᴴ * phaseK a b V p = 1 := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i : Label m, (prepK a b i)ᴴ * prepK a b i := by
      apply Finset.sum_congr rfl
      intro i _
      ext p q
      exact phaseK_gram_entry a b V hV i p q
    _ = 1 := prepK_complete a b ha hb

/-- An actual CPTP preparation channel for any normalized finite factor family. -/
def preparedChannelWith (a b : ℂ)
    (ha : ((Fintype.card m : ℂ)+1) * (star a * a) = 1)
    (hb : (2 * Fintype.card m : ℂ) * (star b * b) = 1)
    (V : Label m → Matrix B J ℂ) (hV : FactorNormalized V) :
    QuantumChannel Q (Ref m × B) :=
  GeneralKraus.channel (phaseK a b V) (phaseK_complete a b V ha hb hV)

def preparedChannel [Nonempty m] (V : Label m → Matrix B J ℂ)
    (hV : FactorNormalized V) : QuantumChannel Q (Ref m × B) :=
  preparedChannelWith (smallCoeff m) (largeCoeff m)
    smallCoeff_normalized largeCoeff_normalized V hV

def columnMatrix (a b : ℂ) (i : Label m) : Matrix (Ref m) Q ℂ :=
  column a b i

omit [Fintype m] [Fintype B] [DecidableEq B] [Fintype J] [DecidableEq J] in
theorem phaseK_sandwich_entry [Fintype m] [Fintype B] [DecidableEq B] [Fintype J] [DecidableEq J] (a b : ℂ) (V : Label m → Matrix B J ℂ)
    (i : Label m) (j : J) (X : Matrix Q Q ℂ) (r s : Ref m) (x y : B) :
    (phaseK a b V (i,j) * X * (phaseK a b V (i,j))ᴴ) (r,x) (s,y) =
      (columnMatrix a b i * X * (columnMatrix a b i)ᴴ) r s *
        (V i x j * star (V i y j)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [phaseK, columnMatrix, star_mul', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem preparedChannelWith_map_entry (a b : ℂ)
    (ha : ((Fintype.card m : ℂ)+1) * (star a * a) = 1)
    (hb : (2 * Fintype.card m : ℂ) * (star b * b) = 1)
    (V : Label m → Matrix B J ℂ) (hV : FactorNormalized V)
    (X : Matrix Q Q ℂ) (r s : Ref m) (x y : B) :
    ((preparedChannelWith a b ha hb V hV).map X) (r,x) (s,y) =
      ∑ i : Label m, (columnMatrix a b i * X * (columnMatrix a b i)ᴴ) r s *
        (V i * (V i)ᴴ) x y := by
  change (∑ p : Label m × J, phaseK a b V p * X * (phaseK a b V p)ᴴ)
    (r,x) (s,y) = _
  simp only [Fintype.sum_prod_type, Matrix.sum_apply, phaseK_sandwich_entry,
    ← Finset.mul_sum]
  rfl

theorem preparedChannel_map_entry [Nonempty m]
    (V : Label m → Matrix B J ℂ) (hV : FactorNormalized V)
    (X : Matrix Q Q ℂ) (r s : Ref m) (x y : B) :
    ((preparedChannel V hV).map X) (r,x) (s,y) =
      ∑ i : Label m,
        (columnMatrix (smallCoeff m) (largeCoeff m) i * X *
          (columnMatrix (smallCoeff m) (largeCoeff m) i)ᴴ) r s *
        (V i * (V i)ᴴ) x y :=
  preparedChannelWith_map_entry _ _ _ _ V hV X r s x y

theorem preparedChannel_block [Nonempty m]
    (V : Label m → Matrix B J ℂ) (hV : FactorNormalized V)
    (X : Matrix Q Q ℂ) (r s : Ref m) :
    GeneralKraus.block ((preparedChannel V hV).map X) r s =
      ∑ i : Label m,
        (columnMatrix (smallCoeff m) (largeCoeff m) i * X *
          (columnMatrix (smallCoeff m) (largeCoeff m) i)ᴴ) r s •
        (V i * (V i)ᴴ) := by
  ext x y
  simpa only [GeneralKraus.block, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul] using preparedChannel_map_entry V hV X r s x y

theorem preparedChannel_natural [Nonempty m]
    {C H : Type} [Fintype C] [DecidableEq C] [Fintype H] [DecidableEq H]
    (N : Matrix B B ℂ →ₗ[ℂ] Matrix C C ℂ)
    (V : Label m → Matrix B J ℂ) (hV : FactorNormalized V)
    (W : Label m → Matrix C H ℂ) (hW : FactorNormalized W)
    (hNW : ∀ i, N (V i * (V i)ᴴ) = W i * (W i)ᴴ)
    (X : Matrix Q Q ℂ) :
    amplify N ((preparedChannel V hV).map X) = (preparedChannel W hW).map X := by
  ext ⟨r,x⟩ ⟨s,y⟩
  change N (GeneralKraus.block ((preparedChannel V hV).map X) r s) x y = _
  rw [preparedChannel_block, map_sum]
  simp_rw [map_smul, hNW]
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
    (preparedChannel_map_entry W hW X r s x y).symm

theorem column_cross_sum (a b : ℂ) (r s : Ref m) :
    (∑ i : Label m, (columnMatrix a b i *
      Matrix.single (0 : Q) (1 : Q) (1 : ℂ) * (columnMatrix a b i)ᴴ) r s) = 0 := by
  simp_rw [KrausSaturation.matrixUnit_sandwich_entry]
  cases r <;> cases s <;>
    simp [columnMatrix, column, flag, simplex, Fintype.sum_option, apply_ite,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]

/-- A common marginal for the prepared states erases the phase cross term. -/
theorem prepared_cross_marginal [Nonempty m]
    {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (V : Label m → Matrix (S × A) J ℂ) (hV : FactorNormalized V)
    (T : Matrix S S ℂ)
    (hT : ∀ i, CMICounterexample.partialTraceMatrix (V i * (V i)ᴴ) = T)
    (r s : Ref m) (x y : S) :
    (∑ z : A, ((preparedChannel V hV).map
      (Matrix.single (0 : Q) (1 : Q) (1 : ℂ))) (r,(x,z)) (s,(y,z))) = 0 := by
  simp_rw [preparedChannel_map_entry]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hentry : ∀ i : Label m, (∑ z : A, (V i * (V i)ᴴ) (x,z) (y,z)) = T x y := by
    intro i
    exact congrArg (fun M : Matrix S S ℂ => M x y) (hT i)
  simp_rw [hentry]
  rw [← Finset.sum_mul, column_cross_sum, zero_mul]

/-- The square output decoder places its result in the flag row. -/
def squareDecoder (a b : ℂ) (L : Matrix B (m × B) ℂ) :
    Matrix (Ref m × B) (Ref m × B) ℂ :=
  fun r s => match r.1, s.1 with
  | none, some t => (a / b) * L r.2 (t,s.2)
  | _, _ => 0

theorem squareDecoder_intertwines (a b : ℂ) (hb : b ≠ 0)
    (V : Label m → Matrix B J ℂ) (L : Matrix B (m × B) ℂ)
    (hL : L * simplexColumns V = plainColumns V) (p : Label m × J) :
    squareDecoder a b L *ᵥ (fun r => phaseK a b V p r 1) =
      fun r => phaseK a b V p r 0 := by
  ext r
  rcases r with ⟨s,x⟩
  cases s with
  | some t =>
      simp [Matrix.mulVec, dotProduct, squareDecoder, phaseK, column, flag]
  | none =>
      have hcol := congrFun (decoder_column V L hL p.1 p.2) x
      change (∑ r : m × B, L x r * (simplex p.1 (some r.1) * V p.1 r.2 p.2)) =
        V p.1 x p.2 at hcol
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
        Fintype.sum_option, squareDecoder, phaseK, column]
      norm_num only [show (1 : Q) ≠ 0 by decide, if_false, if_true,
        flag_none, simplex_none_right, mul_zero, zero_mul, Finset.sum_const_zero,
        zero_add, mul_one]
      calc
        (∑ t, ∑ y, a / b * L x (t,y) *
            (b * simplex p.1 (some t) * V p.1 y p.2)) =
          a * (∑ t, ∑ y, L x (t,y) *
            (simplex p.1 (some t) * V p.1 y p.2)) := by
              simp only [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro t _
              apply Finset.sum_congr rfl
              intro y _
              field_simp
              all_goals ring
        _ = a * V p.1 x p.2 := by
          rw [Fintype.sum_prod_type] at hcol
          rw [hcol]

theorem prepared_intertwiner [Nonempty m] (V : Label m → Matrix B J ℂ)
    (hzero : ∀ w : B → ℂ, (∀ i, w ∈ LinearMap.range (V i).toLin') → w = 0) :
    ∃ D : Matrix (Ref m × B) (Ref m × B) ℂ,
      ∀ p, D *ᵥ (fun r => phaseK (smallCoeff m) (largeCoeff m) V p r 1) =
        fun r => phaseK (smallCoeff m) (largeCoeff m) V p r 0 := by
  obtain ⟨L,hL⟩ := exists_decoder V hzero
  have hb : largeCoeff m ≠ 0 := by
    intro hz
    have h := largeCoeff_normalized (m:=m)
    rw [hz] at h
    simp at h
  exact ⟨squareDecoder (smallCoeff m) (largeCoeff m) L,
    squareDecoder_intertwines _ _ hb V L hL⟩

theorem prepared_completeCoefficient_eq_one [Nonempty m]
    (V : Label m → Matrix B J ℂ) (hV : FactorNormalized V)
    (hzero : ∀ w : B → ℂ, (∀ i, w ∈ LinearMap.range (V i).toLin') → w = 0)
    (γ : ℝ) (hγ : 1 < γ) :
    KrausChannelSaturation.completeCoefficient (preparedChannel V hV) γ = 1 := by
  obtain ⟨D,hD⟩ := prepared_intertwiner V hzero
  exact KrausChannelSaturation.completeCoefficient_eq_one_of_kraus
    (preparedChannel V hV) (phaseK (smallCoeff m) (largeCoeff m) V) D
    (fun _ => rfl) hD γ hγ

end Prepared

section DensityPrepared
open scoped MatrixOrder
variable {B : Type} [Fintype B] [DecidableEq B]

def densityFactors (ρ : Label m → Density B) (i : Label m) : Matrix B B ℂ :=
  CFC.sqrt (ρ i).mat

omit [Fintype m] [DecidableEq m] in
@[simp] theorem densityFactors_product [Fintype m] [DecidableEq m] (ρ : Label m → Density B) (i : Label m) :
    densityFactors ρ i * (densityFactors ρ i)ᴴ = (ρ i).mat := by
  have hroot : (CFC.sqrt (ρ i).mat).PosSemidef := (CFC.sqrt_nonneg (ρ i).mat).posSemidef
  rw [densityFactors, hroot.1.eq, CFC.sqrt_mul_sqrt_self _ (ρ i).positive.nonneg]

theorem densityFactors_normalized (ρ : Label m → Density B) :
    FactorNormalized (densityFactors ρ) := by
  apply factorNormalized_of_trace
  intro i
  rw [densityFactors_product]
  exact (ρ i).normalized

theorem densityFactors_range (ρ : Label m → Density B) (i : Label m) :
    LinearMap.range (densityFactors ρ i).toLin' = LinearMap.range (ρ i).mat.toLin' := by
  have h := KrausSupport.range_self_mul_conjTranspose (densityFactors ρ i)
  rw [densityFactors_product] at h
  exact h.symm

/-- Simplex preparation of an arbitrary finite family of actual density matrices. -/
def preparedDensityChannel [Nonempty m] (ρ : Label m → Density B) :
    QuantumChannel Q (Ref m × B) :=
  preparedChannel (densityFactors ρ) (densityFactors_normalized ρ)

theorem preparedDensityChannel_map_entry [Nonempty m]
    (ρ : Label m → Density B) (X : Matrix Q Q ℂ) (r s : Ref m) (x y : B) :
    ((preparedDensityChannel ρ).map X) (r,x) (s,y) =
      ∑ i : Label m,
        (columnMatrix (smallCoeff m) (largeCoeff m) i * X *
          (columnMatrix (smallCoeff m) (largeCoeff m) i)ᴴ) r s * (ρ i).mat x y := by
  simpa only [preparedDensityChannel, densityFactors_product] using
    preparedChannel_map_entry (densityFactors ρ) (densityFactors_normalized ρ) X r s x y

theorem preparedDensityChannel_natural [Nonempty m]
    {C : Type} [Fintype C] [DecidableEq C]
    (N : Matrix B B ℂ →ₗ[ℂ] Matrix C C ℂ)
    (ρ : Label m → Density B) (σ : Label m → Density C)
    (hN : ∀ i, N (ρ i).mat = (σ i).mat) (X : Matrix Q Q ℂ) :
    amplify N ((preparedDensityChannel ρ).map X) = (preparedDensityChannel σ).map X := by
  apply preparedChannel_natural
  intro i
  simpa only [densityFactors_product] using hN i

theorem preparedDensity_cross_marginal [Nonempty m]
    {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (ρ : Label m → Density (S × A)) (T : Matrix S S ℂ)
    (hT : ∀ i, CMICounterexample.partialTraceMatrix (ρ i).mat = T)
    (r s : Ref m) (x y : S) :
    (∑ z : A, ((preparedDensityChannel ρ).map
      (Matrix.single (0 : Q) (1 : Q) (1 : ℂ))) (r,(x,z)) (s,(y,z))) = 0 := by
  apply prepared_cross_marginal (densityFactors ρ) (densityFactors_normalized ρ) T
  intro i
  simpa only [densityFactors_product] using hT i

theorem preparedDensity_intertwiner [Nonempty m]
    (ρ : Label m → Density B)
    (hzero : ∀ w : B → ℂ, (∀ i, w ∈ LinearMap.range (ρ i).mat.toLin') → w = 0) :
    ∃ D : Matrix (Ref m × B) (Ref m × B) ℂ,
      D * (preparedDensityChannel ρ).map (Matrix.single (1 : Q) (1 : Q) 1) * Dᴴ =
          (preparedDensityChannel ρ).map (Matrix.single (0 : Q) (0 : Q) 1) ∧
      (preparedDensityChannel ρ).map (Matrix.single (0 : Q) (1 : Q) 1) =
          D * (preparedDensityChannel ρ).map (Matrix.single (1 : Q) (1 : Q) 1) := by
  have hz : ∀ w : B → ℂ,
      (∀ i, w ∈ LinearMap.range (densityFactors ρ i).toLin') → w = 0 := by
    intro w hw
    apply hzero w
    intro i
    rw [← densityFactors_range ρ i]
    exact hw i
  obtain ⟨D,hD⟩ := prepared_intertwiner (densityFactors ρ) hz
  refine ⟨D, ?_⟩
  exact KrausSaturation.kraus_channel_intertwining
    (preparedDensityChannel ρ)
    (phaseK (smallCoeff m) (largeCoeff m) (densityFactors ρ)) D
    (fun _ => rfl) hD

end DensityPrepared

end
end SimplexPreparation
