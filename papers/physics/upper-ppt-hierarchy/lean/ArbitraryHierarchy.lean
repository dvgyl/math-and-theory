import ChainGap
import GenericHierarchy
import ReverseOrbit

open scoped BigOperators ComplexOrder

noncomputable section
namespace UpperNoncollapse

open BellBridge Matrix

/-- The actual arbitrary-depth upper PPT SDP, with unrestricted complex auxiliaries.
The chain includes its input at index zero and has q sandwich constraints. -/
def MatrixChain (n q : ℕ) (ρ : CMatrix n) (S : ℕ → CMatrix n) : Prop :=
  S 0 = ρ ∧ (∀ i, i < q → KappaMatrix.sandwich n (S i) (S (i+1))) ∧
    (pt n (S q)).PosSemidef

def matrixValues (n q : ℕ) (ρ : CMatrix n) : Set ℝ :=
  {r | ∃ S, MatrixChain n q ρ S ∧ (Matrix.trace (S q)).re = r}

noncomputable def kappa (n q : ℕ) (ρ : CMatrix n) : ℝ :=
  sInf (matrixValues n q ρ)

theorem matrix_values_bddBelow (n q : ℕ) (ρ : CMatrix n) :
    BddBelow (matrixValues n q ρ) := by
  refine ⟨0, ?_⟩
  rintro r ⟨S, hS, rfl⟩
  have h := KappaGeneric.psd_trace_nonnegative hS.2.2
  exact h

theorem kappa_le_chain (n q : ℕ) {ρ : CMatrix n} {S : ℕ → CMatrix n}
    (hS : MatrixChain n q ρ S) : kappa n q ρ ≤ (Matrix.trace (S q)).re := by
  apply csInf_le (matrix_values_bddBelow n q ρ)
  exact ⟨S, hS, rfl⟩

/-- Positive Bell coefficients record a full-support Bell-diagonal density matrix. -/
def PositiveBellState (n : ℕ) (ρ : CMatrix n) : Prop :=
  ∃ x : BIndex n → ℝ, (∀ j, 0 < x j) ∧ (∑ j, x j) = 1 ∧ ρ = synth n x

theorem matrix_chain_auxiliary_psd (n q : ℕ) {ρ : CMatrix n}
    {S : ℕ → CMatrix n} (hS : MatrixChain n q ρ S) {i : ℕ} (hi : i < q) :
    (S (i+1)).PosSemidef := KappaMatrix.sandwich_psd n (hS.2.1 i hi)

theorem matrix_chain_trace_eq_re (n q : ℕ) (hq : 1 ≤ q) {ρ : CMatrix n}
    {S : ℕ → CMatrix n} (hS : MatrixChain n q ρ S) :
    Matrix.trace (S q) = ((Matrix.trace (S q)).re : ℂ) := by
  have hi : q-1 < q := by omega
  have he : q-1+1 = q := by omega
  have hh := KappaMatrix.sandwich_trace_eq_re n (hS.2.1 (q-1) hi)
  simpa only [he] using hh

/-- An explicit indexing check against the previously verified level-two SDP. -/
theorem matrixValues_two (n : ℕ) (ρ : CMatrix n) :
    matrixValues n 2 ρ = KappaMatrix.values2 n ρ := by
  ext r
  constructor
  · rintro ⟨S, hS, hr⟩
    refine ⟨S 1, S 2, ?_, hr⟩
    refine ⟨?_, hS.2.1 1 (by omega), hS.2.2⟩
    have hh := hS.2.1 0 (by omega)
    simpa only [hS.1, Nat.zero_add] using hh
  · rintro ⟨A, B, hf, hr⟩
    let S : ℕ → CMatrix n := fun i => if i = 0 then ρ else if i = 1 then A else B
    refine ⟨S, ?_, ?_⟩
    · refine ⟨by simp [S], ?_, by simpa [S] using hf.2.2⟩
      intro i hi
      have hc : i = 0 ∨ i = 1 := by omega
      rcases hc with rfl | rfl
      · simpa [S] using hf.1
      · simpa [S] using hf.2.1
    · simpa [S] using hr

theorem kappa_two (n : ℕ) (ρ : CMatrix n) :
    kappa n 2 ρ = KappaMatrix.kappa2 n ρ := by
  unfold kappa KappaMatrix.kappa2
  rw [matrixValues_two]

section Bell
variable (n : ℕ) (H : FoldSystem (BIndex n))
variable (hT : H.T = KappaCertificate.realMat (T n))

include hT in
theorem apply_eq_transform (x : BIndex n → ℝ) : H.apply x = transform n x := by
  unfold FoldSystem.apply
  rw [hT]
  rfl

include hT in
theorem synth_sandwich_of_fold {x y : BIndex n → ℝ} (h : H.Sandwich x y) :
    KappaMatrix.sandwich n (synth n x) (synth n y) := by
  apply KappaMatrix.synth_sandwich
  constructor
  · intro i
    change transform n x i ≤ y i
    rw [← apply_eq_transform n H hT]
    exact (le_abs_self _).trans (h i)
  · intro i
    change -transform n x i ≤ y i
    rw [← apply_eq_transform n H hT]
    exact (neg_le_abs _).trans (h i)

include hT in
theorem extract_chain (q : ℕ) (x : BIndex n → ℝ) {S : ℕ → CMatrix n}
    (hS : MatrixChain n q (synth n x) S) :
    H.Chain q x (fun i => expect n (S i)) := by
  refine ⟨?_, ?_, ?_⟩
  · change expect n (S 0) = x
    rw [hS.1, expect_synth]
  · intro i hi j
    have hs := KappaMatrix.extract_sandwich n (hS.2.1 i hi)
    have h₁ := hs.1 j
    have h₂ := hs.2 j
    change transform n (expect n (S i)) j ≤ expect n (S (i+1)) j at h₁
    change -transform n (expect n (S i)) j ≤ expect n (S (i+1)) j at h₂
    rw [apply_eq_transform n H hT]
    exact abs_le.mpr ⟨by linarith, h₁⟩
  · intro j
    have hp := expect_nonneg n (pt n (S q)) hS.2.2 j
    rw [expect_pt, ← apply_eq_transform n H hT] at hp
    exact hp

include hT in
theorem synth_chain (q : ℕ) (s : ℕ → BIndex n → ℝ)
    (hs : H.Chain q (s 0) s) :
    MatrixChain n q (synth n (s 0)) (fun i => synth n (s i)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i hi
    exact synth_sandwich_of_fold n H hT (hs.2.1 i hi)
  · rw [pt_synth, ← apply_eq_transform n H hT]
    exact synth_psd n _ hs.2.2

include hT in
theorem matrix_values_nonempty (q : ℕ) (hq : 1 ≤ q) (x : BIndex n → ℝ) :
    (matrixValues n q (synth n x)).Nonempty := by
  let M : ℝ := ∑ j, |H.apply x j|
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hbound : ∀ j, |H.apply x j| ≤ M := by
    intro j
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j => |H.apply x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  have hconst : H.apply (fun _ => M) = fun _ => M := by
    funext j
    change (∑ k, H.T j k * M) = M
    rw [← Finset.sum_mul, H.row_sum, one_mul]
  let s : ℕ → BIndex n → ℝ := fun i => if i = 0 then x else fun _ => M
  have hs : H.Chain q x s := by
    refine ⟨by simp [s], ?_, ?_⟩
    · intro i _ j
      by_cases hi : i = 0
      · subst i
        simpa [s, FoldSystem.Sandwich] using hbound j
      · change |H.apply (s i) j| ≤ s (i+1) j
        simp only [s, if_neg hi, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          if_false, hconst, abs_of_nonneg hM]
        rfl
    · intro j
      have hq0 : q ≠ 0 := by omega
      simp only [s, if_neg hq0, hconst]
      exact hM
  have hmat := synth_chain n H hT q s (by simpa only [show s 0 = x from hs.1] using hs)
  refine ⟨(Matrix.trace (synth n (s q))).re, ?_⟩
  refine ⟨(fun i => synth n (s i)), ?_, rfl⟩
  simpa only [show s 0 = x from hs.1] using hmat

end Bell

namespace FoldSystem
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem chain_smul (H : FoldSystem ι) {q : ℕ} {x : ι → ℝ}
    {s : ℕ → ι → ℝ} (hs : H.Chain q x s) {c : ℝ} (hc : 0 ≤ c) :
    H.Chain q (c • x) (fun i => c • s i) := by
  refine ⟨?_, ?_, ?_⟩
  · change c • s 0 = c • x
    rw [hs.1]
  · intro i hi j
    rw [H.apply_smul]
    change |c * H.apply (s i) j| ≤ c * s (i+1) j
    rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (hs.2.1 i hi j) hc
  · intro j
    rw [H.apply_smul]
    exact mul_nonneg hc (hs.2.2 j)

end FoldSystem

/-- Any full-support folding orbit supplied to this theorem produces a normalized
physical state with a strict separation between consecutive original upper SDPs.
The lower bound ranges over arbitrary complex auxiliary matrices. -/
theorem positive_bell_gap_of_orbit (n q : ℕ) (hq : 1 ≤ q)
    (H : FoldSystem (BIndex n))
    (hT : H.T = KappaCertificate.realMat (T n))
    (a : ℕ → BIndex n → ℝ)
    (hfold : ∀ i, i < q+1 → a (i+1) = H.fold (a i))
    (hpos : ∀ i, i ≤ q+1 → ∀ j, (1:ℝ)/2 ≤ a i j)
    (hlast : a (q+1) = fun _ => 1)
    (hnegative : ∃ j, H.apply (a q) j ≤ -1)
    (hnorm : (∑ j, a 0 j ^ 2) = H.d ^ 2) :
    ∃ ρ : CMatrix n, KappaMatrix.QuantumState n ρ ∧ PositiveBellState n ρ ∧
      kappa n (q+1) ρ < kappa n q ρ := by
  let c : ℝ := FoldSystem.total (a 0)
  have hc : 0 < c := by
    obtain ⟨j, _⟩ := hnegative
    have hnonneg : ∀ j, 0 ≤ a 0 j := fun j => le_trans (by norm_num) (hpos 0 (by omega) j)
    have hsingle : a 0 j ≤ c := Finset.single_le_sum (s := Finset.univ)
      (f := a 0) (fun j _ => hnonneg j) (Finset.mem_univ j)
    have h := hpos 0 (by omega) j
    linarith
  have hc0 : c ≠ 0 := ne_of_gt hc
  let x : BIndex n → ℝ := c⁻¹ • a 0
  let ρ := synth n x
  have hx : ∀ j, 0 ≤ x j := by
    intro j
    exact mul_nonneg (inv_nonneg.mpr hc.le) ((by norm_num : (0:ℝ) ≤ 1/2).trans (hpos 0 (by omega) j))
  have hsum : (∑ j, x j) = 1 := by
    change (∑ j, c⁻¹ * a 0 j) = 1
    rw [← Finset.mul_sum]
    change c⁻¹ * c = 1
    exact inv_mul_cancel₀ hc0
  have hstate : KappaMatrix.QuantumState n ρ := by
    refine ⟨synth_psd n x hx, ?_⟩
    rw [trace_synth, hsum]
    norm_num
  let s : ℕ → BIndex n → ℝ := fun i => c⁻¹ • a i
  have hs : H.Chain (q+1) x s := by
    refine ⟨rfl, ?_, ?_⟩
    · intro i hi j
      rw [H.apply_smul]
      change |c⁻¹ * H.apply (a i) j| ≤ c⁻¹ * a (i+1) j
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hc.le), hfold i hi]
      rfl
    · intro j
      rw [H.apply_smul, hlast, H.apply_one]
      change 0 ≤ c⁻¹ * 1
      positivity
  have hmat : MatrixChain n (q+1) ρ (fun i => synth n (s i)) :=
    synth_chain n H hT (q+1) s hs
  have hupper : kappa n (q+1) ρ ≤ H.d^2 / c := by
    have hu := kappa_le_chain n (q+1) hmat
    have htrace : (Matrix.trace (synth n (s (q+1)))).re = H.d^2/c := by
      rw [trace_synth]
      simp only [s, hlast, Pi.smul_apply, smul_eq_mul, mul_one,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Complex.ofReal_re, H.card_eq]
      ring
    exact htrace ▸ hu
  let δ : ℝ := 1 / (2*(H.d+1)^(q+1))
  have hδ : 0 < δ := by
    have hd := H.d_pos
    dsimp [δ]
    positivity
  have hlower : (H.d^2+δ)/c ≤ kappa n q ρ := by
    apply le_csInf (matrix_values_nonempty n H hT q hq x)
    rintro r ⟨S, hS, rfl⟩
    have he := extract_chain n H hT q x hS
    have hraw := H.chain_smul he hc.le
    have hinput : c • x = a 0 := by
      dsimp [x]
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    rw [hinput] at hraw
    have hg := H.chain_gap q a hfold hpos hlast hnegative hnorm
      (fun i => c • expect n (S i)) hraw
    have htotal : FoldSystem.total (c • expect n (S q)) = c * (Matrix.trace (S q)).re := by
      simp only [FoldSystem.total, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_expect]
    rw [htotal] at hg
    apply (div_le_iff₀ hc).2
    dsimp [δ]
    nlinarith
  have hpositive : ∀ j, 0 < x j := by
    intro j
    have ha : 0 < a 0 j := lt_of_lt_of_le (by norm_num) (hpos 0 (by omega) j)
    exact mul_pos (inv_pos.mpr hc) ha
  refine ⟨ρ, hstate, ⟨x, hpositive, hsum, rfl⟩, ?_⟩
  have hstrict : H.d^2/c < (H.d^2+δ)/c := by
    apply (div_lt_div_iff_of_pos_right hc).2
    linarith
  exact hupper.trans_lt (hstrict.trans_le hlower)

/-- The core strict separation, omitting the optional coefficient description. -/
theorem physical_gap_of_orbit (n q : ℕ) (hq : 1 ≤ q)
    (H : FoldSystem (BIndex n))
    (hT : H.T = KappaCertificate.realMat (T n))
    (a : ℕ → BIndex n → ℝ)
    (hfold : ∀ i, i < q+1 → a (i+1) = H.fold (a i))
    (hpos : ∀ i, i ≤ q+1 → ∀ j, (1:ℝ)/2 ≤ a i j)
    (hlast : a (q+1) = fun _ => 1)
    (hnegative : ∃ j, H.apply (a q) j ≤ -1)
    (hnorm : (∑ j, a 0 j ^ 2) = H.d ^ 2) :
    ∃ ρ : CMatrix n, KappaMatrix.QuantumState n ρ ∧
      kappa n (q+1) ρ < kappa n q ρ := by
  obtain ⟨ρ, hρ, _, hg⟩ := positive_bell_gap_of_orbit n q hq H hT a
    hfold hpos hlast hnegative hnorm
  exact ⟨ρ, hρ, hg⟩

/-- The structural bridge from a reverse orbit to the actual matrix SDP. -/
theorem positive_bell_gap_of_reverse_orbit (n q : ℕ) (hq : 1 ≤ q)
    (H : FoldSystem (BIndex n))
    (hT : H.T = KappaCertificate.realMat (T n))
    (r : PositiveReverseOrbit H q) :
    ∃ ρ : CMatrix n, KappaMatrix.QuantumState n ρ ∧ PositiveBellState n ρ ∧
      kappa n (q+1) ρ < kappa n q ρ := by
  let a : ℕ → BIndex n → ℝ := fun i => r.v (q+1-i)
  apply positive_bell_gap_of_orbit n q hq H hT a
  · intro i hi
    have hk : q-i ≤ q := Nat.sub_le _ _
    have hh := r.backward (q-i) hk
    have h₁ : q+1-(i+1) = q-i := by omega
    have h₂ : q+1-i = q-i+1 := by omega
    change r.v (q+1-(i+1)) = H.fold (r.v (q+1-i))
    rw [h₁, h₂]
    exact hh.symm
  · intro i _ j
    exact r.positive (q+1-i) (Nat.sub_le _ _) j
  · change r.v (q+1-(q+1)) = fun _ => 1
    simpa using r.initial
  · change ∃ j, H.apply (r.v (q+1-q)) j ≤ -1
    simpa using r.defect
  · change (∑ j, r.v (q+1-0) j ^ 2) = H.d^2
    simpa using r.norm (q+1) le_rfl

theorem physical_gap_of_reverse_orbit (n q : ℕ) (hq : 1 ≤ q)
    (H : FoldSystem (BIndex n))
    (hT : H.T = KappaCertificate.realMat (T n))
    (r : PositiveReverseOrbit H q) :
    ∃ ρ : CMatrix n, KappaMatrix.QuantumState n ρ ∧
      kappa n (q+1) ρ < kappa n q ρ := by
  obtain ⟨ρ, hρ, _, hg⟩ := positive_bell_gap_of_reverse_orbit n q hq H hT r
  exact ⟨ρ, hρ, hg⟩

end UpperNoncollapse
