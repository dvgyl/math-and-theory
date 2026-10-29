module
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
Finite-dimensional determinant jet transfer. A matrix-vector residual that
vanishes through order two forces the same vanishing for the determinant,
provided one component of the vector is one at zero. This is an ordinary
calculus theorem, intended to connect actual Poisson correctors to the first
two characteristic-polynomial cumulants without assuming a Perron branch.
-/
namespace UnicyclicJets
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000

def ZeroJet2 (f : ℝ → ℝ) : Prop :=
  f 0 = 0 ∧ deriv f 0 = 0 ∧ deriv (deriv f) 0 = 0

theorem second_deriv_mul (a b : ℝ → ℝ)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) :
    deriv (deriv (fun x => a x*b x)) 0 =
      deriv (deriv a) 0*b 0 + 2*deriv a 0*deriv b 0 +
        a 0*deriv (deriv b) 0 := by
  have ha' : ContDiff ℝ 1 (deriv a) := (contDiff_succ_iff_deriv.mp ha).2.2
  have hb' : ContDiff ℝ 1 (deriv b) := (contDiff_succ_iff_deriv.mp hb).2.2
  have hfirst : deriv (fun x => a x*b x) =
      (fun x => deriv a x*b x+a x*deriv b x) := by
    funext x
    exact (((ha.differentiable (by norm_num) x).hasDerivAt).mul
      ((hb.differentiable (by norm_num) x).hasDerivAt)).deriv
  rw [hfirst]
  have h := ((((ha'.differentiable (by norm_num) 0).hasDerivAt).mul
      ((hb.differentiable (by norm_num) 0).hasDerivAt)).add
    (((ha.differentiable (by norm_num) 0).hasDerivAt).mul
      ((hb'.differentiable (by norm_num) 0).hasDerivAt))).deriv
  convert h using 1 ; ring

theorem zeroJet2_mul (a b : ℝ → ℝ)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (hz : ZeroJet2 b) :
    ZeroJet2 (fun x => a x*b x) := by
  rcases hz with ⟨h0,h1,h2⟩
  refine ⟨by simp [h0], ?_, ?_⟩
  · rw [deriv_mul (ha.differentiable (by norm_num) 0) (hb.differentiable (by norm_num) 0)]
    simp [h0,h1]
  · rw [second_deriv_mul a b ha hb]
    simp [h0,h1,h2]

theorem zeroJet2_cancel (a b : ℝ → ℝ)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (hb0 : b 0 = 1)
    (hz : ZeroJet2 (fun x => a x*b x)) : ZeroJet2 a := by
  rcases hz with ⟨h0,h1,h2⟩
  have ha0 : a 0 = 0 := by simpa [hb0] using h0
  have ha1 : deriv a 0 = 0 := by
    rw [deriv_mul (ha.differentiable (by norm_num) 0) (hb.differentiable (by norm_num) 0)] at h1
    simpa [hb0,ha0] using h1
  have ha2 : deriv (deriv a) 0 = 0 := by
    rw [second_deriv_mul a b ha hb] at h2
    simpa [hb0,ha0,ha1] using h2
  exact ⟨ha0,ha1,ha2⟩

theorem zeroJet2_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i))
    (hz : ∀ i ∈ s, ZeroJet2 (f i)) :
    ZeroJet2 (fun x => ∑ i ∈ s, f i x) := by
  have hfirst : deriv (fun x => ∑ i ∈ s, f i x) =
      (fun x => ∑ i ∈ s, deriv (f i) x) := by
    funext x
    exact (HasDerivAt.sum (fun i hi => ((hf i hi).differentiable (by norm_num) x).hasDerivAt)).deriv
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.sum_eq_zero (fun i hi => (hz i hi).1)
  · rw [hfirst]
    exact Finset.sum_eq_zero (fun i hi => (hz i hi).2.1)
  · rw [hfirst]
    have hf' : ∀ i ∈ s, ContDiff ℝ 1 (deriv (f i)) :=
      fun i hi => (contDiff_succ_iff_deriv.mp (hf i hi)).2.2
    have hh := (HasDerivAt.sum (fun i hi =>
      ((hf' i hi).differentiable (by norm_num) 0).hasDerivAt)).deriv
    rw [hh]
    exact Finset.sum_eq_zero (fun i hi => (hz i hi).2.2)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem contDiff_det (A : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiff ℝ 2 (fun x => A x i j)) :
    ContDiff ℝ 2 (fun x => (A x).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum (fun p _ =>
    contDiff_const.mul (contDiff_prod (fun j _ => hA (p j) j)))

theorem contDiff_adjugate (A : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiff ℝ 2 (fun x => A x i j)) (i j : ι) :
    ContDiff ℝ 2 (fun x => (A x).adjugate i j) := by
  simp_rw [Matrix.adjugate_apply]
  apply contDiff_det
  intro k l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne hk]
    exact hA k l

omit [Fintype ι] [DecidableEq ι] in
theorem contDiff_mulVec [Fintype ι] [DecidableEq ι] (A : ℝ → Matrix ι ι ℝ) (v : ℝ → ι → ℝ)
    (hA : ∀ i j, ContDiff ℝ 2 (fun x => A x i j))
    (hv : ∀ i, ContDiff ℝ 2 (fun x => v x i)) (i : ι) :
    ContDiff ℝ 2 (fun x => (A x).mulVec (v x) i) := by
  change ContDiff ℝ 2 (fun x => ∑ j, A x i j*v x j)
  exact ContDiff.sum (fun j _ => (hA i j).mul (hv j))

theorem determinant_zero_jet_of_residual
    (A : ℝ → Matrix ι ι ℝ) (v : ℝ → ι → ℝ) (i : ι)
    (hA : ∀ j k, ContDiff ℝ 2 (fun x => A x j k))
    (hv : ∀ j, ContDiff ℝ 2 (fun x => v x j))
    (hvi : v 0 i = 1)
    (hz : ∀ j, ZeroJet2 (fun x => (A x).mulVec (v x) j)) :
    ZeroJet2 (fun x => (A x).det) := by
  have hleft : ZeroJet2 (fun x =>
      ∑ j, (A x).adjugate i j*((A x).mulVec (v x) j)) := by
    apply zeroJet2_sum
    · intro j _
      exact (contDiff_adjugate A hA i j).mul (contDiff_mulVec A v hA hv j)
    · intro j _
      exact zeroJet2_mul _ _ (contDiff_adjugate A hA i j)
        (contDiff_mulVec A v hA hv j) (hz j)
  have hid : (fun x => ∑ j, (A x).adjugate i j*((A x).mulVec (v x) j)) =
      (fun x => (A x).det*v x i) := by
    funext x
    change ((A x).adjugate).mulVec ((A x).mulVec (v x)) i = _
    rw [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec_assoc,Matrix.one_mulVec]
    rfl
  rw [hid] at hleft
  exact zeroJet2_cancel _ _ (contDiff_det A hA) (hv i) hvi hleft

#print axioms determinant_zero_jet_of_residual
end
end UnicyclicJets
