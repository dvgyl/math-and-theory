import UnilateralCHSH
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.RealVectorSpace

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set Filter
open scoped Topology

namespace UnilateralCHSH.Global

abbrev Pair := Vec × Vec

def feasible : Set Pair := {p | normSq p.1 = 1 ∧ dot p.1 p.2 = 0 ∧ normSq p.2 ≤ 1}

def objective (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) (p : Pair) : ℝ :=
  reducedObjective A C s t p.1 p.2

def coord (i : Fin 3) : Vec →L[ℝ] ℝ := ContinuousLinearMap.proj i

def covec (x : Vec) : Vec →L[ℝ] ℝ :=
  x 0 • coord 0 + x 1 • coord 1 + x 2 • coord 2

def first : Pair →L[ℝ] Vec := ContinuousLinearMap.fst ℝ Vec Vec
def second : Pair →L[ℝ] Vec := ContinuousLinearMap.snd ℝ Vec Vec

def pairCovec (x y : Vec) : Pair →L[ℝ] ℝ :=
  (covec x).comp first + (covec y).comp second

def matCLM (A : Matrix (Fin 3) (Fin 3) ℝ) : Vec →L[ℝ] Vec :=
  ContinuousLinearMap.pi fun i => covec (fun j => A i j)

@[simp] theorem covec_apply (x y : Vec) : covec x y = dot x y := by
  simp [covec, coord, dot]

@[simp] theorem first_apply (p : Pair) : first p = p.1 := rfl
@[simp] theorem second_apply (p : Pair) : second p = p.2 := rfl

@[simp] theorem pairCovec_apply (x y : Vec) (p : Pair) :
    pairCovec x y p = dot x p.1 + dot y p.2 := by
  simp [pairCovec]

@[simp] theorem matCLM_apply (A : Matrix (Fin 3) (Fin 3) ℝ) (x : Vec) :
    matCLM A x = matVec A x := by
  funext i
  simp [matCLM, matVec, dot]

theorem continuous_dot_maps (U V : Pair →L[ℝ] Vec) :
    Continuous (fun p : Pair => dot (U p) (V p)) := by
  have hu (i : Fin 3) : Continuous (fun p : Pair => U p i) :=
    (continuous_apply i).comp U.continuous
  have hv (i : Fin 3) : Continuous (fun p : Pair => V p i) :=
    (continuous_apply i).comp V.continuous
  exact ((hu 0 |>.mul (hv 0)).add (hu 1 |>.mul (hv 1))).add (hu 2 |>.mul (hv 2))

theorem strict_dot_maps (U V : Pair →L[ℝ] Vec) (p : Pair) :
    HasStrictFDerivAt (fun z : Pair => dot (U z) (V z))
      ((covec (U p)).comp V + (covec (V p)).comp U) p := by
  have hu (i : Fin 3) : HasStrictFDerivAt (fun z : Pair => U z i) ((coord i).comp U) p :=
    ((coord i).comp U).hasStrictFDerivAt
  have hv (i : Fin 3) : HasStrictFDerivAt (fun z : Pair => V z i) ((coord i).comp V) p :=
    ((coord i).comp V).hasStrictFDerivAt
  apply (((hu 0 |>.mul (hv 0)).add (hu 1 |>.mul (hv 1))).add (hu 2 |>.mul (hv 2))).congr_fderiv
  apply ContinuousLinearMap.ext
  intro z
  simp [covec, coord, dot]
  ring

theorem continuous_norm_first : Continuous (fun p : Pair => normSq p.1) :=
  continuous_dot_maps first first

theorem continuous_norm_second : Continuous (fun p : Pair => normSq p.2) :=
  continuous_dot_maps second second

theorem continuous_orth : Continuous (fun p : Pair => dot p.1 p.2) :=
  continuous_dot_maps first second

theorem continuous_objective (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    Continuous (objective A C s t) := by
  have h1 := continuous_dot_maps first ((matCLM A).comp first)
  have h2 := continuous_dot_maps second ((matCLM (shift A (-s))).comp second)
  have h3 := continuous_dot_maps second ((matCLM C).comp first)
  simpa only [objective, reducedObjective, first_apply, second_apply,
    ContinuousLinearMap.comp_apply, matCLM_apply] using
    ((continuous_const.sub h1).sub h2).sub (continuous_const.mul h3)

theorem strict_norm_first (p : Pair) :
    HasStrictFDerivAt (fun z : Pair => normSq z.1)
      (pairCovec (fun i => 2*p.1 i) 0) p := by
  apply (strict_dot_maps first first p).congr_fderiv
  apply ContinuousLinearMap.ext
  intro z
  simp [pairCovec, dot]
  ring

theorem strict_orth (p : Pair) :
    HasStrictFDerivAt (fun z : Pair => dot z.1 z.2) (pairCovec p.2 p.1) p := by
  apply (strict_dot_maps first second p).congr_fderiv
  apply ContinuousLinearMap.ext
  intro z
  simp [pairCovec]
  ring

theorem dot_add_left (x y z : Vec) : dot (x+y) z = dot x z+dot y z := by
  simp only [dot, Pi.add_apply]
  ring

theorem dot_sub_left (x y z : Vec) : dot (x-y) z = dot x z-dot y z := by
  simp only [dot, Pi.sub_apply]
  ring

theorem dot_scale_left (x y : Vec) (a : ℝ) :
    dot (fun i => a*x i) y = a*dot x y := by
  simp only [dot]
  ring

def gradN (A C : Matrix (Fin 3) (Fin 3) ℝ) (p : Pair) : Vec :=
  fun i => -2*(matVec A p.1 i-matVec C p.2 i)

def gradV (A C : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) (p : Pair) : Vec :=
  fun i => -2*(matVec (shift A (-s)) p.2 i+matVec C p.1 i)

theorem strict_objective (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) (p : Pair)
    (hsym : ∀ i j, A i j = A j i) (hskew : ∀ i j, C i j = -C j i) :
    HasStrictFDerivAt (objective A C s t)
      (pairCovec (gradN A C p) (gradV A C s p)) p := by
  have h1 := strict_dot_maps first ((matCLM A).comp first) p
  have h2 := strict_dot_maps second ((matCLM (shift A (-s))).comp second) p
  have h3 := strict_dot_maps second ((matCLM C).comp first) p
  have hraw := ((hasStrictFDerivAt_const (𝕜:=ℝ) t p |>.sub h1).sub h2).sub
    ((hasStrictFDerivAt_const (𝕜:=ℝ) (2:ℝ) p).mul h3)
  refine (hraw.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.zero_apply, smul_eq_mul, covec_apply,
      first_apply, second_apply, matCLM_apply, pairCovec_apply]
    have ha := symmetric_dot_exchange A p.1 z.1 hsym
    have hk := symmetric_dot_exchange (shift A (-s)) p.2 z.2 (shift_symmetric A (-s) hsym)
    have hc := skew_dot_exchange C p.2 z.1 hskew
    have hca := dot_symm (matVec A p.1) z.1
    have hck := dot_symm (matVec (shift A (-s)) p.2) z.2
    have hcc := dot_symm (matVec C p.1) z.2
    have hcd := dot_symm (matVec C p.2) z.1
    have hn : dot (fun i => -2*(matVec A p.1 i-matVec C p.2 i)) z.1 =
        -2*(dot (matVec A p.1) z.1-dot (matVec C p.2) z.1) := by
      simp only [dot]
      ring
    have hv : dot (fun i => -2*(matVec (shift A (-s)) p.2 i+matVec C p.1 i)) z.2 =
        -2*(dot (matVec (shift A (-s)) p.2) z.2+dot (matVec C p.1) z.2) := by
      simp only [dot]
      ring
    change _ = dot (fun i => -2*(matVec A p.1 i-matVec C p.2 i)) z.1 +
      dot (fun i => -2*(matVec (shift A (-s)) p.2 i+matVec C p.1 i)) z.2
    rw [hn, hv]
    linarith
  · intro z
    simp [objective, reducedObjective]

theorem coordinate_sq_le_normSq (x : Vec) (i : Fin 3) : (x i)^2 ≤ normSq x := by
  have hi : i=0 ∨ i=1 ∨ i=2 := by fin_cases i <;> simp [Fin.ext_iff]
  rcases hi with hi | hi | hi <;> rw [hi] <;>
    unfold normSq dot <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

theorem sup_norm_le_of_normSq_le_one (x : Vec) (hx : normSq x ≤ 1) : ‖x‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  rw [Real.norm_eq_abs]
  have hsq : (x i)^2 ≤ 1 := le_trans (coordinate_sq_le_normSq x i) hx
  apply abs_le.mpr
  constructor <;> nlinarith

theorem feasible_isClosed : IsClosed feasible := by
  exact (isClosed_eq continuous_norm_first continuous_const).inter
    ((isClosed_eq continuous_orth continuous_const).inter
      (isClosed_le continuous_norm_second continuous_const))

theorem feasible_isCompact : IsCompact feasible := by
  apply (isCompact_closedBall (0:Pair) 1).of_isClosed_subset feasible_isClosed
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le (sup_norm_le_of_normSq_le_one p.1 (le_of_eq hp.1))
    (sup_norm_le_of_normSq_le_one p.2 hp.2.2)

theorem feasible_nonempty : feasible.Nonempty := by
  refine ⟨(![1,0,0],0), ?_⟩
  norm_num [feasible, normSq, dot, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem exists_global_maximum (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    ∃ p ∈ feasible, IsMaxOn (objective A C s t) feasible p :=
  feasible_isCompact.exists_isMaxOn feasible_nonempty (continuous_objective A C s t).continuousOn

theorem exists_maximum_boundary_or_interior
    (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    ∃ p ∈ feasible, IsMaxOn (objective A C s t) feasible p ∧
      (normSq p.2 = 1 ∨ normSq p.2 < 1) := by
  obtain ⟨p, hp, hm⟩ := exists_global_maximum A C s t
  refine ⟨p, hp, hm, ?_⟩
  exact (lt_or_eq_of_le hp.2.2).symm

def constraint (i : Fin 2) (p : Pair) : ℝ :=
  if i=0 then normSq p.1 else dot p.1 p.2

def constraintD (p : Pair) (i : Fin 2) : Pair →L[ℝ] ℝ :=
  if i=0 then pairCovec (fun j => 2*p.1 j) 0 else pairCovec p.2 p.1

theorem strict_constraint (p : Pair) (i : Fin 2) :
    HasStrictFDerivAt (constraint i) (constraintD p i) p := by
  by_cases hi : i=0
  · have heq : constraint i = fun z : Pair => normSq z.1 := by
      funext z
      simp [constraint, hi]
    rw [heq]
    simpa [constraintD, hi] using strict_norm_first p
  · have heq : constraint i = fun z : Pair => dot z.1 z.2 := by
      funext z
      simp [constraint, hi]
    rw [heq]
    simpa [constraintD, hi] using strict_orth p

theorem interior_maximum_local_constraints
    (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) (p : Pair)
    (hp : p ∈ feasible) (hv : normSq p.2 < 1)
    (hmax : IsMaxOn (objective A C s t) feasible p) :
    IsLocalExtrOn (objective A C s t) {q | ∀ i : Fin 2, constraint i q=constraint i p} p := by
  apply Or.inr
  change ∀ᶠ q in 𝓝[{q | ∀ i : Fin 2, constraint i q=constraint i p}] p,
    objective A C s t q ≤ objective A C s t p
  have hball : {q : Pair | normSq q.2 < 1} ∈ 𝓝 p :=
    (isOpen_lt continuous_norm_second continuous_const).mem_nhds hv
  have hball' : ∀ᶠ q in 𝓝[{q | ∀ i : Fin 2, constraint i q=constraint i p}] p,
      normSq q.2 < 1 := Filter.Eventually.filter_mono nhdsWithin_le_nhds hball
  filter_upwards [hball', self_mem_nhdsWithin] with q hq hlevel
  have h0 := hlevel (0:Fin 2)
  have h1 := hlevel (1:Fin 2)
  simp only [constraint, if_pos rfl] at h0
  norm_num [constraint] at h1
  exact hmax ⟨h0.trans hp.1, h1.trans hp.2.1, le_of_lt hq⟩

@[simp] theorem dot_zero_right (x : Vec) : dot x 0 = 0 := by simp [dot]
@[simp] theorem dot_zero_left (x : Vec) : dot 0 x = 0 := by simp [dot]

theorem interior_maximum_lagrange
    (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) (p : Pair)
    (hsym : ∀ i j, A i j = A j i) (hskew : ∀ i j, C i j = -C j i)
    (hp : p ∈ feasible) (hv : normSq p.2 < 1)
    (hmax : IsMaxOn (objective A C s t) feasible p) :
    ∃ (L : Fin 2 → ℝ) (g : ℝ), g ≠ 0 ∧ ∀ z : Pair,
      L 0*(2*dot p.1 z.1)+L 1*(dot p.2 z.1+dot p.1 z.2)+
        g*(dot (gradN A C p) z.1+dot (gradV A C s p) z.2) = 0 := by
  have hext := interior_maximum_local_constraints A C s t p hp hv hmax
  obtain ⟨L, g, hnonzero, hsum⟩ :=
    hext.exists_multipliers_of_hasStrictFDerivAt (strict_constraint p)
      (strict_objective A C s t p hsym hskew)
  have hsum' : L 0 • pairCovec (fun j => 2*p.1 j) 0 +
      L 1 • pairCovec p.2 p.1 + g • pairCovec (gradN A C p) (gradV A C s p) = 0 := by
    simpa [Fin.sum_univ_two, constraintD] using hsum
  have hrel (z : Pair) :
      L 0*(2*dot p.1 z.1)+L 1*(dot p.2 z.1+dot p.1 z.2)+
        g*(dot (gradN A C p) z.1+dot (gradV A C s p) z.2) = 0 := by
    have h := congrArg (fun D : Pair →L[ℝ] ℝ => D z) hsum'
    simpa [pairCovec_apply, dot_scale_left] using h
  have hg : g ≠ 0 := by
    intro hg
    have h1 := hrel (0,p.1)
    simp only [dot_zero_right, zero_add, add_zero, hg, zero_mul, mul_zero] at h1
    rw [← normSq, hp.1, mul_one] at h1
    have h0 := hrel (p.1,0)
    simp only [dot_zero_right, zero_add, add_zero, hg, zero_mul, mul_zero, h1] at h0
    rw [← normSq, hp.1] at h0
    have hL0 : L 0 = 0 := by linarith
    have hL : L=0 := by
      funext i
      fin_cases i
      · exact hL0
      · exact h1
    apply hnonzero
    exact Prod.ext hL hg
  exact ⟨L, g, hg, hrel⟩

def axis (i : Fin 3) : Vec := Pi.single i 1

@[simp] theorem dot_axis (x : Vec) (i : Fin 3) : dot x (axis i) = x i := by
  have hi : i=0 ∨ i=1 ∨ i=2 := by fin_cases i <;> simp [Fin.ext_iff]
  rcases hi with hi | hi | hi <;> rw [hi] <;>
    norm_num [axis, dot, Pi.single_apply, Fin.ext_iff]

theorem interior_maximum_kkt
    (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) (p : Pair)
    (hsym : ∀ i j, A i j = A j i) (hskew : ∀ i j, C i j = -C j i)
    (hp : p ∈ feasible) (hv : normSq p.2 < 1)
    (hmax : IsMaxOn (objective A C s t) feasible p) :
    ∃ mu beta : ℝ,
      (matVec A p.1-matVec C p.2 = fun i => mu*p.1 i-beta*p.2 i) ∧
      (matVec (shift A (-s)) p.2+matVec C p.1 = fun i => -beta*p.1 i) := by
  obtain ⟨L, g, hg, hrel⟩ := interior_maximum_lagrange A C s t p hsym hskew hp hv hmax
  let mu := L 0/g
  let beta := -(L 1/(2*g))
  refine ⟨mu, beta, ?_, ?_⟩
  · funext i
    have hi := hrel (axis i,0)
    simp only [dot_axis, dot_zero_right, mul_zero, add_zero] at hi
    simp only [gradN] at hi
    simp only [Pi.sub_apply]
    dsimp only [mu, beta]
    field_simp
    have hm := congrArg (fun z : ℝ => z*g) hi
    dsimp only at hm
    nlinarith [hm]
  · funext i
    have hi := hrel (0,axis i)
    simp only [dot_axis, dot_zero_right, mul_zero, add_zero, zero_add] at hi
    simp only [gradV] at hi
    simp only [Pi.add_apply]
    dsimp only [mu, beta]
    field_simp
    nlinarith

theorem interior_maximum_spectral_pair
    (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) (p : Pair)
    (hsym : ∀ i j, A i j = A j i) (hskew : ∀ i j, C i j = -C j i)
    (hp : p ∈ feasible) (hv : normSq p.2 < 1)
    (hmax : IsMaxOn (objective A C s t) feasible p) :
    ∃ mu : ℝ,
      (matVec A p.1-matVec C p.2 = fun i => mu*p.1 i) ∧
      (matVec (shift A (-s)) p.2+matVec C p.1 = 0) := by
  obtain ⟨mu, beta, hfirst, hsecond⟩ := interior_maximum_kkt A C s t p hsym hskew hp hv hmax
  have hb := kkt_multiplier_zero A C p.1 p.2 s mu beta hsym hskew hp.1 hp.2.1 hv hfirst hsecond
  refine ⟨mu, ?_, ?_⟩
  · simpa [hb] using hfirst
  · simpa [hb] using hsecond

theorem interior_maximum_spectral_value
    (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) (p : Pair)
    (hsym : ∀ i j, A i j = A j i) (hskew : ∀ i j, C i j = -C j i)
    (hp : p ∈ feasible) (hv : normSq p.2 < 1)
    (hmax : IsMaxOn (objective A C s t) feasible p) :
    ∃ mu : ℝ,
      (matVec A p.1-matVec C p.2 = fun i => mu*p.1 i) ∧
      (matVec (shift A (-s)) p.2+matVec C p.1 = 0) ∧
      objective A C s t p = t-mu := by
  obtain ⟨mu, hfirst, hsecond⟩ := interior_maximum_spectral_pair A C s t p hsym hskew hp hv hmax
  exact ⟨mu, hfirst, hsecond,
    spectral_stationary_value A C p.1 p.2 s mu t hskew hp.1 hfirst hsecond⟩

theorem maximum_boundary_or_spectral
    (A C : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ)
    (hsym : ∀ i j, A i j = A j i) (hskew : ∀ i j, C i j = -C j i) :
    ∃ p ∈ feasible, IsMaxOn (objective A C s t) feasible p ∧
      (normSq p.2 = 1 ∨ ∃ mu : ℝ,
        (matVec A p.1-matVec C p.2 = fun i => mu*p.1 i) ∧
        (matVec (shift A (-s)) p.2+matVec C p.1 = 0) ∧
        objective A C s t p = t-mu) := by
  obtain ⟨p, hp, hmax, hb | hi⟩ := exists_maximum_boundary_or_interior A C s t
  · exact ⟨p, hp, hmax, Or.inl hb⟩
  · exact ⟨p, hp, hmax, Or.inr (interior_maximum_spectral_value A C s t p hsym hskew hp hi hmax)⟩

end UnilateralCHSH.Global
end
