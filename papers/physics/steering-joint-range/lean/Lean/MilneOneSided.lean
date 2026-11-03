import MilneBlochDefs
import Mathlib.Tactic

open scoped BigOperators Matrix
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

def orbitQuadratic (τ : ℝ) (k : V3) (K : T3) (x : V3) : ℝ :=
  τ + 2 * vDot k x - vDot x (tVec K x)

def linePoint (p v : V3) (t : ℝ) : V3 := fun i => p i + t * v i

theorem vSq_pos_of_ne_zero {v : V3} (hv : v ≠ 0) : 0 < vSq v := by
  have h0 := sq_nonneg (v 0)
  have h1 := sq_nonneg (v 1)
  have h2 := sq_nonneg (v 2)
  have he : vSq v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    simp [vSq, Fin.sum_univ_three]
  by_contra h
  have hn : vSq v ≤ 0 := le_of_not_gt h
  have hz0 : v 0 ^ 2 = 0 := by nlinarith
  have hz1 : v 1 ^ 2 = 0 := by nlinarith
  have hz2 : v 2 ^ 2 = 0 := by nlinarith
  have hz0' : v 0 = 0 := (sq_eq_zero_iff).mp hz0
  have hz1' : v 1 = 0 := (sq_eq_zero_iff).mp hz1
  have hz2' : v 2 = 0 := (sq_eq_zero_iff).mp hz2
  have hz : v = 0 := by
    funext i
    fin_cases i
    · exact hz0'
    · exact hz1'
    · exact hz2'
  exact hv hz

theorem vSq_linePoint (p v : V3) (t : ℝ) :
    vSq (linePoint p v t) = vSq p + 2*t*vDot p v + t^2*vSq v := by
  simp [vSq, vDot, linePoint, Fin.sum_univ_three]
  ring

theorem orbitQuadratic_line (τ : ℝ) (k : V3) (K : T3)
    (p v : V3) (t : ℝ) :
    orbitQuadratic τ k K (linePoint p v t) =
      orbitQuadratic τ k K p +
      t * (2*vDot k v-vDot p (tVec K v)-vDot v (tVec K p)) -
      t^2 * vDot v (tVec K v) := by
  simp [orbitQuadratic, vDot, tVec, linePoint, Fin.sum_univ_three]
  ring

/-- A scalar chord whose two endpoints lie below its interior value must
have a strictly negative quadratic coefficient. -/
theorem chord_forces_positive_curvature (f l q a b : ℝ)
    (ha : a < 0) (hb : 0 < b) (hf : 1 < f)
    (hfa : f+l*a-q*a^2 ≤ 1) (hfb : f+l*b-q*b^2 ≤ 1) : 0 < q := by
  by_contra hq
  have hq0 : q ≤ 0 := le_of_not_gt hq
  have hqa : 0 ≤ -q*a^2 := mul_nonneg (neg_nonneg.mpr hq0) (sq_nonneg a)
  have hqb : 0 ≤ -q*b^2 := mul_nonneg (neg_nonneg.mpr hq0) (sq_nonneg b)
  have hla : l*a < 0 := by nlinarith
  have hlb : l*b < 0 := by nlinarith
  rcases mul_neg_iff.mp hla with h | h <;>
    rcases mul_neg_iff.mp hlb with h' | h' <;>
    linarith [h.1,h.2,h'.1,h'.2]

/-- Every line through the open unit ball meets the sphere once in each
direction.  The factorization is retained for later segment arguments. -/
theorem line_sphere_chord (p v : V3) (hp : vSq p < 1) (hv : v ≠ 0) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
      vSq (linePoint p v a) = 1 ∧ vSq (linePoint p v b) = 1 ∧
      ∀ s : ℝ, vSq (linePoint p v s)-1 = vSq v*(s-a)*(s-b) := by
  let A := vSq v
  let B := vDot p v
  let C := vSq p
  have hA : 0 < A := vSq_pos_of_ne_zero hv
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hC : C < 1 := hp
  let D := B^2+A*(1-C)
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_nonneg B, mul_pos hA (sub_pos.mpr hC)]
  let z := Real.sqrt D
  have hz : 0 < z := Real.sqrt_pos.mpr hD
  have hz2 : z^2 = D := Real.sq_sqrt (le_of_lt hD)
  have hzB : B < z := by
    dsimp [D] at hz2
    nlinarith [mul_pos hA (sub_pos.mpr hC)]
  have hzB' : -B < z := by
    dsimp [D] at hz2
    nlinarith [mul_pos hA (sub_pos.mpr hC)]
  let a := (-B-z)/A
  let b := (-B+z)/A
  have ha : a < 0 := div_neg_of_neg_of_pos (by linarith) hA
  have hb : 0 < b := div_pos (by linarith) hA
  have hab : a+b = -2*B/A := by dsimp [a,b]; ring
  have hab' : a*b = (C-1)/A := by
    dsimp [a,b]
    field_simp
    dsimp [D] at hz2
    nlinarith
  have hfactor : ∀ s : ℝ, vSq (linePoint p v s)-1 = A*(s-a)*(s-b) := by
    intro s
    rw [vSq_linePoint]
    change C+2*s*B+s^2*A-1 = A*(s-a)*(s-b)
    calc
      C+2*s*B+s^2*A-1 = A*s^2-A*s*(a+b)+A*(a*b) := by
        rw [hab,hab']
        field_simp
        ring
      _ = A*(s-a)*(s-b) := by ring
  refine ⟨a,b,ha,hb,?_,?_,hfactor⟩
  · have h := hfactor a
    simp only [sub_self,mul_zero,zero_mul] at h
    linarith
  · have h := hfactor b
    simp only [sub_self,mul_zero] at h
    linarith

/-- A quadratic bounded by one on the sphere and violating one at an interior
point has a positive definite negative Hessian, including exclusion of all
singular and indefinite cases.  No extremum-existence assumption is used. -/
theorem orbit_violation_forces_posDef (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian)
    (hboundary : ∀ x : V3, vSq x = 1 → orbitQuadratic τ k K x ≤ 1)
    (p : V3) (hp : vSq p < 1) (hviol : 1 < orbitQuadratic τ k K p) :
    K.PosDef := by
  refine ⟨hK,?_⟩
  intro v hv
  obtain ⟨a,b,ha,hb,hea,heb,_⟩ := line_sphere_chord p v hp hv
  have hfa := hboundary (linePoint p v a) hea
  have hfb := hboundary (linePoint p v b) heb
  rw [orbitQuadratic_line] at hfa hfb
  have hpos := chord_forces_positive_curvature
    (orbitQuadratic τ k K p)
    (2*vDot k v-vDot p (tVec K v)-vDot v (tVec K p))
    (vDot v (tVec K v)) a b ha hb hviol (by nlinarith [hfa]) (by nlinarith [hfb])
  simpa [vDot,tVec,Matrix.mulVec,dotProduct] using hpos

theorem quadratic_form_nonneg (K : T3) (hK : K.PosDef) (x : V3) :
    0 ≤ vDot x (tVec K x) := by
  by_cases hx : x = 0
  · simp [hx,vDot,tVec]
  · have h := hK.2 x hx
    simpa [vDot,tVec,Matrix.mulVec,dotProduct] using le_of_lt h

theorem quadratic_form_smul (K : T3) (x : V3) (s : ℝ) :
    vDot (s • x) (tVec K (s • x)) = s^2*vDot x (tVec K x) := by
  simp [vDot,tVec,Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three]
  ring

/-- Exact completed square at a stationary point, for a real symmetric
quadratic.  The matrix can be singular in this algebraic identity. -/
theorem orbit_completed_square (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian) (p : V3) (hp : tVec K p = k) (x : V3) :
    orbitQuadratic τ k K p-orbitQuadratic τ k K x =
      vDot (x-p) (tVec K (x-p)) := by
  rw [← hp]
  have h10 : K 1 0 = K 0 1 := by simpa using hK.apply 0 1
  have h20 : K 2 0 = K 0 2 := by simpa using hK.apply 0 2
  have h21 : K 2 1 = K 1 2 := by simpa using hK.apply 1 2
  simp [orbitQuadratic,vDot,tVec,Pi.sub_apply,Fin.sum_univ_three]
  rw [h10,h20,h21]
  ring

theorem orbit_critical_value (τ : ℝ) (k : V3) (K : T3)
    (p : V3) (hp : tVec K p = k) :
    orbitQuadratic τ k K p = τ+vDot k p := by
  unfold orbitQuadratic
  rw [hp]
  simp [vDot,Fin.sum_univ_three]
  ring

theorem orbit_critical_point_exists (k : V3) (K : T3) (hK : K.PosDef) :
    ∃ p : V3, tVec K p = k := by
  obtain ⟨p,hp⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hK.isUnit k
  exact ⟨p,hp⟩

theorem orbit_critical_point_is_maximum (τ : ℝ) (k : V3) (K : T3)
    (hK : K.PosDef) (p : V3) (hp : tVec K p = k) (x : V3) :
    orbitQuadratic τ k K x ≤ orbitQuadratic τ k K p := by
  have hs := orbit_completed_square τ k K hK.1 p hp x
  have hn := quadratic_form_nonneg K hK (x-p)
  linarith

theorem orbit_critical_point_unique (τ : ℝ) (k : V3) (K : T3)
    (hK : K.PosDef) (p : V3) (hp : tVec K p = k) (x : V3)
    (he : orbitQuadratic τ k K x = orbitQuadratic τ k K p) : x = p := by
  by_contra hne
  have hn : x-p ≠ 0 := sub_ne_zero.mpr hne
  have hpos := hK.2 (x-p) hn
  have hpos' : 0 < vDot (x-p) (tVec K (x-p)) := by
    simpa [vDot,tVec,Matrix.mulVec,dotProduct] using hpos
  have hs := orbit_completed_square τ k K hK.1 p hp x
  linarith

/-- If a physical quadratic has an interior violation, its (now necessarily
positive-definite) unconstrained vertex lies inside the physical ball. -/
theorem orbit_vertex_inside_of_violation (τ : ℝ) (k : V3) (K : T3)
    (hK : K.PosDef)
    (hboundary : ∀ x : V3, vSq x = 1 → orbitQuadratic τ k K x ≤ 1)
    (p z : V3) (hp : vSq p < 1) (hviol : 1 < orbitQuadratic τ k K p)
    (hz : tVec K z = k) : vSq z < 1 := by
  by_contra hzin
  have hzout : 1 ≤ vSq z := le_of_not_gt hzin
  let v : V3 := z-p
  have hv : v ≠ 0 := by
    intro h
    have hzp : z = p := sub_eq_zero.mp h
    rw [hzp] at hzout
    linarith
  obtain ⟨a,b,ha,hb,_,heb,hfactor⟩ := line_sphere_chord p v hp hv
  have hp1 : linePoint p v 1 = z := by
    funext i
    simp [linePoint,v,Pi.sub_apply]
  have hfactor1 := hfactor 1
  rw [hp1] at hfactor1
  have hprod : 0 ≤ vSq v*(1-a)*(1-b) := by linarith
  have hfirst : 0 < vSq v*(1-a) :=
    mul_pos (vSq_pos_of_ne_zero hv) (by linarith)
  have hb1 : b ≤ 1 := by
    have hh : 0 ≤ 1-b := by
      by_contra h
      have hneg := mul_neg_of_pos_of_neg hfirst (lt_of_not_ge h)
      linarith
    linarith
  have hline : linePoint p v b-z = (1-b) • (p-z) := by
    funext i
    simp [linePoint,v,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hcp := orbit_completed_square τ k K hK.1 z hz p
  have hcl := orbit_completed_square τ k K hK.1 z hz (linePoint p v b)
  rw [hline,quadratic_form_smul] at hcl
  have hq := quadratic_form_nonneg K hK (p-z)
  have hcoef : 0 ≤ 1-(1-b)^2 := by nlinarith
  have hgap := mul_nonneg hcoef hq
  have hlineviol : 1 < orbitQuadratic τ k K (linePoint p v b) := by
    nlinarith
  have hbound := hboundary (linePoint p v b) heb
  linarith

/-- Exact necessary and sufficient one-sided violation test in stationary
point form.  Its sole physical assumption is the proven boundary bound. -/
theorem orbit_violation_iff_stationary (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian)
    (hboundary : ∀ x : V3, vSq x = 1 → orbitQuadratic τ k K x ≤ 1) :
    (∃ x : V3, vSq x < 1 ∧ 1 < orbitQuadratic τ k K x) ↔
      K.PosDef ∧ ∃ p : V3, tVec K p = k ∧ vSq p < 1 ∧ 1 < τ+vDot k p := by
  constructor
  · rintro ⟨x,hx,hviol⟩
    have hPD := orbit_violation_forces_posDef τ k K hK hboundary x hx hviol
    obtain ⟨p,hp⟩ := orbit_critical_point_exists k K hPD
    have hin := orbit_vertex_inside_of_violation τ k K hPD hboundary x p hx hviol hp
    have hmax := orbit_critical_point_is_maximum τ k K hPD p hp x
    have hvalue := orbit_critical_value τ k K p hp
    exact ⟨hPD,p,hp,hin,by linarith⟩
  · rintro ⟨hPD,p,hp,hin,hvalue⟩
    exact ⟨p,hin,by rw [orbit_critical_value τ k K p hp]; exact hvalue⟩

def orbitVertex (k : V3) (K : T3) : V3 := tVec K⁻¹ k

theorem orbitVertex_stationary (k : V3) (K : T3) (hK : K.PosDef) :
    tVec K (orbitVertex k K) = k := by
  change K *ᵥ (K⁻¹ *ᵥ k) = k
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hK.det_pos.ne'.isUnit,
    Matrix.one_mulVec]

/-- Exact inverse-matrix form of the violation criterion.  This theorem
explicitly tests positive definiteness before interpreting the inverse. -/
theorem orbit_violation_iff_inverse (τ : ℝ) (k : V3) (K : T3)
    (hK : K.IsHermitian)
    (hboundary : ∀ x : V3, vSq x = 1 → orbitQuadratic τ k K x ≤ 1) :
    (∃ x : V3, vSq x < 1 ∧ 1 < orbitQuadratic τ k K x) ↔
      K.PosDef ∧ vSq (orbitVertex k K) < 1 ∧ 1 < τ+vDot k (orbitVertex k K) := by
  rw [orbit_violation_iff_stationary τ k K hK hboundary]
  constructor
  · rintro ⟨hPD,p,hp,hin,hvalue⟩
    have hs := orbitVertex_stationary k K hPD
    have he : p = orbitVertex k K := by
      exact Matrix.mulVec_injective_iff_isUnit.mpr hPD.isUnit (hp.trans hs.symm)
    subst p
    exact ⟨hPD,hin,hvalue⟩
  · rintro ⟨hPD,hin,hvalue⟩
    exact ⟨hPD,orbitVertex k K,orbitVertex_stationary k K hPD,hin,hvalue⟩

/-- The exact violating optimum and all of its maximizers. -/
theorem orbit_inverse_optimum (τ : ℝ) (k : V3) (K : T3) (hK : K.PosDef) :
    orbitQuadratic τ k K (orbitVertex k K) = τ+vDot k (orbitVertex k K) ∧
    (∀ x : V3, orbitQuadratic τ k K x ≤ τ+vDot k (orbitVertex k K)) ∧
    (∀ x : V3, orbitQuadratic τ k K x = τ+vDot k (orbitVertex k K) →
      x = orbitVertex k K) := by
  have hs := orbitVertex_stationary k K hK
  have hv := orbit_critical_value τ k K (orbitVertex k K) hs
  refine ⟨hv,?_,?_⟩
  · intro x
    rw [← hv]
    exact orbit_critical_point_is_maximum τ k K hK (orbitVertex k K) hs x
  · intro x hx
    rw [← hv] at hx
    exact orbit_critical_point_unique τ k K hK (orbitVertex k K) hs x hx

end Milne
