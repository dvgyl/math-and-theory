import UnilateralCHSH
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
The real, operational Horodecki bridge for four unit Bloch measurement vectors.
No quantum-state positivity or optimizer-existence assumption is needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace UnilateralCHSH.Horodecki

noncomputable section
open scoped BigOperators

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def chshValue (D : Mat) (a₀ a₁ b₀ b₁ : Vec) : ℝ :=
  (dot a₀ (matVec D b₀) + dot a₀ (matVec D b₁) +
    dot a₁ (matVec D b₀) - dot a₁ (matVec D b₁))/2

def IsMeasurements (a₀ a₁ b₀ b₁ : Vec) : Prop :=
  normSq a₀ = 1 ∧ normSq a₁ = 1 ∧ normSq b₀ = 1 ∧ normSq b₁ = 1

def planeValue (D : Mat) (n : Vec) : ℝ :=
  planeColumnValue n (column D 0) + planeColumnValue n (column D 1) +
    planeColumnValue n (column D 2)

def mix (x y : Vec) (a b : ℝ) : Vec := fun i => a*x i+b*y i

def project (n z : Vec) : Vec := fun i => z i-dot n z*n i

def outer (x : Vec) : Mat := fun i j => x i*x j

def frobDot (X Y : Mat) : ℝ :=
  dot (column X 0) (column Y 0) + dot (column X 1) (column Y 1) +
    dot (column X 2) (column Y 2)

def halfPlus (a₀ a₁ : Vec) : Vec := fun i => (a₀ i+a₁ i)/2

def halfMinus (a₀ a₁ : Vec) : Vec := fun i => (a₀ i-a₁ i)/2

def measurementMatrix (a₀ a₁ b₀ b₁ : Vec) : Mat :=
  fun i j => halfPlus a₀ a₁ i*b₀ j+halfMinus a₀ a₁ i*b₁ j

def projectMatrix (D : Mat) (n : Vec) : Mat := fun i j => project n (column D j) i

theorem dot_scale_left (x y : Vec) (t : ℝ) :
    dot (fun i => t*x i) y = t*dot x y := by
  rw [dot_symm, dot_scale_right, dot_symm y x]

theorem normSq_mix (x y : Vec) (a b : ℝ) :
    normSq (mix x y a b) = a^2*normSq x+b^2*normSq y+2*a*b*dot x y := by
  simp only [normSq, dot, mix]
  ring

theorem quad_outer (x y : Vec) : quad (outer x) y = (dot y x)^2 := by
  simp only [quad, matVec, outer, dot]
  ring

theorem trace_outer (x : Vec) : traceThree (outer x) = normSq x := by
  simp only [traceThree, outer, normSq, dot]

theorem dot_adjoint (D : Mat) (x y : Vec) :
    dot x (matVec D y) = dot (matVec D.transpose x) y := by
  simp only [dot, matVec, Matrix.transpose_apply]
  ring

theorem normSq_adjoint (D : Mat) (x : Vec) :
    normSq (matVec D.transpose x) =
      (dot x (column D 0))^2+(dot x (column D 1))^2+(dot x (column D 2))^2 := by
  simp only [normSq, dot, matVec, Matrix.transpose_apply, column]
  ring

theorem exists_unit_perpendicular (n : Vec) :
    ∃ x : Vec, normSq x=1 ∧ dot n x=0 := by
  let w : Vec := ![-n 1,n 0,0]
  by_cases hw : w=0
  · have hn₀ : n 0=0 := by
      have h := congrFun hw 1
      simpa [w] using h
    refine ⟨![1,0,0],?_,?_⟩
    · norm_num [normSq,dot,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
    · simpa [dot] using hn₀
  · have hwp := normSq_pos w hw
    let r := Real.sqrt (normSq w)
    have hrp : 0<r := Real.sqrt_pos.mpr hwp
    have hrs : r^2=normSq w := Real.sq_sqrt hwp.le
    have hrn : r≠0 := ne_of_gt hrp
    let x : Vec := fun i => (1/r)*w i
    have hx : normSq x=1 := by
      rw [normSq_scale]
      rw [←hrs]
      field_simp
    have horth : dot n w=0 := by simp [dot,w]; ring
    refine ⟨x,hx,?_⟩
    rw [dot_scale_right, horth, mul_zero]

theorem exists_unit_alignment (p : Vec) :
    ∃ b : Vec, normSq b=1 ∧ dot p b=Real.sqrt (normSq p) := by
  by_cases hp : p=0
  · subst p
    refine ⟨![1,0,0],?_,?_⟩
    · norm_num [normSq,dot,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
    · simp [normSq,dot]
  · have hpp := normSq_pos p hp
    let r := Real.sqrt (normSq p)
    have hrp : 0<r := Real.sqrt_pos.mpr hpp
    have hrs : r^2=normSq p := Real.sq_sqrt hpp.le
    have hrn : r≠0 := ne_of_gt hrp
    let b : Vec := fun i => (1/r)*p i
    have hb : normSq b=1 := by
      rw [normSq_scale]
      rw [←hrs]
      field_simp
    refine ⟨b,hb,?_⟩
    rw [dot_scale_right]
    change (1/r)*normSq p=r
    rw [←hrs]
    field_simp
    ring

theorem exists_common_normal (a₀ a₁ : Vec) (h₀ : normSq a₀=1) :
    ∃ n : Vec, normSq n=1 ∧ dot n a₀=0 ∧ dot n a₁=0 := by
  by_cases hc : cross a₀ a₁=0
  · obtain ⟨n,hn,horth⟩ := exists_unit_perpendicular a₀
    have hcol : a₁=fun i => dot a₁ a₀*a₀ i := by
      have ht := vector_triple_product a₀ a₁ a₀
      rw [hc] at ht
      have hz : cross (0:Vec) a₀=0 := by simp [cross]
      rw [hz] at ht
      change (0:Vec)=(fun i => normSq a₀*a₁ i-dot a₁ a₀*a₀ i) at ht
      rw [h₀] at ht
      funext i
      have hi := congrFun ht i
      simp only [Pi.zero_apply,one_mul] at hi
      linarith
    refine ⟨n,hn,by rw [dot_symm]; exact horth,?_⟩
    rw [hcol,dot_scale_right,dot_symm n a₀,horth,mul_zero]
  · have hcp := normSq_pos (cross a₀ a₁) hc
    let r := Real.sqrt (normSq (cross a₀ a₁))
    have hrp : 0<r := Real.sqrt_pos.mpr hcp
    have hrs : r^2=normSq (cross a₀ a₁) := Real.sq_sqrt hcp.le
    have hrn : r≠0 := ne_of_gt hrp
    let n : Vec := fun i => (1/r)*cross a₀ a₁ i
    have hn : normSq n=1 := by
      rw [normSq_scale,←hrs]
      field_simp
    refine ⟨n,hn,?_,?_⟩
    · rw [dot_scale_left,dot_symm, cross_orthogonal_left,mul_zero]
    · rw [dot_scale_left,dot_symm, cross_orthogonal_right,mul_zero]

theorem frame_plane_column (n x z : Vec) (hn : normSq n=1)
    (hx : normSq x=1) (hnx : dot n x=0) :
    planeColumnValue n z=(dot x z)^2+(dot (cross n x) z)^2 := by
  have h := tangent_plane_quad_identity (outer z) n x hn hnx
  simp only [quad_outer,trace_outer,hx,one_mul] at h
  unfold planeColumnValue
  linarith

theorem frame_plane (D : Mat) (n x : Vec) (hn : normSq n=1)
    (hx : normSq x=1) (hnx : dot n x=0) :
    planeValue D n=normSq (matVec D.transpose x)+normSq (matVec D.transpose (cross n x)) := by
  unfold planeValue
  rw [frame_plane_column n x (column D 0) hn hx hnx,
    frame_plane_column n x (column D 1) hn hx hnx,
    frame_plane_column n x (column D 2) hn hx hnx,
    normSq_adjoint,normSq_adjoint]
  ring

theorem project_dot (n z w : Vec) :
    dot (project n z) w=dot z w-dot n z*dot n w := by
  simp only [project,dot]
  ring

theorem project_norm (n z : Vec) (hn : normSq n=1) :
    normSq (project n z)=planeColumnValue n z := by
  have h : normSq (project n z)=normSq z-2*(dot n z)^2+normSq n*(dot n z)^2 := by
    simp only [project,normSq,dot]
    ring
  rw [h,hn]
  unfold planeColumnValue
  ring

theorem sum_pair_mul (X Y : Mat) :
    (∑ p : Fin 3 × Fin 3, X p.1 p.2*Y p.1 p.2)=frobDot X Y := by
  simp [Fintype.sum_prod_type,Fin.sum_univ_succ,frobDot,dot,column]
  ring

theorem frob_cauchy (X Y : Mat) :
    (frobDot X Y)^2 ≤ frobDot X X*frobDot Y Y := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun p => X p.1 p.2) (fun p => Y p.1 p.2)
  have hx : (∑ p : Fin 3 × Fin 3, (X p.1 p.2)^2)=frobDot X X := by
    simpa only [pow_two] using sum_pair_mul X X
  have hy : (∑ p : Fin 3 × Fin 3, (Y p.1 p.2)^2)=frobDot Y Y := by
    simpa only [pow_two] using sum_pair_mul Y Y
  rw [sum_pair_mul X Y,hx,hy] at h
  exact h

theorem measurement_matrix_value (D : Mat) (a₀ a₁ b₀ b₁ : Vec) :
    frobDot D (measurementMatrix a₀ a₁ b₀ b₁)=chshValue D a₀ a₁ b₀ b₁ := by
  simp only [frobDot,dot,column,measurementMatrix,halfPlus,halfMinus,chshValue,matVec]
  ring

theorem measurement_matrix_norm (a₀ a₁ b₀ b₁ : Vec)
    (hm : IsMeasurements a₀ a₁ b₀ b₁) :
    frobDot (measurementMatrix a₀ a₁ b₀ b₁) (measurementMatrix a₀ a₁ b₀ b₁)=1 := by
  have h : frobDot (measurementMatrix a₀ a₁ b₀ b₁) (measurementMatrix a₀ a₁ b₀ b₁)=
      ((normSq a₀+normSq a₁+2*dot a₀ a₁)*normSq b₀+
       (normSq a₀+normSq a₁-2*dot a₀ a₁)*normSq b₁+
       2*(normSq a₀-normSq a₁)*dot b₀ b₁)/4 := by
    simp only [frobDot,dot,column,measurementMatrix,halfPlus,halfMinus,normSq]
    ring
  rw [h,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2]
  ring

theorem measurement_matrix_tangent (a₀ a₁ b₀ b₁ n : Vec)
    (h₀ : dot n a₀=0) (h₁ : dot n a₁=0) (j : Fin 3) :
    dot n (column (measurementMatrix a₀ a₁ b₀ b₁) j)=0 := by
  have h : dot n (column (measurementMatrix a₀ a₁ b₀ b₁) j)=
      ((dot n a₀+dot n a₁)*b₀ j+(dot n a₀-dot n a₁)*b₁ j)/2 := by
    simp only [dot,column,measurementMatrix,halfPlus,halfMinus]
    ring
  rw [h,h₀,h₁]
  ring

theorem projectMatrix_norm (D : Mat) (n : Vec) (hn : normSq n=1) :
    frobDot (projectMatrix D n) (projectMatrix D n)=planeValue D n := by
  change normSq (project n (column D 0))+normSq (project n (column D 1))+
    normSq (project n (column D 2))=planeValue D n
  rw [project_norm n _ hn,project_norm n _ hn,project_norm n _ hn]
  rfl

theorem tangent_frob_project (D : Mat) (n : Vec) (Z : Mat)
    (ht : ∀ j : Fin 3, dot n (column Z j)=0) :
    frobDot (projectMatrix D n) Z=frobDot D Z := by
  unfold frobDot
  change dot (project n (column D 0)) (column Z 0)+
    dot (project n (column D 1)) (column Z 1)+
    dot (project n (column D 2)) (column Z 2)=_
  rw [project_dot,project_dot,project_dot,ht 0,ht 1,ht 2]
  ring

/-- Every four unit Bloch measurements are bounded by a real correlation
plane, including parallel and antiparallel Alice settings. -/
theorem measurements_bounded_by_plane (D : Mat) (a₀ a₁ b₀ b₁ : Vec)
    (hm : IsMeasurements a₀ a₁ b₀ b₁) :
    ∃ n : Vec, normSq n=1 ∧ (chshValue D a₀ a₁ b₀ b₁)^2 ≤ planeValue D n := by
  obtain ⟨n,hn,h₀,h₁⟩ := exists_common_normal a₀ a₁ hm.1
  have h := frob_cauchy (projectMatrix D n) (measurementMatrix a₀ a₁ b₀ b₁)
  rw [tangent_frob_project D n _ (measurement_matrix_tangent a₀ a₁ b₀ b₁ n h₀ h₁),
    measurement_matrix_value,projectMatrix_norm D n hn,measurement_matrix_norm _ _ _ _ hm,mul_one] at h
  exact ⟨n,hn,h⟩


theorem chsh_same (D : Mat) (x b₀ b₁ : Vec) :
    chshValue D x x b₀ b₁=dot x (matVec D b₀) := by
  unfold chshValue
  ring

theorem chsh_mixed (D : Mat) (x y b₀ b₁ : Vec) (a b : ℝ) :
    chshValue D (mix x y a b) (mix x y a (-b)) b₀ b₁=
      a*dot x (matVec D b₀)+b*dot y (matVec D b₁) := by
  simp only [chshValue,mix,dot]
  ring

theorem planeValue_nonnegative (D : Mat) (n : Vec) (hn : normSq n=1) :
    0≤planeValue D n := by
  obtain ⟨x,hx,hnx⟩ := exists_unit_perpendicular n
  rw [frame_plane D n x hn hx hnx]
  exact add_nonneg (normSq_nonneg _) (normSq_nonneg _)

/-- Every correlation-plane value has an explicit four-measurement witness.
The zero-plane case is included; no division by a zero vector occurs. -/
theorem plane_sqrt_attained (D : Mat) (n : Vec) (hn : normSq n=1) :
    ∃ a₀ a₁ b₀ b₁ : Vec, IsMeasurements a₀ a₁ b₀ b₁ ∧
      chshValue D a₀ a₁ b₀ b₁=Real.sqrt (planeValue D n) := by
  obtain ⟨x,hx,hnx⟩ := exists_unit_perpendicular n
  let y := cross n x
  have hy : normSq y=1 := by
    change normSq (cross n x)=1
    rw [cross_normSq,hn,hx,hnx]
    norm_num
  have hxy : dot x y=0 := cross_orthogonal_right n x
  let p := matVec D.transpose x
  let q := matVec D.transpose y
  have hplane : planeValue D n=normSq p+normSq q := frame_plane D n x hn hx hnx
  obtain ⟨b₀,hb₀,hpb⟩ := exists_unit_alignment p
  obtain ⟨b₁,hb₁,hqb⟩ := exists_unit_alignment q
  have hpnonneg := normSq_nonneg p
  have hqnonneg := normSq_nonneg q
  by_cases hzero : normSq p+normSq q=0
  · have hpzero : normSq p=0 := by linarith
    have hval : chshValue D x x b₀ b₁=0 := by
      rw [chsh_same,dot_adjoint]
      change dot p b₀=0
      rw [hpb,hpzero]
      simp
    refine ⟨x,x,b₀,b₁,⟨hx,hx,hb₀,hb₁⟩,?_⟩
    rw [hval,hplane,hzero]
    simp
  · have hsum : 0<normSq p+normSq q := lt_of_le_of_ne (add_nonneg hpnonneg hqnonneg)
      (Ne.symm hzero)
    let r := Real.sqrt (normSq p+normSq q)
    have hr : 0<r := Real.sqrt_pos.mpr hsum
    have hrn : r≠0 := ne_of_gt hr
    have hrs : r^2=normSq p+normSq q := Real.sq_sqrt hsum.le
    have hps : (Real.sqrt (normSq p))^2=normSq p := Real.sq_sqrt hpnonneg
    have hqs : (Real.sqrt (normSq q))^2=normSq q := Real.sq_sqrt hqnonneg
    let a := Real.sqrt (normSq p)/r
    let b := Real.sqrt (normSq q)/r
    have hab : a^2+b^2=1 := by
      dsimp only [a,b]
      field_simp
      nlinarith
    have ha₀ : normSq (mix x y a b)=1 := by
      rw [normSq_mix,hx,hy,hxy]
      nlinarith
    have ha₁ : normSq (mix x y a (-b))=1 := by
      rw [normSq_mix,hx,hy,hxy]
      nlinarith
    have hval : chshValue D (mix x y a b) (mix x y a (-b)) b₀ b₁=r := by
      rw [chsh_mixed,dot_adjoint,dot_adjoint]
      change a*dot p b₀+b*dot q b₁=r
      rw [hpb,hqb]
      dsimp only [a,b]
      field_simp
      nlinarith
    refine ⟨mix x y a b,mix x y a (-b),b₀,b₁,⟨ha₀,ha₁,hb₀,hb₁⟩,?_⟩
    rw [hval,hplane]

theorem plane_attained (D : Mat) (n : Vec) (hn : normSq n=1) :
    ∃ a₀ a₁ b₀ b₁ : Vec, IsMeasurements a₀ a₁ b₀ b₁ ∧
      (chshValue D a₀ a₁ b₀ b₁)^2=planeValue D n := by
  obtain ⟨a₀,a₁,b₀,b₁,hm,hv⟩ := plane_sqrt_attained D n hn
  refine ⟨a₀,a₁,b₀,b₁,hm,?_⟩
  rw [hv]
  exact Real.sq_sqrt (planeValue_nonnegative D n hn)

/-- The optimized squared CHSH correlation and the optimized two-dimensional
correlation-plane value have exactly the same upper bounds. -/
theorem exact_chsh_bound (D : Mat) (bound : ℝ) :
    (∀ n : Vec, normSq n=1 → planeValue D n≤bound) ↔
      (∀ a₀ a₁ b₀ b₁ : Vec, IsMeasurements a₀ a₁ b₀ b₁ →
        (chshValue D a₀ a₁ b₀ b₁)^2≤bound) := by
  constructor
  · intro h a₀ a₁ b₀ b₁ hm
    obtain ⟨n,hn,hb⟩ := measurements_bounded_by_plane D a₀ a₁ b₀ b₁ hm
    exact le_trans hb (h n hn)
  · intro h n hn
    obtain ⟨a₀,a₁,b₀,b₁,hm,hv⟩ := plane_attained D n hn
    have hb := h a₀ a₁ b₀ b₁ hm
    rwa [hv] at hb

def planeFamilyValues {ι : Type*} (family : ι → Mat) (domain : Set ι) : Set ℝ :=
  {b | ∃ i ∈ domain, ∃ n : Vec, normSq n=1 ∧ planeValue (family i) n=b}

def chshFamilyValues {ι : Type*} (family : ι → Mat) (domain : Set ι) : Set ℝ :=
  {b | ∃ i ∈ domain, ∃ a₀ a₁ b₀ b₁ : Vec, IsMeasurements a₀ a₁ b₀ b₁ ∧
    (chshValue (family i) a₀ a₁ b₀ b₁)^2=b}

/-- A proved plane maximum for any family of real correlation matrices is
also the attained four-observable CHSH-square maximum for that family. -/
theorem exact_family_maximum {ι : Type*} (family : ι → Mat) (domain : Set ι) (bound : ℝ)
    (hmax : IsGreatest (planeFamilyValues family domain) bound) :
    IsGreatest (chshFamilyValues family domain) bound := by
  constructor
  · obtain ⟨i,hi,n,hn,hv⟩ := hmax.1
    obtain ⟨a₀,a₁,b₀,b₁,hm,hchsh⟩ := plane_attained (family i) n hn
    exact ⟨i,hi,a₀,a₁,b₀,b₁,hm,hchsh.trans hv⟩
  · rintro z ⟨i,hi,a₀,a₁,b₀,b₁,hm,hv⟩
    obtain ⟨n,hn,hbound⟩ := measurements_bounded_by_plane (family i) a₀ a₁ b₀ b₁ hm
    have hp := hmax.2 ⟨i,hi,n,hn,rfl⟩
    rw [hv] at hbound
    exact le_trans hbound hp

end
end UnilateralCHSH.Horodecki
