import Quadratic
import MemoryCertificate

open scoped BigOperators

namespace ADMMNearSharp.StandardRows

open ADMMBarrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def basisZ {n : ℕ} (i : Fin n) : Fin n → ℤ := fun j => if i = j then 1 else 0

def zIndex {n : ℕ} (i : Fin n) : Fin (2*n) := ⟨2*i.val, by omega⟩
def vIndex {n : ℕ} (i : Fin n) : Fin (2*n) := ⟨2*i.val+1, by omega⟩

def zRowZ {n : ℕ} (i : Fin n) : Fin (2*n) → ℤ := basisZ (zIndex i)
def vRowZ {n : ℕ} (i : Fin n) : Fin (2*n) → ℤ := basisZ (vIndex i)

noncomputable def castRow {n : ℕ} (r : Fin n → ℤ) : Fin n → ℝ := fun i => r i
noncomputable def castMatrix {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℤ) :
    Matrix (Fin n) (Fin m) ℝ := fun i j => A i j

def interleave {n : ℕ} (Z V : Fin n → E) (j : Fin (2*n)) : E :=
  if j.val % 2 = 0 then Z ⟨j.val / 2, by omega⟩ else V ⟨j.val / 2, by omega⟩

@[simp] theorem interleave_zIndex {n : ℕ} (Z V : Fin n → E) (i : Fin n) :
    interleave Z V (zIndex i) = Z i := by
  simp only [interleave, zIndex]
  have h : (2*i.val)%2=0 := by omega
  rw [if_pos h]
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

@[simp] theorem interleave_vIndex {n : ℕ} (Z V : Fin n → E) (i : Fin n) :
    interleave Z V (vIndex i) = V i := by
  simp only [interleave, vIndex]
  have h : ¬(2*i.val+1)%2=0 := by omega
  rw [if_neg h]
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

@[simp] theorem linComb_basisZ {n : ℕ} (i : Fin n) (w : Fin n → E) :
    linComb (castRow (basisZ i)) w = w i := by
  classical
  simp [linComb, castRow, basisZ]

@[simp] theorem linComb_zero {n : ℕ} (w : Fin n → E) :
    linComb (0 : Fin n → ℝ) w = 0 := by simp [linComb]

theorem linComb_add {n : ℕ} (a b : Fin n → ℝ) (w : Fin n → E) :
    linComb (a+b) w = linComb a w + linComb b w := by
  simp [linComb, add_smul, Finset.sum_add_distrib]

theorem linComb_sub {n : ℕ} (a b : Fin n → ℝ) (w : Fin n → E) :
    linComb (a-b) w = linComb a w - linComb b w := by
  simp [linComb, sub_smul, Finset.sum_sub_distrib]

theorem linComb_smul {n : ℕ} (t : ℝ) (a : Fin n → ℝ) (w : Fin n → E) :
    linComb (t • a) w = t • linComb a w := by
  simp [linComb, Finset.smul_sum, smul_smul]

@[simp] theorem castRow_zero {n : ℕ} : castRow (0 : Fin n → ℤ) = 0 := by
  ext i
  simp [castRow]

@[simp] theorem castRow_add {n : ℕ} (a b : Fin n → ℤ) :
    castRow (a+b) = castRow a+castRow b := by ext i; simp [castRow]

@[simp] theorem castRow_sub {n : ℕ} (a b : Fin n → ℤ) :
    castRow (a-b) = castRow a-castRow b := by ext i; simp [castRow]

@[simp] theorem linComb_zRowZ {n : ℕ} (Z V : Fin n → E) (i : Fin n) :
    linComb (castRow (zRowZ i)) (interleave Z V) = Z i := by
  simp [zRowZ]

@[simp] theorem linComb_vRowZ {n : ℕ} (Z V : Fin n → E) (i : Fin n) :
    linComb (castRow (vRowZ i)) (interleave Z V) = V i := by
  simp [vRowZ]

@[simp] theorem interleave_zero {n : ℕ} :
    interleave (0 : Fin n → E) 0 = 0 := by
  ext j
  simp [interleave]

theorem continuous_interleave {n : ℕ} :
    Continuous (fun q : (Fin n → E) × (Fin n → E) => interleave q.1 q.2) := by
  apply continuous_pi
  intro j
  by_cases hj : j.val % 2 = 0
  · simpa only [interleave, if_pos hj] using
      ((continuous_apply (⟨j.val/2, by omega⟩ : Fin n)).comp
        (continuous_fst : Continuous (fun q : (Fin n → E) × (Fin n → E) => q.1)))
  · simpa only [interleave, if_neg hj] using
      ((continuous_apply (⟨j.val/2, by omega⟩ : Fin n)).comp
        (continuous_snd : Continuous (fun q : (Fin n → E) × (Fin n → E) => q.2)))

def oldIndex {d : ℕ} (i : Fin (2*(d+1))) : Fin (2*(d+2)) := ⟨i.val, by omega⟩
def newIndex {d : ℕ} (i : Fin (2*(d+1))) : Fin (2*(d+2)) := ⟨i.val+2, by omega⟩

def S0Z (d : ℕ) : Matrix (Fin (2*(d+1))) (Fin (2*(d+2))) ℤ :=
  fun i => basisZ (oldIndex i)
def S1Z (d : ℕ) : Matrix (Fin (2*(d+1))) (Fin (2*(d+2))) ℤ :=
  fun i => basisZ (newIndex i)
noncomputable def S0 (d : ℕ) := castMatrix (S0Z d)
noncomputable def S1 (d : ℕ) := castMatrix (S1Z d)

@[simp] theorem linComb_S0 {d : ℕ} (Z V : Fin (d+2) → E) (i : Fin (2*(d+1))) :
    linComb (S0 d i) (interleave Z V) =
      interleave (fun j => Z j.castSucc) (fun j => V j.castSucc) i := by
  change linComb (castRow (basisZ (oldIndex i))) (interleave Z V) = _
  rw [linComb_basisZ]
  rfl

@[simp] theorem linComb_S1 {d : ℕ} (Z V : Fin (d+2) → E) (i : Fin (2*(d+1))) :
    linComb (S1 d i) (interleave Z V) =
      interleave (fun j => Z j.succ) (fun j => V j.succ) i := by
  change linComb (castRow (basisZ (newIndex i))) (interleave Z V) = _
  rw [linComb_basisZ]
  simp only [interleave, newIndex, Fin.val_mk]
  have hm : (i.val+2)%2=i.val%2 := by omega
  have hd : (i.val+2)/2=i.val/2+1 := by omega
  simp only [hm, hd]
  rfl

def xRowsZ (d : ℕ) : Matrix (Fin (d+2)) (Fin (2*(d+2))) ℤ :=
  Fin.cases 0 (fun i => zRowZ i.succ + vRowZ i.succ - vRowZ i.castSucc)
def zRowsZ (d : ℕ) : Matrix (Fin (d+2)) (Fin (2*(d+2))) ℤ :=
  Fin.cases 0 (fun i => zRowZ i.succ)
def prevZRowsZ (d : ℕ) : Matrix (Fin (d+2)) (Fin (2*(d+2))) ℤ :=
  Fin.cases 0 (fun i => zRowZ i.castSucc)
def prevVRowsZ (d : ℕ) : Matrix (Fin (d+2)) (Fin (2*(d+2))) ℤ :=
  Fin.cases 0 (fun i => vRowZ i.castSucc)

noncomputable def xRows (d : ℕ) := castMatrix (xRowsZ d)
noncomputable def zRows (d : ℕ) := castMatrix (zRowsZ d)
noncomputable def prevZRows (d : ℕ) := castMatrix (prevZRowsZ d)
noncomputable def prevVRows (d : ℕ) := castMatrix (prevVRowsZ d)
noncomputable def aRows (d : ℕ) (τ : ℝ) := prevZRows d - τ • prevVRows d - xRows d
noncomputable def bRows (d : ℕ) (τ : ℝ) := xRows d + τ • prevVRows d - zRows d

@[simp] theorem linComb_xRows {d : ℕ} (Z V : Fin (d+2) → E) (i : Fin (d+2)) :
    linComb (xRows d i) (interleave Z V) = pointsF Z V i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [xRows, castMatrix, xRowsZ, pointsF, linComb]
  · change linComb (castRow (zRowZ j.succ+vRowZ j.succ-vRowZ j.castSucc))
      (interleave Z V) = _
    simp [pointsF, linComb_add, linComb_sub]

@[simp] theorem linComb_zRows {d : ℕ} (Z V : Fin (d+2) → E) (i : Fin (d+2)) :
    linComb (zRows d i) (interleave Z V) = pointsG Z i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [zRows, castMatrix, zRowsZ, pointsG, linComb]
  · change linComb (castRow (zRowZ j.succ)) (interleave Z V) = _
    simp [pointsG]

@[simp] theorem linComb_prevZRows {d : ℕ} (Z V : Fin (d+2) → E) (i : Fin (d+2)) :
    linComb (prevZRows d i) (interleave Z V) =
      Fin.cases 0 (fun j => Z j.castSucc) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [prevZRows, castMatrix, prevZRowsZ, linComb]
  · change linComb (castRow (zRowZ j.castSucc)) (interleave Z V) = _
    simp

@[simp] theorem linComb_prevVRows {d : ℕ} (Z V : Fin (d+2) → E) (i : Fin (d+2)) :
    linComb (prevVRows d i) (interleave Z V) =
      Fin.cases 0 (fun j => V j.castSucc) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [prevVRows, castMatrix, prevVRowsZ, linComb]
  · change linComb (castRow (vRowZ j.castSucc)) (interleave Z V) = _
    simp

@[simp] theorem linComb_aRows {d : ℕ} (τ : ℝ) (Z V : Fin (d+2) → E) (i : Fin (d+2)) :
    linComb (aRows d τ i) (interleave Z V) = normalsF τ Z V i := by
  have he : aRows d τ i = prevZRows d i - τ • prevVRows d i - xRows d i := rfl
  rw [he, linComb_sub, linComb_sub, linComb_smul]
  simp only [linComb_prevZRows, linComb_prevVRows, linComb_xRows]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [normalsF, pointsF]
  · rfl

@[simp] theorem linComb_bRows {d : ℕ} (τ : ℝ) (Z V : Fin (d+2) → E) (i : Fin (d+2)) :
    linComb (bRows d τ i) (interleave Z V) = normalsG τ Z V i := by
  have he : bRows d τ i = xRows d i + τ • prevVRows d i - zRows d i := rfl
  rw [he, linComb_sub, linComb_add, linComb_smul]
  simp only [linComb_xRows, linComb_prevVRows, linComb_zRows]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [normalsG, pointsF, pointsG]
  · rfl

def coercZ (d : ℕ) : Matrix (Fin (2*(d+1))) (Fin (2*(d+1))) ℤ :=
  fun i j => zRowZ (Fin.last d) i * zRowZ (Fin.last d) j +
    vRowZ (Fin.last d) i * vRowZ (Fin.last d) j

def dzRowZ (d : ℕ) : Fin (2*(d+2)) → ℤ :=
  zRowZ (Fin.last (d+1)) - zRowZ (Fin.last d).castSucc
def dvRowZ (d : ℕ) : Fin (2*(d+2)) → ℤ :=
  vRowZ (Fin.last (d+1)) - vRowZ (Fin.last d).castSucc
def dissZ (d : ℕ) : Matrix (Fin (2*(d+2))) (Fin (2*(d+2))) ℤ :=
  fun i j => dzRowZ d i * dzRowZ d j + dvRowZ d i * dvRowZ d j

noncomputable def coerc (d : ℕ) := castMatrix (coercZ d)
noncomputable def diss (d : ℕ) := castMatrix (dissZ d)

theorem quad_coerc {d : ℕ} (Z V : Fin (d+1) → E) :
    quad (coerc d) (interleave Z V) =
      ‖Z (Fin.last d)‖^2 + ‖V (Fin.last d)‖^2 := by
  have he : coerc d = outer (castRow (zRowZ (Fin.last d))) (castRow (zRowZ (Fin.last d))) +
      outer (castRow (vRowZ (Fin.last d))) (castRow (vRowZ (Fin.last d))) := by
    ext i j
    simp [coerc, coercZ, castMatrix, castRow, outer]
  rw [he, quad_add, quad_outer, quad_outer]
  simp [real_inner_self_eq_norm_sq]

theorem quad_diss {d : ℕ} (Z V : Fin (d+2) → E) :
    quad (diss d) (interleave Z V) =
      ‖Z (Fin.last (d+1))-Z (Fin.last d).castSucc‖^2 +
      ‖V (Fin.last (d+1))-V (Fin.last d).castSucc‖^2 := by
  have he : diss d = outer (castRow (dzRowZ d)) (castRow (dzRowZ d)) +
      outer (castRow (dvRowZ d)) (castRow (dvRowZ d)) := by
    ext i j
    simp [diss, dissZ, castMatrix, castRow, outer]
  rw [he, quad_add, quad_outer, quad_outer]
  simp [dzRowZ, dvRowZ, linComb_sub, real_inner_self_eq_norm_sq]

end ADMMNearSharp.StandardRows
