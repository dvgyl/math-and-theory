import StandardRows

open scoped BigOperators

namespace ADMMNearSharp.StandardRows

def selector (n N a : ℕ) : Matrix (Fin n) (Fin N) ℤ :=
  fun k i => if i.val=k.val+a then 1 else 0

def embeddedEntry {n N : ℕ} (a b : ℕ) (P : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin N) : ℤ :=
  if hi : a ≤ i.val ∧ i.val-a<n then
    if hj : b ≤ j.val ∧ j.val-b<n then
      P ⟨i.val-a,hi.2⟩ ⟨j.val-b,hj.2⟩
    else 0
  else 0

theorem selector_column {n N a : ℕ} (i : Fin N)
    (hi : a ≤ i.val ∧ i.val-a<n) (k : Fin n) :
    selector n N a k i = if k=⟨i.val-a,hi.2⟩ then 1 else 0 := by
  have he : i.val=k.val+a ↔ k=(⟨i.val-a,hi.2⟩ : Fin n) := by
    constructor
    · intro h
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    · intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_mk] at hval
      omega
  simp only [selector, he]

theorem selector_column_zero {n N a : ℕ} (i : Fin N)
    (hi : ¬(a ≤ i.val ∧ i.val-a<n)) (k : Fin n) : selector n N a k i = 0 := by
  have he : i.val ≠ k.val+a := by
    intro h
    apply hi
    constructor <;> omega
  simp [selector,he]

theorem selector_congruence_apply {n N : ℕ} (a b : ℕ)
    (P : Matrix (Fin n) (Fin n) ℤ) (i j : Fin N) :
    ((selector n N a).transpose * P * selector n N b) i j =
      embeddedEntry a b P i j := by
  classical
  by_cases hi : a ≤ i.val ∧ i.val-a<n
  · by_cases hj : b ≤ j.val ∧ j.val-b<n
    · simp [Matrix.mul_apply, Matrix.transpose_apply,
        selector_column i hi, selector_column j hj, embeddedEntry, hi, hj]
    · simp [Matrix.mul_apply, Matrix.transpose_apply,
        selector_column_zero j hj, embeddedEntry, hi, hj]
  · simp [Matrix.mul_apply, Matrix.transpose_apply,
      selector_column_zero i hi, embeddedEntry, hi]

theorem S0Z_eq_selector (d : ℕ) :
    S0Z d = selector (2*(d+1)) (2*(d+2)) 0 := by
  ext i j
  simp [S0Z,basisZ,oldIndex,selector,Fin.ext_iff,eq_comm]

theorem S1Z_eq_selector (d : ℕ) :
    S1Z d = selector (2*(d+1)) (2*(d+2)) 2 := by
  ext i j
  simp [S1Z,basisZ,newIndex,selector,Fin.ext_iff,eq_comm]

theorem S0_congruence_apply {d : ℕ}
    (P : Matrix (Fin (2*(d+1))) (Fin (2*(d+1))) ℤ)
    (i j : Fin (2*(d+2))) :
    ((S0Z d).transpose * P * S0Z d) i j = embeddedEntry 0 0 P i j := by
  rw [S0Z_eq_selector]
  exact selector_congruence_apply 0 0 P i j

theorem S1_congruence_apply {d : ℕ}
    (P : Matrix (Fin (2*(d+1))) (Fin (2*(d+1))) ℤ)
    (i j : Fin (2*(d+2))) :
    ((S1Z d).transpose * P * S1Z d) i j = embeddedEntry 2 2 P i j := by
  rw [S1Z_eq_selector]
  exact selector_congruence_apply 2 2 P i j

theorem difference_congruence_apply {d : ℕ}
    (T : Matrix (Fin (2*(d+1))) (Fin (2*(d+1))) ℤ)
    (i j : Fin (2*(d+2))) :
    ((S1Z d-S0Z d).transpose * T * (S1Z d-S0Z d)) i j =
      embeddedEntry 2 2 T i j - embeddedEntry 2 0 T i j -
      embeddedEntry 0 2 T i j + embeddedEntry 0 0 T i j := by
  rw [S0Z_eq_selector,S1Z_eq_selector]
  simp only [Matrix.transpose_sub,Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_apply,
    selector_congruence_apply]
  ring

end ADMMNearSharp.StandardRows
