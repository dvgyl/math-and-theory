import BergeBroom.Exact

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Berge

/-- The construction's quotient/remainder expression is a single floor. -/
theorem upperValue_eq_floor {a s n : ℕ} (hs : 1 ≤ s) :
    upperValue a s n = a * (n + 1) / (s * a + 1) := by
  let A := s * a + 1
  let q := n / A
  let t := n % A
  let d := t / s
  let u := t % s
  have hA : 0 < A := by dsimp [A]; omega
  have hn : A * q + t = n := Nat.div_add_mod n A
  have ht : s * d + u = t := Nat.div_add_mod t s
  have htA : t < A := Nat.mod_lt n hA
  have hu : u < s := Nat.mod_lt t (by omega)
  have hd : d ≤ a := by
    by_contra h
    have hda : a + 1 ≤ d := by omega
    have hm := Nat.mul_le_mul_left s hda
    dsimp [A] at htA
    nlinarith
  have hid : a * (n + 1) + d = A * (a * q + d) + a * (u + 1) := by
    rw [← hn, ← ht]
    dsimp [A]
    ring
  have hua : a * (u + 1) ≤ s * a := by
    have hh := Nat.mul_le_mul_left a (show u + 1 ≤ s by omega)
    simpa [Nat.mul_comm] using hh
  have hv : upperValue a s n = a * q + d := rfl
  rw [hv]
  symm
  apply Nat.div_eq_of_lt_le
  · change (a * q + d) * A ≤ a * (n + 1)
    nlinarith
  · change a * (n + 1) < (a * q + d + 1) * A
    dsimp [A] at *
    nlinarith

/-- The exact saturation value in its single-floor form. -/
theorem exact_saturation_floor {a s n : ℕ} (ha : 3 ≤ a) (hs : 2 ≤ s)
    (hn : s * a + 1 ≤ n) :
    IsSaturationNumber a (s + 1) n (a * (n + 1) / (s * a + 1)) := by
  simpa only [upperValue_eq_floor (by omega : 1 ≤ s)] using exact_saturation ha hs hn

/-- The single-floor formula for arbitrary uniformity at least three. -/
theorem exact_saturation_uniform_floor {a r n : ℕ} (ha : 3 ≤ a) (hr : 3 ≤ r)
    (hn : (r - 1) * a + 1 ≤ n) :
    IsSaturationNumber a r n (a * (n + 1) / ((r - 1) * a + 1)) := by
  have hh : r - 1 + 1 = r := by omega
  simpa only [hh] using exact_saturation_floor ha (by omega : 2 ≤ r - 1) hn

/-- The particularly simple three-uniform exact value. -/
theorem exact_saturation_three_floor {a n : ℕ} (ha : 3 ≤ a) (hn : 2 * a + 1 ≤ n) :
    IsSaturationNumber a 3 n (a * (n + 1) / (2 * a + 1)) := by
  simpa using exact_saturation_floor ha (by omega : 2 ≤ 2) hn

/-- Equivalent ceiling-division form, with the numerator nonnegative in this range. -/
theorem exact_saturation_ceiling {a s n : ℕ} (ha : 3 ≤ a) (hs : 2 ≤ s)
    (hn : s * a + 1 ≤ n) :
    IsSaturationNumber a (s + 1) n
      ((a * (n - s + 1) + (s * a + 1) - 1) / (s * a + 1)) := by
  have hsn : s ≤ n := by nlinarith
  have hnsub : n - s + s = n := Nat.sub_add_cancel hsn
  have hnum : a * (n - s + 1) + (s * a + 1) - 1 = a * (n + 1) := by
    have hsum : a * (n - s + 1) + (s * a + 1) = a * (n + 1) + 1 := by
      nlinarith
    omega
  rw [hnum]
  exact exact_saturation_floor ha hs hn

end Berge
