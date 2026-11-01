import BergeBroom.Construction
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Berge

/-- The final integer optimization, fed by actual component counts below. -/
theorem counting_lower_arithmetic {a s n m h e z : ℕ}
    (_ha : 3 ≤ a) (hs : 2 ≤ s) (hn : s*a+1 ≤ n)
    (hmass : n ≤ s*m+h+e+z) (hstars : (s*a+1)*h ≤ n)
    (hsmall : e+z ≤ s) (hsmall' : 0<h → e+z ≤ s-1) :
    upperValue a s n ≤ m := by
  let A := s*a+1
  let q := n/A
  let t := n%A
  let d := t/s
  let eps := t%s
  have hA : 0<A := by dsimp [A]; omega
  have hq : 1≤q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hA).mpr (by simpa [A] using hn)
  have hhq : h≤q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hA).mpr (by simpa [A,Nat.mul_comm] using hstars)
  have hnq : A*q+t=n := Nat.div_add_mod n A
  have htd : s*d+eps=t := Nat.div_add_mod t s
  have hv : upperValue a s n=a*q+d := rfl
  have hdecomp : n=s*(a*q+d)+q+eps := by
    dsimp [A] at hnq
    nlinarith
  by_contra hbad
  have hm : m+1≤a*q+d := by rw [hv] at hbad; omega
  have hsm : s*(m+1)≤s*(a*q+d) := Nat.mul_le_mul_left s hm
  by_cases hh : 0<h
  · have hez := hsmall' hh
    have hs1 : s-1+1=s := by omega
    nlinarith
  · have hh0 : h=0 := by omega
    nlinarith

end Berge
