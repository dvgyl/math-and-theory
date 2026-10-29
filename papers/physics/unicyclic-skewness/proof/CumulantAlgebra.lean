import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Algebra of the first three winding-current cumulants.

If P(s) = a1*s + a2*s^2 + a3*s^3 + ... is the characteristic
polynomial at zero tilt, implicit differentiation of
P(lambda(k)) = U*(exp(k)-1) + V*(exp(-k)-1)
gives the three displayed equations proved here for the explicit definitions.

This file verifies their algebraic consequences. It does NOT prove that a
given Markov generator has this tilted characteristic polynomial, nor does
it prove the spectral coefficient assumptions from the transition rates.
-/

namespace UnicyclicCumulant

noncomputable section

def first (a1 U V : ℝ) : ℝ := (U-V)/a1

def second (a1 a2 U V : ℝ) : ℝ :=
  ((U+V) - 2*a2*(first a1 U V)^2)/a1

def third (a1 a2 a3 U V : ℝ) : ℝ :=
  ((U-V) - 6*a2*(first a1 U V)*(second a1 a2 U V) -
    6*a3*(first a1 U V)^3)/a1

theorem first_equation (a1 U V : ℝ) (ha1 : a1 ≠ 0) :
    a1 * first a1 U V = U-V := by
  dsimp [first]
  field_simp

theorem second_equation (a1 a2 U V : ℝ) (ha1 : a1 ≠ 0) :
    a1 * second a1 a2 U V + 2*a2*(first a1 U V)^2 = U+V := by
  dsimp [second]
  rw [mul_div_cancel₀ _ ha1]
  ring

theorem third_equation (a1 a2 a3 U V : ℝ) (ha1 : a1 ≠ 0) :
    a1 * third a1 a2 a3 U V +
      6*a2*(first a1 U V)*(second a1 a2 U V) +
      6*a3*(first a1 U V)^3 = U-V := by
  dsimp [third]
  rw [mul_div_cancel₀ _ ha1]
  ring

theorem scaled_cumulant_reduction
    (a1 a2 a3 U V d T c p2 p3 C1 C2 C3 : ℝ)
    (hd : d ≠ 0)
    (ha1 : a1 = d*T)
    (ha2 : a2 = d*T^2*(1-p2)/2)
    (ha3 : a3 = d*T^3*(1-3*p2+2*p3)/6)
    (hminus : U-V = d*c)
    (hplus : U+V = d*(c^2+1)/2)
    (h1 : a1*C1 = U-V)
    (h2 : a1*C2 + 2*a2*C1^2 = U+V)
    (h3 : a1*C3 + 6*a2*C1*C2 + 6*a3*C1^3 = U-V) :
    T*C1 = c ∧
    T*C2 = (1-c^2)/2 + p2*c^2 ∧
    T*C3 = c*(c^2*(3*p2^2-2*p3) + (c^2-1)*(1-3*p2)/2) := by
  have hC1 : T*C1 = c := by
    apply mul_left_cancel₀ hd
    calc
      d*(T*C1) = a1*C1 := by rw [ha1]; ring
      _ = U-V := h1
      _ = d*c := hminus
  have hC2sum : T*C2 + (1-p2)*c^2 = (c^2+1)/2 := by
    apply mul_left_cancel₀ hd
    calc
      d*(T*C2 + (1-p2)*c^2) = a1*C2 + 2*a2*C1^2 := by
        rw [ha1, ha2, ← hC1]
        ring
      _ = U+V := h2
      _ = d*((c^2+1)/2) := by rw [hplus]; ring
  have hC2 : T*C2 = (1-c^2)/2 + p2*c^2 := by linarith only [hC2sum]
  have hC3sum : T*C3 + 3*(1-p2)*c*((1-c^2)/2+p2*c^2) +
      (1-3*p2+2*p3)*c^3 = c := by
    apply mul_left_cancel₀ hd
    calc
      d*(T*C3 + 3*(1-p2)*c*((1-c^2)/2+p2*c^2) +
          (1-3*p2+2*p3)*c^3) =
          a1*C3 + 6*a2*C1*C2 + 6*a3*C1^3 := by
        rw [ha1, ha2, ha3, ← hC2, ← hC1]
        ring
      _ = U-V := h3
      _ = d*c := hminus
  refine ⟨hC1, hC2, ?_⟩
  nlinarith only [hC3sum]

theorem cumulant_ratio_reduction
    (a1 a2 a3 U V d T c p2 p3 C1 C2 C3 : ℝ)
    (hd : d ≠ 0) (hT : T ≠ 0) (hc : c ≠ 0)
    (ha1 : a1 = d*T)
    (ha2 : a2 = d*T^2*(1-p2)/2)
    (ha3 : a3 = d*T^3*(1-3*p2+2*p3)/6)
    (hminus : U-V = d*c)
    (hplus : U+V = d*(c^2+1)/2)
    (h1 : a1*C1 = U-V)
    (h2 : a1*C2 + 2*a2*C1^2 = U+V)
    (h3 : a1*C3 + 6*a2*C1*C2 + 6*a3*C1^3 = U-V) :
    C2/C1 = c*p2 - (c^2-1)/(2*c) ∧
    C3/C1 = c^2*(3*p2^2-2*p3) + (c^2-1)*(1-3*p2)/2 := by
  obtain ⟨hC1, hC2, hC3⟩ := scaled_cumulant_reduction
    a1 a2 a3 U V d T c p2 p3 C1 C2 C3 hd ha1 ha2 ha3
    hminus hplus h1 h2 h3
  have hC1nz : C1 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hC1
    exact hc hC1.symm
  constructor
  · have hratio : C2/C1 = ((1-c^2)/2+p2*c^2)/c := by
      apply (div_eq_div_iff hC1nz hc).2
      calc
        C2*c = C2*(T*C1) := by rw [hC1]
        _ = (T*C2)*C1 := by ring
        _ = ((1-c^2)/2+p2*c^2)*C1 := by rw [hC2]
    rw [hratio]
    field_simp
    ring
  · apply (div_eq_iff hC1nz).2
    apply mul_left_cancel₀ hT
    calc
      T*C3 = c*(c^2*(3*p2^2-2*p3) + (c^2-1)*(1-3*p2)/2) := hC3
      _ = T*((c^2*(3*p2^2-2*p3) + (c^2-1)*(1-3*p2)/2)*C1) := by
        rw [← hC1]
        ring

theorem explicit_cumulant_ratio_reduction
    (a1 a2 a3 U V d T c p2 p3 : ℝ)
    (hd : d ≠ 0) (hT : T ≠ 0) (hc : c ≠ 0)
    (ha1 : a1 = d*T)
    (ha2 : a2 = d*T^2*(1-p2)/2)
    (ha3 : a3 = d*T^3*(1-3*p2+2*p3)/6)
    (hminus : U-V = d*c)
    (hplus : U+V = d*(c^2+1)/2) :
    second a1 a2 U V / first a1 U V = c*p2 - (c^2-1)/(2*c) ∧
    third a1 a2 a3 U V / first a1 U V =
      c^2*(3*p2^2-2*p3) + (c^2-1)*(1-3*p2)/2 := by
  have ha1nz : a1 ≠ 0 := by rw [ha1]; exact mul_ne_zero hd hT
  exact cumulant_ratio_reduction a1 a2 a3 U V d T c p2 p3
    (first a1 U V) (second a1 a2 U V) (third a1 a2 a3 U V)
    hd hT hc ha1 ha2 ha3 hminus hplus
    (first_equation a1 U V ha1nz)
    (second_equation a1 a2 U V ha1nz)
    (third_equation a1 a2 a3 U V ha1nz)

#print axioms scaled_cumulant_reduction
#print axioms explicit_cumulant_ratio_reduction

end
end UnicyclicCumulant
