import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable section
namespace Motzkin.Certificate

def P (n : ℝ) : ℝ :=
  111034368*n^12 + 3364180992*n^11 + 46409331456*n^10 +
  385445807712*n^9 + 2146478817312*n^8 + 8443039471929*n^7 +
  24049942325892*n^6 + 49975719381810*n^5 + 75163688028504*n^4 +
  79753800966621*n^3 + 56628081108524*n^2 + 24132003073520*n +
  4660409556032

def D (n : ℝ) : ℝ := 16*(n+3)^3

def V (n : ℝ) : ℝ := 48*(n+3)^3 - 72*(n+3)^2 + 9*(n+3) + 32

def Y (n : ℝ) : ℝ := (n+2)*(2*V n + 3*D n) - 4*(n+3)

def Z (n : ℝ) : ℝ := (n+3)*(2*Y n + 3*V n*(n+4)) + 4*(n+3)*(n+4)

theorem corner_polynomial (n : ℝ) :
    (n+5)*D n*(Y n)^3 - (n+4)^2*(V n)^3*Z n = (n+3)*P n := by
  dsimp [D, V, Y, Z, P]
  ring

theorem P_pos (n : ℝ) (hn : 0 ≤ n) : 0 < P n := by
  unfold P
  positivity

def lowerNumerator (n : ℝ) : ℝ := 304*n^3 + 1687*n^2 + 1599*n - 1790

def upperNumerator (n : ℝ) : ℝ := 112*n^2 - 509*n - 1331

def previousV (n : ℝ) : ℝ := 48*(n+2)^3 - 72*(n+2)^2 + 9*(n+2) + 32

def previousH (n : ℝ) : ℝ := 16*n^2 + 40*n + 19

def currentW (n : ℝ) : ℝ := 48*(n+3)^2 - 72*(n+3) + 9

theorem lower_cleared (n : ℝ) :
    32*(n+1)*(n+3)^2*previousV n + 768*(n+1)*(n+3)^2*(n+2)^3 -
      4*previousV n - (n+3)*currentW n*previousV n = lowerNumerator n := by
  dsimp [previousV, currentW, lowerNumerator]
  ring

theorem upper_cleared (n : ℝ) :
    V n*previousH n - 32*(n+1)*(n+3)^2*previousH n -
      256*(n+1)*(n+3)^2*(n+2)^2 - 4*previousH n = upperNumerator n := by
  dsimp [V, previousH, upperNumerator]
  ring

theorem lower_shift (n : ℝ) :
    lowerNumerator n = 304*(n-13)^3 + 13543*(n-13)^2 +
      199589*(n-13) + 971988 := by
  dsimp [lowerNumerator]
  ring

theorem upper_shift (n : ℝ) :
    upperNumerator n = 112*(n-13)^2 + 2403*(n-13) + 10980 := by
  dsimp [upperNumerator]
  ring

theorem lower_pos (n : ℝ) (hn : 13 ≤ n) : 0 < lowerNumerator n := by
  have ht : 0 ≤ n-13 := by linarith
  rw [lower_shift]
  positivity

theorem upper_pos (n : ℝ) (hn : 13 ≤ n) : 0 < upperNumerator n := by
  have ht : 0 ≤ n-13 := by linarith
  rw [upper_shift]
  positivity

def L (n : ℝ) : ℝ := 3 - 9/(2*(n+3)) + 9/(16*(n+3)^2)
def U (n : ℝ) : ℝ := L n + 2/(n+3)^3
def E (n : ℝ) : ℝ := 1/(8*(n+3)^2)

def y (n r u : ℝ) : ℝ := ((n+2)*(2*r+3)+2*u)/(n+4)
def z (n r u v : ℝ) : ℝ := ((n+3)*(2*y n r u+3*r)+2*v)/(n+5)
def F (n r u v : ℝ) : ℝ := (y n r u)^3-r^3*z n r u v

def fullDenominator (n : ℝ) : ℝ := 65536*(n+3)^11*(n+4)^3*(n+5)
def reducedDenominator (n : ℝ) : ℝ := 65536*(n+3)^8*(n+4)^3*(n+5)

/-- Scaled form avoids making a division equality at a zero denominator. -/
theorem corner_scaled (n : ℝ)
    (h3 : n+3 ≠ 0) (h4 : n+4 ≠ 0) (h5 : n+5 ≠ 0) :
    fullDenominator n * F n (U n) (-E n) (E n) = P n := by
  dsimp [fullDenominator, F, y, z, U, L, E, P]
  field_simp [h3, h4, h5]; ring

def gapShift (t : ℝ) : ℝ :=
  58605568*t^12 + 9653801984*t^11 + 723458556672*t^10 +
  32566142496352*t^9 + 978753038000288*t^8 + 20633351214169401*t^7 +
  311625831704217912*t^6 + 3377331981471101346*t^5 +
  25822213571611442448*t^4 + 133590768426096292509*t^3 +
  429272400422485948736*t^2 + 706171963822972745984*t +
  306994825721596657664

theorem quantitative_shift (n : ℝ) :
    P n - 800*reducedDenominator n = gapShift (n-12) := by
  dsimp [P, reducedDenominator, gapShift]
  ring

theorem quantitative_polynomial_pos (n : ℝ) (hn : 12 ≤ n) :
    800*reducedDenominator n < P n := by
  have ht : 0 ≤ n-12 := by linarith
  have hp : 0 < gapShift (n-12) := by unfold gapShift; positivity
  have he := quantitative_shift n
  linarith

theorem range_lower_shift (n : ℝ) :
    16*n^2 - 120*n - 477 = 16*(n-12)^2 + 264*(n-12) + 387 := by ring

theorem beta_margin (n : ℝ) :
    (n+3)*(7*n+20) - 5*(n+4)*(n+5) = 2*n^2 - 4*n - 40 := by ring

end Motzkin.Certificate
