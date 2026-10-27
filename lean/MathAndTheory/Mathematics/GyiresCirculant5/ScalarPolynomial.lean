module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.Definitions
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Scalar forms

`P5Scalar` is `P5` as a function of five real arguments, and `gram_eq_vector`, `conv_eq_vector`
write the autocorrelation and self-convolution of `![a, b, c, d, e]` explicitly.
-/

@[expose] public section

open scoped BigOperators
namespace MathAndTheory.GyiresCirculant5

def P5Scalar (a b c d e : ℝ) : ℝ :=
    a ^ 5 +
    5 * a ^ 3 * b * e +
    5 * a ^ 3 * c * d +
    5 * a ^ 2 * b ^ 2 * d +
    5 * a ^ 2 * b * c ^ 2 +
    5 * a ^ 2 * c * e ^ 2 +
    5 * a ^ 2 * d ^ 2 * e +
    5 * a * b ^ 3 * c +
    5 * a * b ^ 2 * e ^ 2 +
    15 * a * b * c * d * e +
    5 * a * b * d ^ 3 +
    5 * a * c ^ 3 * e +
    5 * a * c ^ 2 * d ^ 2 +
    5 * a * d * e ^ 3 +
    b ^ 5 +
    5 * b ^ 3 * d * e +
    5 * b ^ 2 * c ^ 2 * e +
    5 * b ^ 2 * c * d ^ 2 +
    5 * b * c ^ 3 * d +
    5 * b * c * e ^ 3 +
    5 * b * d ^ 2 * e ^ 2 +
    c ^ 5 +
    5 * c ^ 2 * d * e ^ 2 +
    5 * c * d ^ 3 * e +
    d ^ 5 +
    e ^ 5

theorem P5_vector (a b c d e : ℝ) :
    P5 (![a,b,c,d,e]) = P5Scalar a b c d e := by
  rfl

theorem gram_eq_vector (a b c d e : ℝ) :
    gram (![a,b,c,d,e]) =
      ![a*a+b*b+c*c+d*d+e*e,
        a*b+b*c+c*d+d*e+e*a,
        a*c+b*d+c*e+d*a+e*b,
        a*c+b*d+c*e+d*a+e*b,
        a*b+b*c+c*d+d*e+e*a] := by
  funext k
  fin_cases k <;> norm_num [gram, Fin.sum_univ_succ]
  · change a*a + (b*b + (c*c + (d*d + (e*e)))) = a*a+b*b+c*c+d*d+e*e
    ring
  · change a*b + (b*c + (c*d + (d*e + (e*a)))) = a*b+b*c+c*d+d*e+e*a
    ring
  · change a*c + (b*d + (c*e + (d*a + (e*b)))) = a*c+b*d+c*e+d*a+e*b
    ring
  · change a*d + (b*e + (c*a + (d*b + (e*c)))) = a*c+b*d+c*e+d*a+e*b
    ring
  · change a*e + (b*a + (c*b + (d*c + (e*d)))) = a*b+b*c+c*d+d*e+e*a
    ring

theorem conv_eq_vector (a b c d e : ℝ) :
    conv (![a,b,c,d,e]) =
      ![a*a+b*e+c*d+d*c+e*b,
        a*b+b*a+c*e+d*d+e*c,
        a*c+b*b+c*a+d*e+e*d,
        a*d+b*c+c*b+d*a+e*e,
        a*e+b*d+c*c+d*b+e*a] := by
  funext k
  fin_cases k <;> norm_num [conv, Fin.sum_univ_succ]
  · change a*a + (b*e + (c*d + (d*c + (e*b)))) = a*a+b*e+c*d+d*c+e*b
    ring
  · change a*b + (b*a + (c*e + (d*d + (e*c)))) = a*b+b*a+c*e+d*d+e*c
    ring
  · change a*c + (b*b + (c*a + (d*e + (e*d)))) = a*c+b*b+c*a+d*e+e*d
    ring
  · change a*d + (b*c + (c*b + (d*a + (e*e)))) = a*d+b*c+c*b+d*a+e*e
    ring
  · change a*e + (b*d + (c*c + (d*b + (e*a)))) = a*e+b*d+c*c+d*b+e*a
    ring

theorem P5_gram_vector (a b c d e : ℝ) :
    P5 (gram (![a,b,c,d,e])) =
    P5Scalar (a*a+b*b+c*c+d*d+e*e)
      (a*b+b*c+c*d+d*e+e*a)
      (a*c+b*d+c*e+d*a+e*b)
      (a*c+b*d+c*e+d*a+e*b)
      (a*b+b*c+c*d+d*e+e*a) := by
  rw [gram_eq_vector, P5_vector]

theorem P5_conv_vector (a b c d e : ℝ) :
    P5 (conv (![a,b,c,d,e])) =
    P5Scalar (a*a+b*e+c*d+d*c+e*b)
      (a*b+b*a+c*e+d*d+e*c)
      (a*c+b*b+c*a+d*e+e*d)
      (a*d+b*c+c*b+d*a+e*e)
      (a*e+b*d+c*c+d*b+e*a) := by
  rw [conv_eq_vector, P5_vector]

end MathAndTheory.GyiresCirculant5
