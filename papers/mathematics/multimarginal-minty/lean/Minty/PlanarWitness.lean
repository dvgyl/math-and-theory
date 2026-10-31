import Minty.Core

/-! A three-point integer witness in the real plane.  All computational
claims are kernel-checked algebraic theorems.  The obstruction concerns
actual triples compatible with the witness and having total zero. -/

namespace Minty

noncomputable def witness : Fin 3 → Triple :=
  ![![![-1, -2], ![3, -12], ![9, -2]],
    ![![-2, -5], ![0, -7], ![-14, -2]],
    ![![2, 0], ![-4, 15], ![14, -1]]]

theorem witness_compatible : ∀ i j, Compatible (witness i) (witness j) := by
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [pairing, total, witness, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem planar_certificate_identity (a b c d : ℝ) :
    4 * (a^2 + b^2 + 13*a - 12*b - 16) +
      3 * (c^2 + d^2 - 16*c - 49) +
      4 * ((-a-c)^2 + (-b-d)^2 + 12*(-a-c) - 10*(-b-d) - 52) +
      8 * (c^2 + d^2 + 20*c - 16*d + 79) =
    8 * (a + c/2 + 1/4)^2 + 8 * (b + d/2 - 1/2)^2 +
      13 * (c + 31/13)^2 + 13 * (d - 42/13)^2 + 23/26 := by
  ring

theorem planar_polynomial_obstruction (a b c d e f : ℝ)
    (hx : a + c + e = 0) (hy : b + d + f = 0)
    (hA : a^2 + b^2 + 13*a - 12*b - 16 ≤ 0)
    (hB : c^2 + d^2 - 16*c - 49 ≤ 0)
    (hC : e^2 + f^2 + 12*e - 10*f - 52 ≤ 0)
    (hD : c^2 + d^2 + 20*c - 16*d + 79 ≤ 0) : False := by
  have he : e = -a-c := by linarith
  have hf : f = -b-d := by linarith
  rw [he, hf] at hC
  have hi := planar_certificate_identity a b c d
  have h1 := sq_nonneg (a + c/2 + 1/4)
  have h2 := sq_nonneg (b + d/2 - 1/2)
  have h3 := sq_nonneg (c + 31/13)
  have h4 := sq_nonneg (d - 42/13)
  linarith

theorem no_zero_extension (u : Triple) (hs : total u = 0)
    (h : ∀ j, Compatible u (witness j)) : False := by
  have hA := h 0 0
  have hB := h 1 1
  have hC := h 1 2
  have hD := h 2 1
  rw [hs] at hA hB hC hD
  norm_num [pairing, total, witness, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at hA hB hC hD
  have hx := congrFun hs 0
  have hy := congrFun hs 1
  norm_num [total] at hx hy
  apply planar_polynomial_obstruction (u 0 0) (u 0 1) (u 1 0) (u 1 1)
    (u 2 0) (u 2 1) hx hy
  · nlinarith [hA]
  · nlinarith [hB]
  · nlinarith [hC]
  · nlinarith [hD]

end Minty
