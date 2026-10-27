module

public import SparsePolynomial
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

open scoped BigOperators
open Polynomial

namespace MathAndTheory.Gyires.RankTwo.Certificate

def scale (c : ℤ) (p : SparsePolynomial.Polynomial) : SparsePolynomial.Polynomial := SparsePolynomial.mul (SparsePolynomial.const c) p

def linear (a b : ℤ) : SparsePolynomial.Polynomial :=
  SparsePolynomial.add (scale a (SparsePolynomial.var 2)) (scale b (SparsePolynomial.var 3))

def sumPolys (ps : List SparsePolynomial.Polynomial) : SparsePolynomial.Polynomial :=
  ps.foldr SparsePolynomial.add (SparsePolynomial.const 0)

def elementaryPolys : List SparsePolynomial.Polynomial → ℕ → SparsePolynomial.Polynomial
  | [], 0 => SparsePolynomial.const 1
  | [], _+1 => SparsePolynomial.const 0
  | _::_, 0 => SparsePolynomial.const 1
  | p::ps, k+1 => SparsePolynomial.add (elementaryPolys ps (k+1))
      (SparsePolynomial.mul p (elementaryPolys ps k))

def profileForms (n a m L R : ℕ) : List SparsePolynomial.Polynomial :=
  List.replicate a (linear ((m : ℤ)*((n : ℤ)-L)) ((m : ℤ)*((n : ℤ)-R))) ++
  List.replicate m (linear ((n : ℤ)*((L : ℤ)-a)-(m : ℤ)*L) ((n : ℤ)*((R : ℤ)-a)-(m : ℤ)*R)) ++
  List.replicate (n-a-m) (linear (-(m : ℤ)*L) (-(m : ℤ)*R))

def Dpoly (n L R : ℕ) : SparsePolynomial.Polynomial :=
  SparsePolynomial.mul (linear L R) (linear ((n : ℤ)-L) ((n : ℤ)-R))

def Kpoly (n c l L R : ℕ) : SparsePolynomial.Polynomial :=
  SparsePolynomial.sub (scale l (Dpoly n L R))
    (scale n (SparsePolynomial.mul (linear ((L : ℤ)-c) ((R : ℤ)-c))
      (linear ((l : ℤ)+c-L) ((l : ℤ)+c-R))))

def Xpoly (n a m L R k : ℕ) : SparsePolynomial.Polynomial :=
  elementaryPolys (profileForms n a m L R) k

def Cpoly (n a m c l L R : ℕ) : SparsePolynomial.Polynomial :=
  sumPolys ((List.range (n+1)).map (fun k =>
    scale ((k.factorial : ℤ)*((n-k).factorial : ℤ)*((m : ℤ)*l)^(n-k))
      (SparsePolynomial.mul (SparsePolynomial.mul (Xpoly n a m L R k) (Xpoly n c l L R k))
        (SparsePolynomial.pow (Dpoly n L R) (n-k)))))

def Gpoly (n a m c l L R : ℕ) : SparsePolynomial.Polynomial :=
  sumPolys ((List.range (n+1)).map (fun k =>
    scale ((k.factorial : ℤ)*((n-k).factorial : ℤ)*(m : ℤ)^(2*(n-k))*(l : ℤ)^(n-k))
      (SparsePolynomial.mul (SparsePolynomial.mul (SparsePolynomial.pow (Xpoly n a m L R k) 2) (SparsePolynomial.pow (Kpoly n c l L R) k))
        (SparsePolynomial.pow (Dpoly n L R) (2*(n-k))))))

def Hpoly (n a m c l L R : ℕ) : SparsePolynomial.Polynomial :=
  SparsePolynomial.sub (scale ((m : ℤ)^n) (SparsePolynomial.mul (Cpoly n a m c l L R) (SparsePolynomial.pow (Dpoly n L R) n)))
    (Gpoly n a m c l L R)

def strongPoly (n a m c l L R : ℕ) : SparsePolynomial.Polynomial :=
  SparsePolynomial.sub (SparsePolynomial.pow (Cpoly n a m c l L R) 2)
    (scale ((n.factorial : ℤ)*(l : ℤ)^n) (Gpoly n a m c l L R))

lemma eval_scale (f : ℕ →* ℝ) (c : ℤ) (p : SparsePolynomial.Polynomial) :
    SparsePolynomial.eval f (scale c p) = c * SparsePolynomial.eval f p := by
  simp only [scale, SparsePolynomial.eval_mul, SparsePolynomial.eval_const]

lemma eval_linear (f : ℕ →* ℝ) (a b : ℤ) :
    SparsePolynomial.eval f (linear a b) = a*f 2+b*f 3 := by
  simp only [linear, SparsePolynomial.eval_add, eval_scale, SparsePolynomial.eval_var]

lemma eval_sumPolys (f : ℕ →* ℝ) (ps : List SparsePolynomial.Polynomial) :
    SparsePolynomial.eval f (sumPolys ps) = (ps.map (SparsePolynomial.eval f)).sum := by
  induction ps with
  | nil => simp [sumPolys, SparsePolynomial.eval_const]
  | cons p ps ih => simp only [sumPolys, List.foldr_cons, SparsePolynomial.eval_add,
      List.map_cons, List.sum_cons] at *; rw [ih]

lemma list_range_sum (h : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map h).sum = ∑ k ∈ Finset.range n, h k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

lemma coeff_linear_factor (b : ℝ) (p : ℝ[X]) (k : ℕ) :
    ((1+C b*X)*p).coeff (k+1) = p.coeff (k+1)+b*p.coeff k := by
  rw [add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]

lemma product_linear_constant (xs : List ℝ) :
    ((xs.map (fun x => (1+C x*X : ℝ[X]))).prod).coeff 0 = 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Polynomial.mul_coeff_zero, ih]

theorem eval_elementaryPolys (f : ℕ →* ℝ) (ps : List SparsePolynomial.Polynomial) (k : ℕ) :
    SparsePolynomial.eval f (elementaryPolys ps k) =
      ((ps.map (fun p => (1+C (SparsePolynomial.eval f p)*X : ℝ[X]))).prod).coeff k := by
  induction ps generalizing k with
  | nil => cases k <;> simp [elementaryPolys, SparsePolynomial.eval_const, Polynomial.coeff_one]
  | cons p ps ih =>
    cases k with
    | zero =>
        simpa only [elementaryPolys, SparsePolynomial.eval_const, Int.cast_one, List.map_map,
          Function.comp_def] using (product_linear_constant ((p::ps).map (SparsePolynomial.eval f))).symm
    | succ k =>
        simp only [elementaryPolys, SparsePolynomial.eval_add, SparsePolynomial.eval_mul, ih,
          List.map_cons, List.prod_cons, coeff_linear_factor]

theorem eval_Dpoly (f : ℕ →* ℝ) (n L R : ℕ) :
    SparsePolynomial.eval f (Dpoly n L R) =
      ((L : ℝ)*f 2+R*f 3)*(((n : ℝ)-L)*f 2+(n-R)*f 3) := by
  simp only [Dpoly, SparsePolynomial.eval_mul, eval_linear, Int.cast_sub, Int.cast_natCast]

theorem eval_Kpoly (f : ℕ →* ℝ) (n c l L R : ℕ) :
    SparsePolynomial.eval f (Kpoly n c l L R) = (l : ℝ)*SparsePolynomial.eval f (Dpoly n L R)-
      (n : ℝ)*(((L : ℝ)-c)*f 2+(R-c)*f 3)*(((l : ℝ)+c-L)*f 2+(l+c-R)*f 3) := by
  simp only [Kpoly, SparsePolynomial.eval_sub, eval_scale, SparsePolynomial.eval_mul, eval_linear,
    Int.cast_natCast, Int.cast_add, Int.cast_sub]
  ring

theorem eval_Cpoly (f : ℕ →* ℝ) (n a m c l L R : ℕ) :
    SparsePolynomial.eval f (Cpoly n a m c l L R) =
      ∑ k ∈ Finset.range (n+1), (k.factorial : ℝ)*((n-k).factorial : ℝ)*
        ((m : ℝ)*l)^(n-k)*SparsePolynomial.eval f (Xpoly n a m L R k)*SparsePolynomial.eval f (Xpoly n c l L R k)*
          SparsePolynomial.eval f (Dpoly n L R)^(n-k) := by
  simp only [Cpoly, eval_sumPolys, List.map_map, Function.comp_def,
    eval_scale, SparsePolynomial.eval_mul, SparsePolynomial.eval_pow, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    list_range_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem eval_Gpoly (f : ℕ →* ℝ) (n a m c l L R : ℕ) :
    SparsePolynomial.eval f (Gpoly n a m c l L R) =
      ∑ k ∈ Finset.range (n+1), (k.factorial : ℝ)*((n-k).factorial : ℝ)*
        (m : ℝ)^(2*(n-k))*(l : ℝ)^(n-k)*(SparsePolynomial.eval f (Xpoly n a m L R k))^2*
          SparsePolynomial.eval f (Kpoly n c l L R)^k*SparsePolynomial.eval f (Dpoly n L R)^(2*(n-k)) := by
  simp only [Gpoly, eval_sumPolys, List.map_map, Function.comp_def,
    eval_scale, SparsePolynomial.eval_mul, SparsePolynomial.eval_pow, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    list_range_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem eval_Hpoly (f : ℕ →* ℝ) (n a m c l L R : ℕ) :
    SparsePolynomial.eval f (Hpoly n a m c l L R) =
      (m : ℝ)^n*SparsePolynomial.eval f (Cpoly n a m c l L R)*SparsePolynomial.eval f (Dpoly n L R)^n-
        SparsePolynomial.eval f (Gpoly n a m c l L R) := by
  simp only [Hpoly, SparsePolynomial.eval_sub, eval_scale, SparsePolynomial.eval_mul, SparsePolynomial.eval_pow,
    Int.cast_pow, Int.cast_natCast]
  ring

end MathAndTheory.Gyires.RankTwo.Certificate
