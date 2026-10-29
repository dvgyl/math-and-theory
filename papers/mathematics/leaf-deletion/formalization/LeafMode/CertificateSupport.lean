import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace LeafMode.Cert
open Polynomial

/-- Interpret a coefficient list in ascending degree order. -/
noncomputable def ofList : List ℤ → Polynomial ℤ
  | [] => 0
  | a :: p => C a + X * ofList p

/-- Coefficientwise addition, padding the shorter input with zero. -/
def add : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : ℤ) (p : List ℤ) : List ℤ := p.map (a * ·)

def mul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

def derivAux (n : ℕ) : List ℤ → List ℤ
  | [] => []
  | a :: p => (a * n) :: derivAux (n+1) p

def deriv (p : List ℤ) : List ℤ := derivAux 1 p.tail

@[simp] theorem ofList_nil : ofList [] = 0 := rfl
@[simp] theorem ofList_cons (a : ℤ) (p : List ℤ) :
    ofList (a::p) = C a + X * ofList p := rfl

@[simp] theorem ofList_add (p q : List ℤ) : ofList (add p q) = ofList p + ofList q := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih, C_add]; ring

@[simp] theorem ofList_scale (a : ℤ) (p : List ℤ) : ofList (scale a p) = C a * ofList p := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
    change C (a*b) + X * ofList (scale a p) = C a * (C b + X * ofList p)
    rw [ih, C_mul]
    ring

@[simp] theorem ofList_mul (p q : List ℤ) : ofList (mul p q) = ofList p * ofList q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp only [mul, ofList_add, ofList_scale, ofList_cons, C_0, zero_add, ih]; ring

@[simp] theorem ofList_derivAux (n : ℕ) (p : List ℤ) :
    ofList (derivAux n p) = C (n : ℤ) * ofList p + X * (ofList p).derivative := by
  induction p generalizing n with
  | nil => simp [derivAux]
  | cons a p ih =>
    simp only [derivAux, ofList_cons, ih, derivative_add, derivative_C, derivative_mul,
      derivative_X, zero_add, one_mul, Nat.cast_add, Nat.cast_one, C_add, C_mul, C_1]
    ring

@[simp] theorem ofList_deriv (p : List ℤ) : ofList (deriv p) = (ofList p).derivative := by
  cases p with
  | nil => simp [deriv, derivAux]
  | cons a p => simp [deriv]

@[simp] theorem coeff_ofList (p : List ℤ) (n : ℕ) :
    (ofList p).coeff n = p[n]?.getD 0 := by
  induction p generalizing n with
  | nil => simp
  | cons a p ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [ofList_cons, coeff_add, coeff_X_mul, coeff_C_ne_zero (by omega)]
      simpa using ih n

/-- A polynomial solving this homogeneous first-order ODE with zero constant
term must be zero. -/
theorem ode_zero (a b h : Polynomial ℤ) (ha : a.coeff 0 ≠ 0)
    (h0 : h.coeff 0 = 0) (hh : a * h.derivative = b * h) : h = 0 := by
  apply Polynomial.ext
  intro n
  simp only [coeff_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact h0
    | succ n =>
      have hr : (b * h).coeff n = 0 := by
        rw [coeff_mul]
        apply Finset.sum_eq_zero
        rintro ⟨i,j⟩ hij
        have hs : i+j=n := Finset.mem_antidiagonal.mp hij
        have hj : j < n+1 := by omega
        simp [ih j hj]
      have hl : (a * h.derivative).coeff n = a.coeff 0 * (h.coeff (n+1) * (n+1)) := by
        rw [coeff_mul, Finset.sum_eq_single (0,n)]
        · simp [coeff_derivative]
        · rintro ⟨i,j⟩ hij hne
          have hs : i+j=n := Finset.mem_antidiagonal.mp hij
          have hi : i ≠ 0 := by
            intro hi
            subst i
            have hj : j=n := by omega
            subst j
            exact hne rfl
          have hj : j+1 < n+1 := by omega
          simp [coeff_derivative, ih (j+1) hj]
        · simp
      have he : a.coeff 0 * (h.coeff (n+1) * (n+1)) = 0 := by rw [← hl, hh, hr]
      have hn : (n+1 : ℤ) ≠ 0 := by omega
      exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left ha)).resolve_right hn

/-- A polynomial ODE with nonzero constant multiplier has a unique solution at a
specified constant term. -/
theorem ode_unique (a b f g : Polynomial ℤ) (ha : a.coeff 0 ≠ 0)
    (h0 : f.coeff 0 = g.coeff 0)
    (hf : a * f.derivative = b * f) (hg : a * g.derivative = b * g) : f = g := by
  apply sub_eq_zero.mp
  apply ode_zero a b (f-g) ha
  · simp [coeff_sub, h0]
  · simp only [derivative_sub, mul_sub, hf, hg]

/-- Exact list arithmetic can certify a polynomial power without trusting an
external symbolic-algebra package. -/
theorem power_of_ode (a f : List ℤ) (n : ℕ)
    (ha : a[0]?.getD 0 = 1) (hf0 : f[0]?.getD 0 = 1)
    (hODE : mul a (deriv f) = scale n (mul (deriv a) f)) :
    ofList f = ofList a ^ n := by
  apply ode_unique (ofList a) (C (n:ℤ) * (ofList a).derivative)
  · simpa [ha]
  · have hc (m : ℕ) : (ofList a ^ m).coeff 0 = 1 := by
      induction m with
      | zero => simp
      | succ m ih => simp [pow_succ, ih, ha]
    simp [hf0, hc]
  · have hh := congrArg ofList hODE
    simpa [mul_assoc] using hh
  · cases n with
    | zero => simp
    | succ n => rw [derivative_pow_succ, pow_succ]; simp only [Nat.cast_add, Nat.cast_one]; ring


/-- Check every adjacent coefficient inequality, including the last coefficient
against the zero coefficient beyond the supplied list. -/
def trend (i peak : ℕ) : List ℤ → Bool
  | [] => true
  | a :: p => decide (if i < peak then a ≤ p[0]?.getD 0 else p[0]?.getD 0 ≤ a)
      && trend (i+1) peak p

theorem trend_sound (i peak : ℕ) (p : List ℤ) (h : trend i peak p = true) (k : ℕ) :
    if i+k < peak then (ofList p).coeff k ≤ (ofList p).coeff (k+1)
    else (ofList p).coeff (k+1) ≤ (ofList p).coeff k := by
  induction p generalizing i k with
  | nil => simp
  | cons a p ih =>
    have hh := Bool.and_eq_true_iff.mp h
    cases k with
    | zero =>
      have hh0 := of_decide_eq_true hh.1
      simp only [coeff_ofList]
      simpa using hh0
    | succ k =>
      have hk := ih (i+1) hh.2 k
      simp only [coeff_ofList] at hk ⊢
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk

/-- Consecutive monotonicity gives comparison with the mode. -/
theorem le_of_between (f : ℕ → ℤ) (a b : ℕ) (hab : a ≤ b)
    (h : ∀ i, a ≤ i → i < b → f i ≤ f (i+1)) : f a ≤ f b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    have ih' : f a ≤ f b := ih (by intro i hai hib; exact h i hai (by omega))
    exact le_trans ih' (h b hab (by omega))

theorem peak_max (f : ℕ → ℤ) (m : ℕ)
    (hu : ∀ i, i < m → f i ≤ f (i+1))
    (hd : ∀ i, m ≤ i → f (i+1) ≤ f i) (k : ℕ) : f k ≤ f m := by
  by_cases h : k ≤ m
  · exact le_of_between f k m h (by intro i _ him; exact hu i him)
  · have hk : m ≤ k := by omega
    have hm := le_of_between (fun i => -f i) m k hk (by intro i hmi _; exact neg_le_neg (hd i hmi))
    simpa using neg_le_neg hm

/-- Strict inequalities at the two neighboring coefficients make the mode unique. -/
theorem peak_unique (f : ℕ → ℤ) (m : ℕ) (hm : 0 < m)
    (hu : ∀ i, i < m → f i ≤ f (i+1))
    (hd : ∀ i, m ≤ i → f (i+1) ≤ f i)
    (hl : f (m-1) < f m) (hr : f (m+1) < f m)
    (k : ℕ) (hk : k ≠ m) : f k < f m := by
  by_cases hkm : k < m
  · have hk' : k ≤ m-1 := by omega
    have hu' := le_of_between f k (m-1) hk' (by intro i _ hi; exact hu i (by omega))
    exact lt_of_le_of_lt hu' hl
  · have hk' : m+1 ≤ k := by omega
    have hd' := le_of_between (fun i => -f i) (m+1) k hk'
      (by intro i hi _; exact neg_le_neg (hd i (by omega)))
    exact lt_of_le_of_lt (by simpa using neg_le_neg hd') hr

end LeafMode.Cert
