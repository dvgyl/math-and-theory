import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sparse polynomials, square certificates and chambers

A polynomial in the gap variables `x 0, x 1, …` is a list of terms
`(exponent vector, integer coefficient)`, evaluated in any field; the sign
results hold in every linearly ordered field.  A chamber records the scaled
certificate polynomial `scale • F`, its nonnegative remainder split into the
degree-one part `lin` and the rest, and square triples
`p • x^(m+2u) - q • x^(m+u+v) + r • x^(m+2v)` with `p, r ≥ 0` and `q² ≤ 4pr`.
`Chamber.valid` is a Boolean check, evaluated by the kernel, that the
remainder and the squares add up to the polynomial, that every sign condition
holds and that the degree-one part is `(a-1)!` on exactly the gap segments
comparable with some element of the short chain.
-/

namespace ShortChain

/-- A term: exponent vector and integer coefficient. -/
abbrev Term := List ℕ × ℤ

/-- A square triple `p • x^(m+2u) - q • x^(m+u+v) + r • x^(m+2v)`. -/
structure Sq where
  m : List ℕ
  u : List ℕ
  v : List ℕ
  p : ℤ
  q : ℤ
  r : ℤ

/-- Certificate data for one chamber `(a, w)`. -/
structure Chamber where
  a : ℕ
  word : List Bool
  scale : ℕ
  poly : List Term
  lin : List Term
  rest : List Term
  squares : List Sq

/-- Lexicographic order on exponent vectors. -/
def lexLt : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | i :: l, j :: m => if i < j then true else if i = j then lexLt l m else false

/-- Insert a term into a sorted term list, adding coefficients of equal monomials. -/
def ins (t : Term) : List Term → List Term
  | [] => if t.2 = 0 then [] else [t]
  | s :: l =>
    if t.1 = s.1 then (if t.2 + s.2 = 0 then l else (t.1, t.2 + s.2) :: l)
    else if lexLt t.1 s.1 then (if t.2 = 0 then s :: l else t :: s :: l)
    else s :: ins t l

/-- Coordinatewise sum of exponent vectors (missing entries count as zero). -/
def vadd : List ℕ → List ℕ → List ℕ
  | [], l => l
  | i :: l, [] => i :: l
  | i :: l, j :: m => (i + j) :: vadd l m

/-- The three terms of a square triple. -/
def sqTerms (s : Sq) : List Term :=
  [(vadd s.m (vadd s.u s.u), s.p), (vadd s.m (vadd s.u s.v), -s.q),
    (vadd s.m (vadd s.v s.v), s.r)]

/-- Sign conditions making a square triple nonnegative on the orthant. -/
def sqOK (s : Sq) : Bool :=
  decide (0 ≤ s.p) && decide (0 ≤ s.r) && decide (s.q * s.q ≤ 4 * s.p * s.r)

/-- `heights w o c` lists, for each gap segment, the number of short-chain
elements incomparable with it: opened minus closed boundaries so far. -/
def heights : List Bool → ℕ → ℕ → List ℕ
  | [], o, c => [o - c]
  | true :: w, o, c => (o - c) :: heights w (o + 1) c
  | false :: w, o, c => (o - c) :: heights w o (c + 1)

/-- Indices `j, j+1, …` of the entries of a list that are below `a`. -/
def segs (a : ℕ) : List ℕ → ℕ → List ℕ
  | [], _ => []
  | h :: hs, j => if h < a then j :: segs a hs (j + 1) else segs a hs (j + 1)

/-- Gap segments whose elements are comparable with at least one element of
the short chain. -/
def comparableSegments (c : Chamber) : List ℕ := segs c.a (heights c.word 0 0) 0

/-- The unit exponent vector of length `d` at position `j`. -/
def unitVec : ℕ → ℕ → List ℕ
  | 0, _ => []
  | d + 1, 0 => 1 :: List.replicate d 0
  | d + 1, j + 1 => 0 :: unitVec d j

/-- The expected degree-one part of the remainder. -/
def expectedLin (c : Chamber) : List Term :=
  (comparableSegments c).map fun j =>
    (unitVec (2 * c.a + 1) j, ((c.scale * (c.a - 1).factorial : ℕ) : ℤ))

/-- The kernel-checked validity of a chamber certificate. -/
def Chamber.valid (c : Chamber) : Bool :=
  decide (0 < c.scale) && decide (0 < c.a) &&
  decide (List.foldr ins c.rest (c.lin ++ c.squares.flatMap sqTerms) = c.poly) &&
  c.rest.all (fun t => decide (0 ≤ t.2)) && c.squares.all sqOK &&
  decide (c.lin = expectedLin c)

/-- Dyck words with `k` opening letters left and `o` open letters, using `f`
letters in total. -/
def dyckF : ℕ → ℕ → ℕ → List (List Bool)
  | 0, k, o => if k = 0 ∧ o = 0 then [[]] else []
  | f + 1, k, o =>
    (if 0 < k then (dyckF f (k - 1) (o + 1)).map (true :: ·) else []) ++
    (if 0 < o then (dyckF f k (o - 1)).map (false :: ·) else [])

/-- All Dyck words with `a` letters `L` (`true`) and `a` letters `U` (`false`). -/
def dyckWords (a : ℕ) : List (List Bool) := dyckF (2 * a) a 0

theorem segs_lt (a : ℕ) (hs : List ℕ) (j k : ℕ) (hk : k ∈ segs a hs j) :
    k < j + hs.length := by
  induction hs generalizing j with
  | nil => simp [segs] at hk
  | cons h hs ih =>
    simp only [segs] at hk
    split_ifs at hk with hh
    · rcases List.mem_cons.mp hk with rfl | hk
      · simp
      · have := ih (j + 1) hk; simp only [List.length_cons]; omega
    · have := ih (j + 1) hk; simp only [List.length_cons]; omega

theorem heights_length (w : List Bool) (o c : ℕ) :
    (heights w o c).length = w.length + 1 := by
  induction w generalizing o c with
  | nil => simp [heights]
  | cons b w ih => cases b <;> simp [heights, ih]

/-! ### Evaluation in a field -/

section Eval

variable {R : Type*} [Field R]

/-- The monomial with exponent vector `e`, starting at variable `i`. -/
def mono : List ℕ → ℕ → (ℕ → R) → R
  | [], _, _ => 1
  | k :: e, i, x => x i ^ k * mono e (i + 1) x

/-- Evaluation of a term list. -/
def evalT (x : ℕ → R) (l : List Term) : R :=
  (l.map fun t => (t.2 : R) * mono t.1 0 x).sum

/-- The certificate polynomial `F_{a,w}` as a function of the gaps. -/
def Chamber.F (c : Chamber) (x : ℕ → R) : R := evalT x c.poly / c.scale

theorem mono_vadd (e f : List ℕ) (i : ℕ) (x : ℕ → R) :
    mono (vadd e f) i x = mono e i x * mono f i x := by
  induction e generalizing f i with
  | nil => simp [vadd, mono]
  | cons k e ih =>
    cases f with
    | nil => simp [vadd, mono]
    | cons l f => simp only [vadd, mono, ih, pow_add]; ring

theorem mono_replicate (d i : ℕ) (x : ℕ → R) : mono (List.replicate d 0) i x = 1 := by
  induction d generalizing i with
  | zero => simp [mono]
  | succ d ih => simp [List.replicate_succ, mono, ih]

theorem mono_unitVec (d j i : ℕ) (x : ℕ → R) (h : j < d) :
    mono (unitVec d j) i x = x (i + j) := by
  induction d generalizing j i with
  | zero => omega
  | succ d ih =>
    cases j with
    | zero => simp [unitVec, mono, mono_replicate]
    | succ j =>
      simp only [unitVec, mono, pow_zero, one_mul]
      rw [ih j (i + 1) (by omega)]
      congr 1
      omega

theorem evalT_nil (x : ℕ → R) : evalT x [] = 0 := by simp [evalT]

theorem evalT_cons (x : ℕ → R) (t : Term) (l : List Term) :
    evalT x (t :: l) = t.2 * mono t.1 0 x + evalT x l := by simp [evalT]

theorem evalT_append (x : ℕ → R) (l m : List Term) :
    evalT x (l ++ m) = evalT x l + evalT x m := by simp [evalT]

theorem evalT_ins (x : ℕ → R) (t : Term) (l : List Term) :
    evalT x (ins t l) = t.2 * mono t.1 0 x + evalT x l := by
  induction l with
  | nil =>
    by_cases h : t.2 = 0
    · simp [ins, h, evalT_nil]
    · simp [ins, h, evalT_cons, evalT_nil]
  | cons s l ih =>
    by_cases h1 : t.1 = s.1
    · by_cases h2 : t.2 + s.2 = 0
      · have h3 : ((t.2 + s.2 : ℤ) : R) = 0 := by rw [h2, Int.cast_zero]
        push_cast at h3
        simp only [ins, h1, ↓reduceIte, h2, evalT_cons]
        linear_combination (-(mono s.1 0 x)) * h3
      · simp only [ins, h1, ↓reduceIte, h2, ↓reduceIte, evalT_cons]
        push_cast
        ring
    · by_cases h4 : lexLt t.1 s.1 = true
      · by_cases h5 : t.2 = 0
        · simp [ins, h1, h4, h5, evalT_cons]
        · simp [ins, h1, h4, h5, evalT_cons]
      · simp only [ins, h1, h4, ↓reduceIte, Bool.false_eq_true, evalT_cons, ih]
        ring

theorem evalT_foldr_ins (x : ℕ → R) (base ts : List Term) :
    evalT x (List.foldr ins base ts) = evalT x ts + evalT x base := by
  induction ts with
  | nil => simp [evalT_nil]
  | cons t ts ih => rw [List.foldr_cons, evalT_ins, ih, evalT_cons]; ring

theorem evalT_expectedLin (c : Chamber) (hlen : c.word.length = 2 * c.a) (x : ℕ → R) :
    evalT x (expectedLin c) =
      ((c.scale * (c.a - 1).factorial : ℕ) : R) * ((comparableSegments c).map x).sum := by
  have hmem : ∀ j ∈ comparableSegments c, j < 2 * c.a + 1 := by
    intro j hj
    have := segs_lt c.a _ 0 j hj
    rw [heights_length, hlen] at this
    omega
  unfold expectedLin evalT
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply]
  rw [mono_unitVec _ _ _ _ (hmem j hj), zero_add]
  push_cast
  ring

/-- The certificate identity `scale • F = lin + rest + squares`. -/
theorem Chamber.evalT_poly (c : Chamber) (hc : c.valid = true) (x : ℕ → R) :
    evalT x c.poly = evalT x c.lin + evalT x (c.squares.flatMap sqTerms) + evalT x c.rest := by
  simp only [Chamber.valid, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [← hc.1.1.1.2, evalT_foldr_ins, evalT_append]

end Eval

/-! ### Signs over a linearly ordered field -/

section Order

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

theorem mono_nonneg (e : List ℕ) (i : ℕ) (x : ℕ → R) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ mono e i x := by
  induction e generalizing i with
  | nil => simp [mono]
  | cons k e ih => exact mul_nonneg (pow_nonneg (hx i) k) (ih (i + 1))

theorem quad_nonneg (p q r U V : R) (hp : 0 ≤ p) (hr : 0 ≤ r) (h : q * q ≤ 4 * p * r) :
    0 ≤ p * (U * U) - q * (U * V) + r * (V * V) := by
  rcases eq_or_lt_of_le hp with h0 | hpos
  · subst h0
    have hq : q = 0 := by nlinarith [mul_self_nonneg q]
    subst hq
    nlinarith [mul_self_nonneg V]
  · have key : 0 ≤ 4 * p * (p * (U * U) - q * (U * V) + r * (V * V)) := by
      nlinarith [mul_self_nonneg (2 * p * U - q * V), mul_self_nonneg V]
    exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : R) < 4 * p)).mp (by linarith)

theorem sqTerms_nonneg (s : Sq) (hs : sqOK s = true) (x : ℕ → R) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ evalT x (sqTerms s) := by
  simp only [sqOK, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨hp, hr⟩, hq⟩ := hs
  have hp' : (0 : R) ≤ s.p := by exact_mod_cast hp
  have hr' : (0 : R) ≤ s.r := by exact_mod_cast hr
  have hq' : (s.q : R) * s.q ≤ 4 * s.p * s.r := by exact_mod_cast hq
  have hm := mono_nonneg s.m 0 x hx
  have hquad := quad_nonneg (s.p : R) (s.q : R) (s.r : R) (mono s.u 0 x) (mono s.v 0 x) hp' hr' hq'
  have expand : evalT x (sqTerms s) =
      mono s.m 0 x * (s.p * (mono s.u 0 x * mono s.u 0 x) -
        s.q * (mono s.u 0 x * mono s.v 0 x) + s.r * (mono s.v 0 x * mono s.v 0 x)) := by
    simp only [sqTerms, evalT_cons, evalT_nil, mono_vadd]
    push_cast
    ring
  rw [expand]
  exact mul_nonneg hm hquad

theorem evalT_flatMap_nonneg (l : List Sq) (hl : l.all sqOK = true) (x : ℕ → R)
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ evalT x (l.flatMap sqTerms) := by
  induction l with
  | nil => simp [evalT_nil]
  | cons s l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rw [List.flatMap_cons, evalT_append]
    exact add_nonneg (sqTerms_nonneg s hl.1 x hx) (ih hl.2)

theorem evalT_nonneg (l : List Term) (hl : l.all (fun t => decide (0 ≤ t.2)) = true)
    (x : ℕ → R) (hx : ∀ i, 0 ≤ x i) : 0 ≤ evalT x l := by
  induction l with
  | nil => simp [evalT_nil]
  | cons t l ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
    rw [evalT_cons]
    have ht : (0 : R) ≤ t.2 := by exact_mod_cast hl.1
    exact add_nonneg (mul_nonneg ht (mono_nonneg _ _ x hx)) (ih hl.2)

/-- **Lower bound.**  A valid chamber polynomial dominates `(a-1)!` times the
sum of the gaps whose elements are comparable with the short chain. -/
theorem Chamber.lower_bound (c : Chamber) (hc : c.valid = true)
    (hlen : c.word.length = 2 * c.a) (x : ℕ → R) (hx : ∀ i, 0 ≤ x i) :
    ((c.a - 1).factorial : R) * ((comparableSegments c).map x).sum ≤ c.F x := by
  have hc' := hc
  simp only [Chamber.valid, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨hscale, _⟩, _⟩, hrest⟩, hsq⟩, hlin⟩ := hc'
  have hD : (0 : R) < c.scale := by exact_mod_cast hscale
  have h1 := c.evalT_poly hc x
  rw [hlin, evalT_expectedLin c hlen] at h1
  have h2 := evalT_flatMap_nonneg c.squares hsq x hx
  have h3 := evalT_nonneg c.rest hrest x hx
  unfold Chamber.F
  rw [le_div_iff₀ hD, h1]
  push_cast
  nlinarith

/-- **Nonnegativity.**  A valid chamber polynomial is nonnegative on the
closed nonnegative orthant. -/
theorem Chamber.nonneg (c : Chamber) (hc : c.valid = true)
    (hlen : c.word.length = 2 * c.a) (x : ℕ → R) (hx : ∀ i, 0 ≤ x i) : 0 ≤ c.F x := by
  refine le_trans ?_ (c.lower_bound hc hlen x hx)
  apply mul_nonneg (by positivity)
  exact List.sum_nonneg fun y hy => by
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
    exact hx j

end Order

end ShortChain
