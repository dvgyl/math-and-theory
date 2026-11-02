import Std
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace HarmonicBoundary.OddCounting

/- Coefficient lists are in increasing powers of t.  These are ordinary
   integer polynomial operations; the final theorem is an exact rational
   function identity certifying the period-four coefficient polynomials.
   The graph-counting correspondence is not formalized in this file. -/

def add : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a+b) :: add p q

def scale (c : Int) (p : List Int) : List Int := p.map (c * ·)

def mul : List Int → List Int → List Int
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

def pow (p : List Int) : Nat → List Int
  | 0 => [1]
  | n+1 => mul p (pow p n)

def shift (k : Nat) (p : List Int) : List Int := List.replicate k 0 ++ p
def norm (p : List Int) : List Int := (p.reverse.dropWhile (· == 0)).reverse

def numerator : List Int := [7,-3,-4,8,-1,4,11,-8,1,1]
def denominator : List Int := mul (mul (pow [1,-1] 5) (pow [1,1] 2)) [1,0,1]

def sumNumerator : List Int :=
  add (scale 2 denominator)
    (add (mul [5,6,-5,-5,3] (mul (mul (pow [1,-1] 2) [1,1]) [1,0,1]))
      (add (shift 1 (mul [2,2,4] (mul (mul [1,-1] [1,1]) [1,0,1])))
        (shift 2 [1,0,4,2,6,0,3])))

theorem disjoint_classes_sum_identity : norm sumNumerator = norm numerator := by decide

def newton (r : Fin 4) (j : Fin 5) : Int :=
  ((#[#[8,109,502,896,512], #[18,177,678,1024,512],
       #[36,280,886,1152,512], #[66,420,1126,1280,512]] : Array (Array Int))[r.val]!)[j.val]!

def periodDenominator : List Int := pow [1,0,0,0,-1] 5

def quasiNumerator : List Int :=
  (List.finRange 4).foldl (fun result r =>
    (List.finRange 5).foldl (fun value j =>
      add value (shift (r.val + 4*j.val)
        (scale (newton r j) (pow [1,0,0,0,-1] (4-j.val))))) result)
    (scale (-1) periodDenominator)

theorem quasipolynomial_rational_identity :
    norm (mul quasiNumerator denominator) =
    norm (mul numerator periodDenominator) := by decide

#print axioms disjoint_classes_sum_identity
#print axioms quasipolynomial_rational_identity

end HarmonicBoundary.OddCounting
