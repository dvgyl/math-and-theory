module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.ListPolynomial

/-!
# Expression trees

`PolyExpr n` is a small syntax of polynomial expressions in `n` variables. `listInterpret`
evaluates an expression in coefficient lists and `realInterpret` in real numbers, and
`polyEval_listInterpret` proves that the two interpretations agree.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0

namespace MathAndTheory.GyiresCirculant5

inductive PolyExpr (n : ℕ) where
  | const : ℝ → PolyExpr n
  | var : Fin n → PolyExpr n
  | add : PolyExpr n → PolyExpr n → PolyExpr n
  | mul : PolyExpr n → PolyExpr n → PolyExpr n
  | scale : ℝ → PolyExpr n → PolyExpr n
  | pow : PolyExpr n → ℕ → PolyExpr n

def listInterpret {n : ℕ} : PolyExpr n → (Fin n → List ℝ) → List ℝ
  | .const c, _ => [c]
  | .var i, w => w i
  | .add p q, w => polyAdd (listInterpret p w) (listInterpret q w)
  | .mul p q, w => polyMul (listInterpret p w) (listInterpret q w)
  | .scale c p, w => polyScale c (listInterpret p w)
  | .pow p k, w => polyPow (listInterpret p w) k

def realInterpret {n : ℕ} : PolyExpr n → (Fin n → ℝ) → ℝ
  | .const c, _ => c
  | .var i, v => v i
  | .add p q, v => realInterpret p v + realInterpret q v
  | .mul p q, v => realInterpret p v * realInterpret q v
  | .scale c p, v => c * realInterpret p v
  | .pow p k, v => realInterpret p v ^ k

theorem polyEval_listInterpret {n : ℕ} (e : PolyExpr n)
    (w : Fin n → List ℝ) (x : ℝ) :
    polyEval (listInterpret e w) x =
      realInterpret e (fun i => polyEval (w i) x) := by
  induction e with
  | const c => exact polyEval_singleton c x
  | var i => rfl
  | add p q hp hq => exact polyEval_add_eq hp hq
  | mul p q hp hq => exact polyEval_mul_eq hp hq
  | scale c p hp => exact polyEval_scale_eq c hp
  | pow p k hp => exact polyEval_pow_eq k hp

end MathAndTheory.GyiresCirculant5
