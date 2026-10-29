module
public import MilneDefs

@[expose] public section

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false

noncomputable section

namespace Milne

abbrev V3 := Fin 3 → ℝ
abbrev T3 := Matrix (Fin 3) (Fin 3) ℝ

def vDot (u v : V3) : ℝ := ∑ i, u i * v i
def vSq (u : V3) : ℝ := ∑ i, u i ^ 2
def tSq (T : T3) : ℝ := ∑ i, ∑ j, T i j ^ 2
def tVec (T : T3) (v : V3) : V3 := fun i => ∑ j, T i j * v j
def ttVec (T : T3) (v : V3) : V3 := fun j => ∑ i, T i j * v i

/-- The lift of a qubit operator to Alice's subsystem. -/
def onAlice (F : Matrix Q Q ℂ) : CMatrix :=
  fun i j => if i.2 = j.2 then F i.1 j.1 else 0

def pauliZ : Matrix Q Q ℂ := !![1, 0; 0, -1]

def pauli : Fin 3 → Matrix Q Q ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], pauliZ]

/-- The standard Pauli observable associated with a real three-vector. -/
def spin (v : V3) : Matrix Q Q ℂ :=
  !![(v 2 : ℂ), (v 0 : ℂ) - Complex.I*(v 1 : ℂ);
     (v 0 : ℂ) + Complex.I*(v 1 : ℂ), -(v 2 : ℂ)]

/-- The standard trace-one qubit matrix with Bloch vector v. -/
def qubitState (v : V3) : Matrix Q Q ℂ := (1/2:ℂ) • (1 + spin v)

/-- The standard Fano (Pauli) representation of a two-qubit state. Positivity
is a hypothesis in all physical theorems; no scalar surrogate is substituted. -/
def blochState (a b : V3) (T : T3) : CMatrix := fun i j =>
  (1/4:ℂ) * ((if i = j then 1 else 0) +
    (∑ k, (a k : ℂ) * onAlice (pauli k) i j) +
    (∑ k, (b k : ℂ) * onBob (pauli k) i j) +
    ∑ k, ∑ l, (T k l : ℂ) * pauli k i.1 j.1 * pauli l i.2 j.2)

end Milne
