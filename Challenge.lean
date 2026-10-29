module
public import Mathlib

/-! An exact five-cycle for classical projection-based two-block ADMM.
The penalty is one. Only the multiplier update is scaled by tau = 199/100.
The projections are unique global minimizers over the actual convex hulls. -/
@[expose] public section
noncomputable section

namespace ADMMGeometry
open scoped BigOperators

abbrev Vec := Fin 4 → ℝ

abbrev Vertices := Fin 5 → Vec

def sqDist (x y : Vec) : ℝ := ∑ j, (x j - y j) ^ 2

def polytope (v : Vertices) : Set Vec := convexHull ℝ (Set.range v)

def IsProjection (S : Set Vec) (q p : Vec) : Prop :=
  p ∈ S ∧
  (∀ y ∈ S, sqDist q p ≤ sqDist q y) ∧
  (∀ y ∈ S, sqDist q y ≤ sqDist q p → y = p)

end ADMMGeometry

namespace ADMMData

abbrev Vec := Fin 4 → ℝ

def tau : ℝ := 199 / 100

def v : Fin 5 → Vec := ![
  ![57, -289, 314, -85],
  ![-257, -143, -304, -116],
  ![-216, 200, 178, 273],
  ![124, 267, 16, -325],
  ![292, -35, -204, 253]]

def z : Fin 5 → Vec := ![
  ![20, -62, -161, 80],
  ![-52, -38, 177, 31],
  ![-53, 38, -126, -129],
  ![20, 62, 26, 178],
  ![65, 0, 84, -160]]

def x : Fin 5 → Vec := ![
  ![-215, -316, 357, -258],
  ![-366, 108, -441, 0],
  ![-12, 381, 356, 260],
  ![360, 129, -136, -420],
  ![233, -302, -136, 418]]

def u (i : Fin 5) : Vec := tau • v i

end ADMMData

namespace ADMMCounterexample
open ADMMGeometry ADMMData Filter
open scoped Topology

def C : Set ADMMData.Vec := polytope x

def D : Set ADMMData.Vec := polytope z

def phase (n : ℕ) : Fin 5 := ⟨n % 5, Nat.mod_lt _ (by decide)⟩

def X (n : ℕ) : ADMMData.Vec := x (phase n)

def Z (n : ℕ) : ADMMData.Vec := z (phase n)

def U (n : ℕ) : ADMMData.Vec := u (phase n)

def IsADMMTrajectory (C D : Set ADMMData.Vec) (t : ℝ)
    (X Z U : ℕ → ADMMData.Vec) : Prop :=
  ∀ n, IsProjection C (Z n - U n) (X (n + 1)) ∧
    IsProjection D (X (n + 1) + U n) (Z (n + 1)) ∧
    U (n + 1) = U n + t • (X (n + 1) - Z (n + 1))

theorem counterexample :
    (1 : ℝ) < tau ∧ tau < 2 ∧
    Convex ℝ C ∧ IsCompact C ∧ IsClosed C ∧
    Convex ℝ D ∧ IsCompact D ∧ IsClosed D ∧
    (0 : ADMMData.Vec) ∈ C ∩ D ∧
    IsADMMTrajectory C D tau (fun _ => 0) (fun _ => 0) (fun _ => 0) ∧
    IsADMMTrajectory C D tau X Z U ∧
    (∀ n, X (n + 5) = X n) ∧
    (∀ n, Z (n + 5) = Z n) ∧
    (∀ n, U (n + 5) = U n) ∧
    X 0 ≠ X 1 ∧
    (∀ n, (500000 : ℝ) ≤ sqDist (X n) (Z n)) ∧
    ¬ Tendsto (fun n : ℕ => sqDist (X n) (Z n)) atTop (𝓝 (0 : ℝ)) := by
  sorry

end ADMMCounterexample
