import MLVDepthOne

/-!
# Reverse comparison for actual MLV chains of length one

For an algebraic algebraically closed ambient field, a complete length-one
chain implies the literal lower-degree approximation criterion. The ordinary
case is ruled out by absence of a maximal base approximation. In the limit
case, a lower-degree element beating all base centres would make its minimal
polynomial unstable, contrary to the full limit augmentation's stability.
-/

noncomputable section

open Polynomial

namespace NTCThird.MLV

universe u

variable {K : Type u} {E : Type*} [Field K] [Field E] [Algebra K E]

set_option maxHeartbeats 800000

omit [Field E] in
theorem sum_min_strict_of_large_member (s : Multiset E) (d : E → WithTop ℚ)
    (b : E) (hb : b ∈ s) {γ δ : ℚ} (hγδ : γ < δ) (hdb : (δ : WithTop ℚ) ≤ d b) :
    (s.map (fun c => min (γ : WithTop ℚ) (d c))).sum <
      (s.map (fun c => min (δ : WithTop ℚ) (d c))).sum := by
  classical
  rw [← Multiset.cons_erase hb, Multiset.map_cons, Multiset.map_cons,
    Multiset.sum_cons, Multiset.sum_cons]
  have hγδ' : (γ : WithTop ℚ) < (δ : WithTop ℚ) := by exact_mod_cast hγδ
  rw [min_eq_left (hγδ'.le.trans hdb), min_eq_left hdb]
  apply WithTop.add_lt_add_of_lt_of_le (sum_min_ne_top _ _ _)
  · exact hγδ'
  · exact Multiset.sum_map_le_sum_map _ _
      (fun c _ => min_le_min hγδ'.le le_rfl)

theorem monic_unstable_of_root_beyond_family [IsAlgClosed E]
    {I : Type*} [LinearOrder I]
    (v : AddValuation E (WithTop ℚ)) (θ : E) (a : I → K) (γ : I → ℚ)
    (hγ : ∀ i, (γ i : WithTop ℚ) = v (θ - algebraMap K E (a i)))
    (hincr : StrictMono γ)
    (μ : ∀ i, LinearMonomialValuation v (algebraMap K E (a i)) (γ i))
    (f : K[X]) (hf : f.Monic) (b : E) (hb : b ∈ f.aroots E)
    (hbeyond : ∀ i, (γ i : WithTop ℚ) ≤ v (θ - b)) :
    Unstable (fun i => restrictedMonomial (K := K) (μ i)) f := by
  intro i j hij
  change restrictedMonomial (μ i) f < restrictedMonomial (μ j) f
  rw [restrictedMonomial_apply, restrictedMonomial_apply,
    (μ i).root_formula θ (hγ i), (μ j).root_formula θ (hγ j)]
  have hmon : (f.map (algebraMap K E)).Monic := hf.map _
  rw [hmon.leadingCoeff, v.map_one, zero_add, zero_add]
  exact sum_min_strict_of_large_member _ (fun c => v (θ - c)) b hb
    (hincr hij) (hbeyond j)

/-- No separate approximation condition is assumed of the continuous family:
its actual linear key polynomials determine the required centre distances. -/
theorem baseApproximation_of_degree_one_limit [IsAlgClosed E] [Algebra.IsAlgebraic K E]
    (v : AddValuation E (WithTop ℚ)) (θ : E)
    {μ : AddValuation K[X] (WithTop ℚ)} {γ : WithTop ℚ}
    (L : LimitAugmentation μ (evaluationValuation v θ) (minpoly K θ) γ)
    (hdeg : L.family.stable_degree = 1)
    (hC : ∀ c : K, μ (C c) = v (algebraMap K E c)) :
    NTCThird.BaseApproximation K v θ := by
  classical
  letI := L.family.indexOrder
  letI := L.family.indexNonempty
  letI := L.family.indexNoMax
  let a : L.family.Index → K := fun i => -(L.family.polynomial i).coeff 0
  have hγ : ∀ i, (L.family.value i : WithTop ℚ) = v (θ - algebraMap K E (a i)) :=
    fun i => L.degree_one_family_value v θ hdeg hC i
  have hρ : L.family.valuation = fun i => baseBall v (a i) (L.family.value i) := by
    funext i
    exact L.family.degree_one_valuation v hdeg hC i
  intro b hb
  by_contra hn
  push_neg at hn
  have hbint : IsIntegral K b := (Algebra.IsAlgebraic.isAlgebraic (R := K) b).isIntegral
  have hmon := minpoly.monic hbint
  have hroot : b ∈ (minpoly K b).aroots E :=
    mem_aroots.mpr ⟨hmon.ne_zero, minpoly.aeval K b⟩
  have hu := monic_unstable_of_root_beyond_family v θ a L.family.value hγ
    L.family.strict_values
    (fun i => linearMonomialValuation v (algebraMap K E (a i)) (L.family.value i))
    (minpoly K b) hmon b hroot (fun i => by rw [hγ i]; exact (hn (a i)).le)
  obtain ⟨δ, hstable⟩ := L.stable_below (minpoly K b) hb
  rw [hρ] at hstable
  exact not_unstable_of_stableValue hstable hu

theorem no_ordinary_terminal_of_no_max
    (v : AddValuation E (WithTop ℚ)) (θ : E)
    (μ : AddValuation K[X] (WithTop ℚ)) (a : K) (γ : WithTop ℚ)
    (hμ : InitialMonomial (v.comap (algebraMap K E)) a γ μ)
    (hγ : γ = v (θ - algebraMap K E a))
    (hdegree : 1 < (minpoly K θ).natDegree)
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    ¬OrdinaryAugmentation μ (evaluationValuation v θ) (minpoly K θ) ⊤ := by
  intro A
  obtain ⟨b, hb⟩ := hbetter a
  have hfinite : γ ≠ ⊤ := by rw [hγ]; exact ne_of_lt (hb.trans_le le_top)
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hμ' : μ = baseBall v a q := by
    apply InitialMonomial.ext (γ := (q : WithTop ℚ))
    · rw [hq]
      exact hμ
    · exact baseBall_initial v a q
  have heq := A.low_degree_eq (X - C b) (by simpa using hdegree)
  have hqθ : (q : WithTop ℚ) = v (θ - algebraMap K E a) := hq.trans hγ
  rw [hμ', baseBall_linear_at_element v θ a b q hqθ] at heq
  have hq_lt : (q : WithTop ℚ) < v (θ - algebraMap K E b) := by rwa [hqθ]
  rw [min_eq_left hq_lt.le] at heq
  have heval : evaluationValuation v θ (X - C b) = v (θ - algebraMap K E b) := by simp
  rw [heval] at heq
  exact (ne_of_lt hq_lt) heq.symm

theorem finiteMLVChain_one_degree
    {v : AddValuation K (WithTop ℚ)} {ν : AddValuation K[X] (WithTop ℚ)} {F : K[X]}
    (C : FiniteMLVChain v ν F 1) : 1 < F.natDegree := by
  have h := C.strict_degrees (show (0 : Fin 2) < 1 by decide)
  change (C.polynomial 0).natDegree < (C.polynomial 1).natDegree at h
  have hlast : (Fin.last 1 : Fin 2) = 1 := rfl
  rw [C.initial_polynomial, natDegree_X_sub_C, ← hlast, C.terminal_polynomial] at h
  exact h

theorem baseApproximation_of_finiteMLVChain_one [IsAlgClosed E] [Algebra.IsAlgebraic K E]
    (v : AddValuation E (WithTop ℚ)) (θ : E)
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d))
    (C : FiniteMLVChain (v.comap (algebraMap K E))
      (evaluationValuation v θ) (minpoly K θ) 1) :
    NTCThird.BaseApproximation K v θ := by
  have hdegree := finiteMLVChain_one_degree C
  have hlast : (Fin.last 1 : Fin 2) = 1 := rfl
  have hφ₁ : C.polynomial 1 = minpoly K θ := C.terminal_polynomial
  have hν₁ : C.valuation 1 = evaluationValuation v θ := C.terminal_valuation
  have hγ₁ : C.value 1 = ⊤ := C.terminal_value
  have hγ₀ : C.value 0 = v (θ - algebraMap K E C.initial_center) := by
    have h := C.endpoint_values (0 : Fin 1)
    change evaluationValuation v θ (C.polynomial 0) = C.value 0 at h
    rw [C.initial_polynomial] at h
    simpa using h.symm
  have hstep := C.step (0 : Fin 1)
  change OrdinaryAugmentation (C.valuation 0) (C.valuation 1) (C.polynomial 1) (C.value 1) ∨
    ∃ L : LimitAugmentation (C.valuation 0) (C.valuation 1) (C.polynomial 1) (C.value 1),
      L.family.stable_degree = (C.polynomial 0).natDegree ∧
      ¬TangentDirection (C.valuation 0) (C.valuation 1) (C.polynomial 0) at hstep
  rw [hν₁, hφ₁, hγ₁] at hstep
  rcases hstep with A | ⟨L, hdeg, _⟩
  · exact (no_ordinary_terminal_of_no_max v θ (C.valuation 0) C.initial_center
      (C.value 0) C.initial_formula hγ₀ hdegree hbetter A).elim
  · rw [C.initial_polynomial, natDegree_X_sub_C] at hdeg
    exact baseApproximation_of_degree_one_limit v θ L hdeg (C.base_extension 0)

/-- The comparison concerns genuine finite chains and holds for each actual
generator, before any minimum over generators is taken. -/
theorem finiteMLVChain_one_iff [IsAlgClosed E] [Algebra.IsAlgebraic K E]
    (v : AddValuation E (WithTop ℚ)) (θ : E)
    (hbetter : ∀ c : K, ∃ d : K,
      v (θ - algebraMap K E c) < v (θ - algebraMap K E d)) :
    Nonempty (FiniteMLVChain (v.comap (algebraMap K E))
      (evaluationValuation v θ) (minpoly K θ) 1) ↔
      1 < NTCThird.elementDegree K θ ∧ NTCThird.BaseApproximation K v θ := by
  constructor
  · rintro ⟨C⟩
    exact ⟨finiteMLVChain_one_degree C,
      baseApproximation_of_finiteMLVChain_one v θ hbetter C⟩
  · rintro ⟨hdegree, happrox⟩
    exact exists_finiteMLVChain_one_of_baseApproximation v θ
      (Algebra.IsAlgebraic.isAlgebraic (R := K) θ).isIntegral hdegree hbetter happrox

end NTCThird.MLV
