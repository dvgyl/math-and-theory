import HahnApproximation
import TowerForwardFinite
import ClosureTransport

/-!
# Every base approximation in an actual AS tower improves

The strict improvement is uniform over all non-base elements of the tower,
not merely a selected AS generator.  The actual value-group support theorem
and monomial theorem discharge every hypothesis of leading-term cancellation.
The second theorem transports this fact to any actual embedding in the
algebraic closure with an extending valuation.
-/

noncomputable section
set_option maxHeartbeats 1200000
attribute [local instance 2000] HahnSeries.instAlgebra
attribute [local instance 3000] Algebra.id
attribute [local instance 2500] AlgebraicClosure.instAlgebra

open HahnSeries IntermediateField

namespace NTCThird

variable {k : Type*} [Field k]

theorem no_max_base_approximation_of_henselian_asTower
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ a ∈ K, LeftFinite a)
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (x : ℕ → HahnSeries ℚ k)
    (hF0 : F 0 = K.toSubfield)
    (hstep : ∀ i < N, ∃ a ∈ F i, x i ^ p - x i = a ∧
      F (i + 1) = (IntermediateField.adjoin (F i) {x i}).toSubfield)
    (θ : HahnSeries ℚ k) (hθ : θ ∈ F N) (hnot : θ ∉ K) :
    ∀ a : K, ∃ b : K, HahnSeries.addVal ℚ k (θ - a) <
      HahnSeries.addVal ℚ k (θ - b) := by
  have hmon := hahnValueGroup_single_mem_of_henselian K hK hy
  exact hahn_approximation_no_max K.toSubfield (hahnValueGroup K.toSubfield)
    hmon (fun a ha => supportedIn_hahnValueGroup_of_leftFinite
      K.toSubfield hmon a ha (hbase a ha)) θ
    (supportedIn_henselian_asTower p K hK hy hbase N F x hF0 hstep θ hθ) hnot

theorem closure_no_max_base_approximation_of_asTower
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (K : IntermediateField k (HahnSeries ℚ k)) [PerfectField K]
    (hK : RationalValuedHenselian (F := K)
      ((HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)))
    (hy : single (1 : ℚ) (1 : k) ∈ K)
    (hbase : ∀ a ∈ K, LeftFinite a)
    (N : ℕ) (F : ℕ → Subfield (HahnSeries ℚ k)) (x : ℕ → HahnSeries ℚ k)
    (hF0 : F 0 = K.toSubfield)
    (hstep : ∀ i < N, ∃ a ∈ F i, x i ^ p - x i = a ∧
      F (i + 1) = (IntermediateField.adjoin (F i) {x i}).toSubfield)
    (M : IntermediateField K (HahnSeries ℚ k)) (hFN : F N = M.toSubfield)
    (ι : M →ₐ[K] AlgebraicClosure K)
    (w : AddValuation (AlgebraicClosure K) (WithTop ℚ))
    (hw : ∀ a : K, w (algebraMap K (AlgebraicClosure K) a) =
      HahnSeries.addVal ℚ k (a : HahnSeries ℚ k))
    (θ : AlgebraicClosure K) (hθ : θ ∈ ι.fieldRange)
    (hdegree : 1 < elementDegree K θ) :
    ∀ a : K, ∃ b : K,
      w (θ - algebraMap K (AlgebraicClosure K) a) <
        w (θ - algebraMap K (AlgebraicClosure K) b) := by
  letI : Algebra K (HahnSeries ℚ k) := K.toAlgebra
  letI : FiniteDimensional K M :=
    finiteDimensional_actual_asTower p K N F x hF0 hstep M hFN
  letI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  obtain ⟨m, rfl⟩ := hθ
  change 1 < elementDegree K (ι m) at hdegree
  change ∀ a : K, ∃ b : K,
    w (ι m - algebraMap K (AlgebraicClosure K) a) <
      w (ι m - algebraMap K (AlgebraicClosure K) b)
  have hmnot : (m : HahnSeries ℚ k) ∉ K := by
    intro hmK
    let a : K := ⟨(m : HahnSeries ℚ k), hmK⟩
    have hm : m = algebraMap K M a := Subtype.ext rfl
    rw [hm, ι.commutes, elementDegree_algebraMap K a] at hdegree
    exact (lt_irrefl 1) hdegree
  have hmF : (m : HahnSeries ℚ k) ∈ F N := by
    rw [hFN]
    exact m.property
  let vK := (HahnSeries.addVal ℚ k).comap (SubringClass.subtype K)
  let vM := (HahnSeries.addVal ℚ k).comap (SubringClass.subtype M)
  have hval : ∀ z : M, w (ι z) = vM z :=
    valuation_embedding_apply_of_henselian vK hK vM (fun _ => rfl) w hw ι
  have hdist (a : K) :
      w (ι m - algebraMap K (AlgebraicClosure K) a) =
        HahnSeries.addVal ℚ k ((m : HahnSeries ℚ k) - (a : HahnSeries ℚ k)) := by
    rw [← ι.commutes, ← map_sub ι]
    exact hval (m - algebraMap K M a)
  intro a
  obtain ⟨b, hb⟩ := no_max_base_approximation_of_henselian_asTower
    p K hK hy hbase N F x hF0 hstep (m : HahnSeries ℚ k) hmF hmnot a
  refine ⟨b, ?_⟩
  rw [hdist, hdist]
  exact hb

end NTCThird
