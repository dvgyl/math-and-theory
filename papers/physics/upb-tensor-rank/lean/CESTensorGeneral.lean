import CESTensor
import GeneralDefs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions

open scoped BigOperators Matrix

namespace PPTCone

theorem noSR_sum_eq_zero {A B : Type*} {k r : ℕ}
    (S : Submodule ℂ (Matrix A B ℂ)) (hS : NoSR k S) (hr : r ≤ k)
    (a : Fin r → A → ℂ) (b : Fin r → B → ℂ)
    (hm : (fun i j => ∑ t, a t i * b t j) ∈ S) :
    (fun i j => ∑ t, a t i * b t j) = 0 :=
  hS _ hm ⟨r, hr, a, b, fun _ _ => rfl⟩

theorem noSR_one_of_noProduct {A B : Type*}
    (S : Submodule ℂ (Matrix A B ℂ)) (hS : NoProduct S) : NoSR 1 S := by
  intro X hX h
  obtain ⟨r, hr, a, b, hab⟩ := h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr with hr | hr
  · subst r
    ext i j
    simpa using hab i j
  · subst r
    have he : X = fun i j => a 0 i * b 0 j := by
      ext i j
      simpa using hab i j
    rw [he] at hX ⊢
    exact hS (a 0) (b 0) hX

theorem contract_sum_column_mem
    {A B C D I : Type*} [Fintype C] [Fintype I]
    (S : Submodule ℂ (Matrix A B ℂ))
    (U : I → Matrix A C ℂ) (V : I → B × D → ℂ)
    (hS : ∀ c d, (fun a b => ∑ t, U t a c * V t (b,d)) ∈ S)
    (x : C → ℂ) (d : D) :
    (fun a b => ∑ t, (U t *ᵥ x) a * V t (b,d)) ∈ S := by
  have hm := S.sum_mem (fun c (_ : c ∈ Finset.univ) => S.smul_mem (x c) (hS c d))
  convert hm using 1
  ext a b
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem contract_sum_row_mem
    {A B C D I : Type*} [Fintype A] [DecidableEq A] [Fintype I]
    (T : Submodule ℂ (Matrix C D ℂ))
    (U : I → Matrix A C ℂ) (V : I → B × D → ℂ)
    (hT : ∀ a b, (fun c d => ∑ t, U t a c * V t (b,d)) ∈ T)
    (φ : Module.Dual ℂ (A → ℂ)) (b : B) :
    (fun c d => ∑ t, φ (fun a => U t a c) * V t (b,d)) ∈ T := by
  have hm := T.sum_mem (fun a (_ : a ∈ Finset.univ) =>
    T.smul_mem (φ (Pi.single a 1)) (hT a b))
  convert hm using 1
  ext c d
  have he : ∀ t, φ (fun a => U t a c) = ∑ a, φ (Pi.single a 1) * U t a c :=
    fun t => dual_apply_eq_sum φ _
  simp only [he, Matrix.sum_apply, Matrix.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Every unrestricted finite Schmidt decomposition can be compressed so
that its right factors are linearly independent, without increasing length. -/
theorem HasSR.independent_right {A B : Type*} [Fintype B]
    {k : ℕ} {v : A × B → ℂ} (h : HasSR k v) :
    ∃ r : ℕ, r ≤ k ∧ ∃ a : Fin r → A → ℂ, ∃ b : Fin r → B → ℂ,
      LinearIndependent ℂ b ∧ ∀ i j, v (i,j) = ∑ t, a t i * b t j := by
  classical
  obtain ⟨n, hnk, a, b, hab⟩ := h
  let W := Submodule.span ℂ (Set.range b)
  let bb : Fin n → W := fun t => ⟨b t, Submodule.subset_span ⟨t, rfl⟩⟩
  let β := Module.finBasis ℂ W
  let r := Module.finrank ℂ W
  let aa : Fin r → A → ℂ := fun l i => ∑ t, a t i * β.repr (bb t) l
  let cc : Fin r → B → ℂ := fun l => (β l : B → ℂ)
  have hr : r ≤ n := by
    simpa [r, W, Set.finrank] using (finrank_range_le_card (R := ℂ) b)
  refine ⟨r, hr.trans hnk, aa, cc, ?_, ?_⟩
  · exact β.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  · intro i j
    have hrepr : ∀ t, b t j = ∑ l, β.repr (bb t) l * cc l j := by
      intro t
      have hh := congrArg (fun w : W => (w : B → ℂ) j) (β.sum_repr (bb t))
      simpa [cc, bb] using hh.symm
    rw [hab i j]
    calc
      (∑ t, a t i * b t j) = ∑ t, ∑ l, a t i * (β.repr (bb t) l * cc l j) := by
        simp_rw [hrepr, Finset.mul_sum]
      _ = ∑ l, ∑ t, a t i * (β.repr (bb t) l * cc l j) := Finset.sum_comm
      _ = ∑ l, aa l i * cc l j := by
        simp only [aa, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_congr rfl
        intro t _
        ring

theorem independent_coefficients_zero
    {I V : Type*} [Fintype I] [AddCommGroup V] [Module ℂ V]
    (b : I → V) (hb : LinearIndependent ℂ b) (a : I → ℂ)
    (h : ∑ t, a t • b t = 0) : ∀ t, a t = 0 := by
  intro t
  exact (linearIndependent_iff'.mp hb) Finset.univ a
    (by simpa using h) t (Finset.mem_univ t)

theorem independent_slices_zero
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (k n : ℕ) (hn : n + 1 ≤ k)
    (S : Submodule ℂ (Matrix A B ℂ)) (T : Submodule ℂ (Matrix C D ℂ))
    (hS : NoSR k S) (hT : NoSR k T)
    (U : Fin (n + 2) → Matrix A C ℂ) (V : Fin (n + 2) → B × D → ℂ)
    (hV : LinearIndependent ℂ V)
    (hSC : ∀ c d, (fun a b => ∑ t, U t a c * V t (b,d)) ∈ S)
    (hTC : ∀ a b, (fun c d => ∑ t, U t a c * V t (b,d)) ∈ T) :
    ∀ a c b d, (∑ t, U t a c * V t (b,d)) = 0 := by
  classical
  let f := (U 0).mulVecLin
  let g := (U 1).mulVecLin
  by_cases hf : f = 0
  · have hU0 : ∀ a c, U 0 a c = 0 := by
      intro a c
      have hh := LinearMap.congr_fun hf (Pi.single c 1)
      have hc : (fun a => U 0 a c) = 0 := by
        simpa [f, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hh
      exact congrFun hc a
    intro a c b d
    have hm : (fun a b => ∑ t : Fin (n+1), U t.succ a c * V t.succ (b,d)) ∈ S := by
      simpa only [Fin.sum_univ_succ, hU0, zero_mul, zero_add] using hSC c d
    have hz := noSR_sum_eq_zero S hS hn
      (fun t a => U t.succ a c) (fun t b => V t.succ (b,d)) hm
    rw [Fin.sum_univ_succ, hU0, zero_mul, zero_add]
    exact congrFun (congrFun hz a) b
  have hrange : LinearMap.range g ≤ LinearMap.range f := by
    rintro y ⟨x, rfl⟩
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range f) (g x)).mp
    intro φ hφ
    have hφ0 : ∀ c, φ (fun a => U 0 a c) = 0 := by
      intro c
      have hh := ((Submodule.mem_dualAnnihilator φ).mp hφ)
        (f (Pi.single c 1)) (LinearMap.mem_range_self f _)
      simpa [f, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hh
    have hzT : ∀ b, (fun c d => ∑ t : Fin (n+1),
        φ (fun a => U t.succ a c) * V t.succ (b,d)) = 0 := by
      intro b
      apply noSR_sum_eq_zero T hT hn
        (fun t c => φ (fun a => U t.succ a c)) (fun t d => V t.succ (b,d))
      simpa only [Fin.sum_univ_succ, hφ0, zero_mul, zero_add] using
        contract_sum_row_mem T U V hTC φ b
    have hφall : ∀ t c, φ (fun a => U t a c) = 0 := by
      intro t c
      apply independent_coefficients_zero V hV (fun t => φ (fun a => U t a c)) _ t
      ext ⟨b,d⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [Fin.sum_univ_succ, hφ0, zero_mul, zero_add]
      exact congrFun (congrFun (hzT b) c) d
    change φ (U 1 *ᵥ x) = 0
    rw [mulVec_eq_sum_columns, map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [map_smul, hφall]
    simp
  obtain ⟨x, z, hfx, hgx⟩ := pencil_has_dependent_value f g hf hrange
  have hzS : ∀ d, (fun a b => ∑ t, (U t *ᵥ x) a * V t (b,d)) = 0 := by
    intro d
    apply hS _ (contract_sum_column_mem S U V hSC x d)
    refine ⟨n+1, hn,
      Fin.cons (f x) (fun t : Fin n => U t.succ.succ *ᵥ x),
      Fin.cons (fun b => V 0 (b,d) + z * V 1 (b,d))
        (fun t : Fin n => fun b => V t.succ.succ (b,d)), ?_⟩
    intro a b
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    change (f x) a * V 0 (b,d) +
      ((g x) a * V 1 (b,d) + ∑ t : Fin n, (U t.succ.succ *ᵥ x) a * V t.succ.succ (b,d)) =
      (f x) a * (V 0 (b,d) + z * V 1 (b,d)) +
      ∑ t : Fin n, (U t.succ.succ *ᵥ x) a * V t.succ.succ (b,d)
    rw [hgx]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  exfalso
  apply hfx
  ext a
  have hcoeff := independent_coefficients_zero V hV (fun t => (U t *ᵥ x) a)
    (by
      ext ⟨b,d⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact congrFun (congrFun (hzS d) a) b) 0
  exact hcoeff

/-- If both matrix subspaces avoid nonzero Schmidt rank at most k, their
regrouped tensor product avoids nonzero Schmidt rank at most k+1. -/
theorem tensor_no_sr
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (k : ℕ) (hk : 1 ≤ k)
    (S : Submodule ℂ (Matrix A B ℂ)) (T : Submodule ℂ (Matrix C D ℂ))
    (hS : NoSR k S) (hT : NoSR k T)
    (v : (A × C) × (B × D) → ℂ)
    (hslices : ∀ c d, (fun a b => v ((a,c),(b,d))) ∈ S)
    (htslices : ∀ a b, (fun c d => v ((a,c),(b,d))) ∈ T)
    (hv : HasSR (k+1) v) : v = 0 := by
  obtain ⟨r, hr, a, b, hb, hab⟩ := hv.independent_right
  cases r with
  | zero =>
      ext p
      rcases p with ⟨i,j⟩
      simpa using hab i j
  | succ r =>
      cases r with
      | zero =>
          ext p
          rcases p with ⟨⟨i,c⟩,⟨j,d⟩⟩
          have hz := hS (fun i j => v ((i,c),(j,d))) (hslices c d)
            ⟨1, hk, (fun t i => a t (i,c)), (fun t j => b t (j,d)),
              fun i j => hab (i,c) (j,d)⟩
          exact congrFun (congrFun hz i) j
      | succ n =>
          have hn : n+1 ≤ k := Nat.le_of_succ_le_succ hr
          have hz := independent_slices_zero k n hn S T hS hT
            (fun t i c => a t (i,c)) b hb
            (fun c d => by simpa only [hab] using hslices c d)
            (fun i j => by simpa only [hab] using htslices i j)
          ext p
          rcases p with ⟨⟨i,c⟩,⟨j,d⟩⟩
          simpa only [hab] using hz i c j d

end PPTCone
