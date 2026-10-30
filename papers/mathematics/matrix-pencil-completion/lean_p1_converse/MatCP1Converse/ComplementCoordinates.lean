module

public import MatCP1Converse.ComplementChart

@[expose] public section

namespace MatCP1Converse

open Matrix

variable {F n p m a b : Type*} [Field F]
  [Fintype n] [Fintype p] [Fintype m] [Fintype a] [Fintype b]
  [DecidableEq n] [DecidableEq p] [DecidableEq m]

omit [Fintype a] [DecidableEq m] in
/-- Every prescribed intrinsic quotient in this chart has exactly the displayed
two-block form, and its second block is a valid static quotient. -/
theorem complement_chart_recover_quotient
    (Gi : Matrix n n F) (B : Matrix n m F) (Qh : Matrix a (n ⊕ n) F)
    (hQh : Function.Surjective Qh.mulVec)
    (hk : LinearMap.ker Qh.mulVecLin =
      LinearMap.range (complementChartT Gi B).mulVecLin) :
    ∃ Q : Matrix a n F, Function.Surjective Q.mulVec ∧
      LinearMap.ker Q.mulVecLin = LinearMap.range (Gi * B).mulVecLin ∧
      Qh = complementChartQ Q := by
  have hcols : Qh.toCols₁ = -Qh.toCols₂ := by
    apply Matrix.mulVec_injective
    funext v
    have hm : Sum.elim v v ∈ LinearMap.range (complementChartT Gi B).mulVecLin := by
      refine ⟨Sum.elim v 0, ?_⟩
      simp [complementChartT, fromBlocks_mulVec]
    rw [← hk] at hm
    have hh : Qh.toCols₁ *ᵥ v + Qh.toCols₂ *ᵥ v = 0 := by
      change Qh *ᵥ Sum.elim v v = 0 at hm
      rw [← fromCols_toCols Qh, fromCols_mulVec_sumElim] at hm
      exact hm
    simpa only [Matrix.neg_mulVec] using eq_neg_of_add_eq_zero_left hh
  have hform : Qh = complementChartQ Qh.toCols₂ := by
    calc
      Qh = fromCols Qh.toCols₁ Qh.toCols₂ := (fromCols_toCols Qh).symm
      _ = complementChartQ Qh.toCols₂ := by rw [hcols]; rfl
  refine ⟨Qh.toCols₂, ?_, ?_, hform⟩
  · intro z
    obtain ⟨v, hv⟩ := hQh z
    refine ⟨(v ∘ Sum.inr) - (v ∘ Sum.inl), ?_⟩
    rw [hform] at hv
    simpa [complementChartQ, fromCols_mulVec, Matrix.neg_mulVec,
      Matrix.mulVec_sub, sub_eq_add_neg, add_comm, Matrix.mulVec_add,
      Matrix.mulVec_neg] using hv
  · apply le_antisymm
    · intro v hv
      have hm : Sum.elim (0 : n → F) v ∈
          LinearMap.range (complementChartT Gi B).mulVecLin := by
        rw [← hk]
        change Qh *ᵥ Sum.elim 0 v = 0
        rw [hform]
        simpa [complementChartQ, fromCols_mulVec] using
          (show Qh.toCols₂ *ᵥ v = 0 from hv)
      obtain ⟨w, hw⟩ := hm
      have ht : w ∘ Sum.inl = 0 := by
        have hh := congrArg (fun x : n ⊕ n → F => x ∘ Sum.inl) hw
        simpa [complementChartT, fromBlocks_mulVec] using hh
      refine ⟨w ∘ Sum.inr, ?_⟩
      have hh := congrArg (fun x : n ⊕ n → F => x ∘ Sum.inr) hw
      simpa [complementChartT, fromBlocks_mulVec, ht] using hh
    · rintro v ⟨w, rfl⟩
      have hm := LinearMap.mem_range_self (complementChartT Gi B).mulVecLin
        (Sum.elim 0 w)
      rw [← hk] at hm
      change Qh *ᵥ ((complementChartT Gi B) *ᵥ Sum.elim 0 w) = 0 at hm
      rw [hform] at hm
      simpa [complementChartQ, complementChartT, fromCols_mulVec,
        fromBlocks_mulVec] using hm

omit [Fintype p] [DecidableEq p] in
/-- Every prescribed intrinsic kernel basis in this chart has exactly the
displayed graph form. Its negated first block is a valid static kernel basis. -/
theorem complement_chart_recover_kernel
    (G Gi : Matrix n n F) (C : Matrix p n F) (Kh : Matrix (n ⊕ n) b F)
    (hGiG : Gi * G = 1) (hGGi : G * Gi = 1)
    (hKh : Function.Injective Kh.mulVec)
    (hr : LinearMap.range Kh.mulVecLin =
      LinearMap.ker (complementChartS G C).mulVecLin) :
    ∃ K : Matrix n b F, Function.Injective K.mulVec ∧
      LinearMap.range K.mulVecLin = LinearMap.ker (C * Gi).mulVecLin ∧
      Kh = complementChartK Gi K := by
  let K : Matrix n b F := -Kh.toRows₁
  have hform : Kh = complementChartK Gi K := by
    apply Matrix.mulVec_injective
    funext v
    have hm := LinearMap.mem_range_self Kh.mulVecLin v
    rw [hr] at hm
    have ht : Kh.toRows₁ *ᵥ v + G *ᵥ (Kh.toRows₂ *ᵥ v) = 0 := by
      have hh := congrArg (fun x : n ⊕ p → F => x ∘ Sum.inl)
        (show (complementChartS G C) *ᵥ (Kh *ᵥ v) = 0 from hm)
      rw [← fromRows_toRows Kh, fromRows_mulVec] at hh
      simpa [complementChartS, fromBlocks_mulVec] using hh
    have hbot : Kh.toRows₂ *ᵥ v = (Gi * K) *ᵥ v := by
      have hh := congrArg (fun x => Gi *ᵥ x)
        (eq_neg_of_add_eq_zero_right ht)
      simpa [K, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hGiG,
        Matrix.mul_neg, Matrix.neg_mulVec] using hh
    ext i
    cases i with
    | inl i =>
      change (Kh.toRows₁ *ᵥ v) i = ((-K) *ᵥ v) i
      simp [K]
    | inr i =>
      change (Kh.toRows₂ *ᵥ v) i = ((Gi * K) *ᵥ v) i
      exact congrFun hbot i
  refine ⟨K, ?_, ?_, hform⟩
  · intro v w hvw
    apply hKh
    rw [hform]
    simp only [complementChartK, fromRows_mulVec, Matrix.neg_mulVec,
      ← Matrix.mulVec_mulVec, hvw]
  · apply le_antisymm
    · rintro v ⟨w, rfl⟩
      have hm := LinearMap.mem_range_self Kh.mulVecLin w
      rw [hr] at hm
      have hh := congrArg (fun x : n ⊕ p → F => x ∘ Sum.inr)
        (show (complementChartS G C) *ᵥ (Kh *ᵥ w) = 0 from hm)
      rw [hform] at hh
      change (C * Gi) *ᵥ (K *ᵥ w) = 0
      simpa [complementChartS, complementChartK, fromBlocks_mulVec,
        fromRows_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hh
    · intro v hv
      have hm : Sum.elim (-v) (Gi *ᵥ v) ∈ LinearMap.range Kh.mulVecLin := by
        rw [hr]
        change (complementChartS G C) *ᵥ Sum.elim (-v) (Gi *ᵥ v) = 0
        have hz : (C * Gi) *ᵥ v = 0 := hv
        ext i
        cases i with
        | inl i => simp [complementChartS, fromBlocks_mulVec,
            Matrix.mulVec_mulVec, hGGi]
        | inr i => simpa [complementChartS, fromBlocks_mulVec,
            Matrix.mulVec_mulVec] using congrFun hz i
      obtain ⟨w, hw⟩ := hm
      refine ⟨w, ?_⟩
      change Kh *ᵥ w = Sum.elim (-v) (Gi *ᵥ v) at hw
      rw [hform] at hw
      have hh := congrArg (fun x : n ⊕ n → F => x ∘ Sum.inl) hw
      simpa [complementChartK, fromRows_mulVec, Matrix.neg_mulVec] using hh

/-- The actual intrinsic complementary pencils, with arbitrary prescribed full
quotient and kernel maps, satisfy the rank contraction in a common pivot chart.
The conclusion uses the genuine normal rank over `RatFunc F`. -/
theorem complement_chart_contraction [DecidableEq a] [DecidableEq b]
    (G0 Gi0 G1 Gi1 : Matrix n n F)
    (B0 B1 : Matrix n m F) (C0 C1 : Matrix p n F)
    (h0left : Gi0 * G0 = 1) (h0right : G0 * Gi0 = 1)
    (h1left : Gi1 * G1 = 1) (h1right : G1 * Gi1 = 1)
    (hB0 : Function.Injective B0.mulVec) (hB1 : Function.Injective B1.mulVec)
    (hC0 : Function.Surjective C0.mulVec) (hC1 : Function.Surjective C1.mulVec)
    (Q0 Q1 : Matrix a (n ⊕ n) F) (K0 K1 : Matrix (n ⊕ n) b F)
    (hQ0 : Function.Surjective Q0.mulVec) (hQ1 : Function.Surjective Q1.mulVec)
    (hK0 : Function.Injective K0.mulVec) (hK1 : Function.Injective K1.mulVec)
    (hker0 : LinearMap.ker Q0.mulVecLin =
      LinearMap.range (complementChartT Gi0 B0).mulVecLin)
    (hker1 : LinearMap.ker Q1.mulVecLin =
      LinearMap.range (complementChartT Gi1 B1).mulVecLin)
    (hrange0 : LinearMap.range K0.mulVecLin =
      LinearMap.ker (complementChartS G0 C0).mulVecLin)
    (hrange1 : LinearMap.range K1.mulVecLin =
      LinearMap.ker (complementChartS G1 C1).mulVecLin) :
    ∃ (L Li : Matrix a a F) (R Ri : Matrix b b F),
      L * Li = 1 ∧ Li * L = 1 ∧ R * Ri = 1 ∧ Ri * R = 1 ∧
      Pencil.normalRank
        ((L * (complementPencil Q1 K1).1 * R,
          L * (complementPencil Q1 K1).2 * R) - complementPencil Q0 K0) ≤
        (completedBlock G1 Gi1 B1 C1 - completedBlock G0 Gi0 B0 C0).rank := by
  obtain ⟨q0, hq0, hkq0, hformq0⟩ :=
    complement_chart_recover_quotient Gi0 B0 Q0 hQ0 hker0
  obtain ⟨q1, hq1, hkq1, hformq1⟩ :=
    complement_chart_recover_quotient Gi1 B1 Q1 hQ1 hker1
  obtain ⟨k0, hk0, hrk0, hformk0⟩ :=
    complement_chart_recover_kernel G0 Gi0 C0 K0 h0left h0right hK0 hrange0
  obtain ⟨k1, hk1, hrk1, hformk1⟩ :=
    complement_chart_recover_kernel G1 Gi1 C1 K1 h1left h1right hK1 hrange1
  obtain ⟨L, Li, R, Ri, hLl, hLr, hRl, hRr, hRank⟩ :=
    pivot_compression_strict_equivalence_bound G0 Gi0 G1 Gi1 B0 B1 C0 C1
      h0left h0right h1left h1right hB0 hB1 hC0 hC1
      q0 q1 k0 k1 hq0 hq1 hk0 hk1 hkq0 hkq1 hrk0 hrk1
  refine ⟨L, Li, R, Ri, hLl, hLr, hRl, hRr, ?_⟩
  simpa only [hformq0, hformq1, hformk0, hformk1,
    complement_chart_coefficients, Matrix.mul_assoc] using hRank

end MatCP1Converse
