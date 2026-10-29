module
public import AsymmetricTutte.Inputs
public import AsymmetricTutte.Coloops
public import AsymmetricTutte.Bases
public import AsymmetricTutte.RankOne


@[expose] public section

open Finset
open Results.TutteThreshold

namespace AsymmetricTutte

variable {ι : Type*} [DecidableEq ι]


def Claim (M : RkMat ι) (x y : ℝ) : Prop :=
  eval M 1 1 ^ 2 ≤ eval M x 0 * eval M 0 y

lemma claim_dual (M : RkMat ι) (x y : ℝ) : Claim M.dual y x ↔ Claim M x y := by
  simp only [Claim, eval_dual, mul_comm]

lemma claim_rank_one {M : RkMat ι} (hM : M.Admissible) (hr : M.r M.E = 1)
    {x y : ℝ} (hxy : ScalarInputs x y) : Claim M x y := by
  have hL : Loopless M := fun e he => (hM e he).1
  have hne : M.E.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro h
    rw [h, M.r_empty] at hr
    omega
  have hk := hM.two_le_card hne
  have hn : M.E.card ≠ 0 := by omega
  unfold Claim
  rw [eval_rank_one hL hr, eval_rank_one hL hr, eval_rank_one hL hr]
  simpa only [sub_self, zero_add, one_geom_sum, zero_geom_sum, if_neg hn,
    sub_add_cancel, zero_sub, neg_add_eq_sub] using hxy.rank_one M.E.card hk

lemma pair_class_card {M : RkMat ι} (_hM : Loopless M) {e f : ι}
    (hp : M.ParPair e f) : 2 ≤ (parClass M e).card := by
  have hsub : ({e, f} : Finset ι) ⊆ parClass M e := by
    refine insert_subset (self_mem_parClass hp.1 hp.2.2.2.1) ?_
    exact singleton_subset_iff.mpr (mem_parClass.mpr ⟨hp.2.1, hp.2.2.2.2.2⟩)
  have hc := card_le_card hsub
  simpa only [card_pair hp.2.2.1] using hc

lemma same_pair {M N : RkMat ι} (h : M.Same N) {e f : ι} (hp : M.ParPair e f) :
    N.ParPair e f := by
  obtain ⟨he, hf, hef, h1, h2, h3⟩ := hp
  refine ⟨h.1 ▸ he, h.1 ▸ hf, hef, ?_, ?_, ?_⟩
  · rw [← h.2 {e} (singleton_subset_iff.mpr he)]
    exact h1
  · rw [← h.2 {f} (singleton_subset_iff.mpr hf)]
    exact h2
  · rw [← h.2 {e, f} (insert_subset he (singleton_subset_iff.mpr hf))]
    exact h3

lemma mates_dual {M : RkMat ι}
    (hm : ∀ e ∈ M.E, ∃ f, M.ParPair e f ∨ M.SerPair e f) :
    ∀ e ∈ M.dual.E, ∃ f, M.dual.ParPair e f ∨ M.dual.SerPair e f := by
  intro e he
  obtain ⟨f, hp | hs⟩ := hm e he
  · exact ⟨f, Or.inr (same_pair M.dual_dual_same.symm hp)⟩
  · exact ⟨f, Or.inl hs⟩

lemma claim_parallel {M : RkMat ι} (hM : M.Admissible) {e f : ι}
    (hp : M.ParPair e f) (hm : ∀ e ∈ M.E, ∃ f, M.ParPair e f ∨ M.SerPair e f)
    {x y : ℝ} (hxy : ScalarInputs x y)
    (ih : ∀ N : RkMat ι, N.E.card < M.E.card → N.Admissible → Claim N x y) :
    Claim M x y := by
  have hL : Loopless M := fun e he => (hM e he).1
  have he := hp.1
  have hk := pair_class_card hL hp
  by_cases hC : M.r (M.E \ parClass M e) = M.r M.E
  · let L := classRest M e
    let N := classCollapse M e he
    let Q := N.con e (mem_insert_self _ _)
    have hN : N.Admissible := collapse_admissible hM he hC
    have hQ : Q.Admissible := collapse_contract_admissible hM he hC
    have hsizeL : L.E.card < M.E.card := class_rest_card_lt hL he
    have hsizeQ : Q.E.card < M.E.card := by
      rw [class_contract_ground hL he]
      exact hsizeL
    have hIQ := ih Q hsizeQ hQ
    have hA : (x - 1) * eval Q x 0 ≤ eval L x 0 := by
      have h := nbc_a (mem_insert_self e (M.E \ parClass M e))
        (hN e (mem_insert_self _ _)).1 (hN e (mem_insert_self _ _)).2 hxy.hx.le
      rw [eval_congr (class_deletion_same M hL he)] at h
      exact h
    have hV : (y - 1) * eval L 0 y ≤ eval Q 0 y := by
      have h := nbc_b (mem_insert_self e (M.E \ parClass M e))
        (hN e (mem_insert_self _ _)).1 (hN e (mem_insert_self _ _)).2 hxy.hy.le
      rw [eval_congr (class_deletion_same M hL he)] at h
      exact h
    have hz : (∑ j ∈ range (parClass M e).card, (0 : ℝ) ^ j) = 1 := by
      rw [zero_geom_sum, if_neg (by omega)]
    have hAx := class_recurrence hM he hC x 0
    have hCy := class_recurrence hM he hC 0 y
    have hBs := class_recurrence hM he hC 1 1
    rw [hz, one_mul] at hAx
    rw [one_geom_sum] at hBs
    have hU : 0 ≤ eval L 0 y := by rw [← eval_dual L]; exact eval_axis_nonneg _ hxy.hy.le
    have hV0 : 0 ≤ eval Q 0 y := by rw [← eval_dual Q]; exact eval_axis_nonneg _ hxy.hy.le
    by_cases hLc : Coloopless L
    · have hLA : L.Admissible := fun g hg => ⟨hL g (sdiff_subset hg), hLc g hg⟩
      have hIL := ih L hsizeL hLA
      unfold Claim at hIQ hIL ⊢
      rw [hAx, hCy, hBs]
      exact hxy.parallel _ hk _ _ _ _ _ _ (eval_axis_nonneg _ hxy.hx.le)
        (eval_axis_nonneg _ hxy.hx.le) hU hV0 (eval_basis_pos L).le (eval_basis_pos Q).le
        hA hV hIL hIQ
    · have hfcol : ∃ a ∈ L.E, L.r (L.E.erase a) + 1 = L.r L.E := by
        simp only [Coloopless, not_forall] at hLc
        obtain ⟨a, ha, hne⟩ := hLc
        rcases L.posit_trichotomy ha with h0 | hc | ⟨_, hc⟩
        · have := hL a (sdiff_subset ha)
          change M.r {a} = 0 at h0
          omega
        · exact ⟨a, ha, hc⟩
        · exact False.elim (hne hc)
      obtain ⟨a, ha, hac⟩ := hfcol
      obtain ⟨b, hb, hba, hbc⟩ := class_rest_coloop_mate hM he hk hC hm ha hac
      have hsame := class_deletion_same M hL he
      have hbound : 2 * eval L 1 1 ≤ eval Q 1 1 := by
        have haN : a ∈ (N.del e).E := hsame.1.symm ▸ ha
        have hbN : b ∈ (N.del e).E := hsame.1.symm ▸ hb
        have hacN : (N.del e).r ((N.del e).E.erase a) + 1 =
            (N.del e).r (N.del e).E := by
          rw [hsame.2 _ (erase_subset _ _), hsame.2 _ subset_rfl, hsame.1]
          exact hac
        have hbcN : (N.del e).r ((N.del e).E.erase b) + 1 =
            (N.del e).r (N.del e).E := by
          rw [hsame.2 _ (erase_subset _ _), hsame.2 _ subset_rfl, hsame.1]
          exact hbc
        have h := bases_contraction_ge_two hN (mem_insert_self _ _) haN hbN hba.symm
          hacN hbcN
        rw [eval_congr hsame] at h
        exact h
      have hzero := eval_axis_zero_of_coloop ha hac y
      unfold Claim at hIQ ⊢
      rw [hAx, hCy, hBs, hzero, zero_add]
      exact hxy.coloop _ hk _ _ _ _ _ (eval_axis_nonneg _ hxy.hx.le)
        (eval_axis_nonneg _ hxy.hx.le) hV0 (eval_basis_pos L).le (eval_basis_pos Q).le
        hA hIQ hbound
  · have hs := rank_one_separator hL he hC
    have hPc : (M.restrict (parClass M e) hs.1).Admissible := hM.restrict_sep hs
    have hCc : (classRest M e).Admissible := hM.restrict_sep hs.compl
    have hIC := ih _ (class_rest_card_lt hL he) hCc
    have hIP := claim_rank_one hPc (rank_parClass hL he) hxy
    unfold Claim at hIC hIP ⊢
    rw [eval_sep hs, eval_sep hs, eval_sep hs]
    have hprod := mul_le_mul hIP hIC (sq_nonneg _) (mul_nonneg
      (eval_axis_nonneg _ hxy.hx.le)
      (by rw [← eval_dual]; exact eval_axis_nonneg _ hxy.hy.le))
    dsimp only [classRest] at hprod
    nlinarith only [hprod]

theorem rankMat_sufficiency (M : RkMat ι) (hM : M.Admissible) {x y : ℝ}
    (hxy : ScalarInputs x y) (hyx : ScalarInputs y x) : Claim M x y := by
  suffices H : ∀ n : ℕ, ∀ M : RkMat ι, M.E.card = n → M.Admissible →
      ∀ x y : ℝ, ScalarInputs x y → ScalarInputs y x → Claim M x y from
    H _ M rfl hM x y hxy hyx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hn hM x y hxy hyx
    by_cases hempty : M.E = ∅
    · simp [Claim, eval_empty hempty]
    have hne := nonempty_iff_ne_empty.mpr hempty
    have IH : ∀ N : RkMat ι, N.E.card < M.E.card → N.Admissible → Claim N x y := by
      intro N hsize hN
      exact ih _ (by omega) N rfl hN x y hxy hyx
    by_cases hfree : ∃ e ∈ M.E, M.ClassFree e
    · obtain ⟨e, he, hp, hs⟩ := hfree
      have hc : (M.E.erase e).card < M.E.card := card_erase_lt_of_mem he
      have hd := IH (M.del e) hc (hM.del he hs)
      have hq := IH (M.con e he) hc (hM.con he hp)
      unfold Claim at hd hq ⊢
      rw [eval_ord he (hM e he).1 (hM e he).2,
        eval_ord he (hM e he).1 (hM e he).2, eval_ord he (hM e he).1 (hM e he).2]
      exact hxy.ordinary _ _ _ _ _ _ (eval_axis_nonneg _ hxy.hx.le)
        (eval_axis_nonneg _ hxy.hx.le)
        (by rw [← eval_dual]; exact eval_axis_nonneg _ hxy.hy.le)
        (by rw [← eval_dual]; exact eval_axis_nonneg _ hxy.hy.le)
        (eval_basis_pos _).le (eval_basis_pos _).le hd hq
    have hm : ∀ e ∈ M.E, ∃ f, M.ParPair e f ∨ M.SerPair e f := by
      intro e he
      by_contra h
      apply hfree
      refine ⟨e, he, ?_, ?_⟩
      · exact fun f hp => h ⟨f, Or.inl hp⟩
      · exact fun f hs => h ⟨f, Or.inr hs⟩
    obtain ⟨e, he⟩ := hne
    obtain ⟨f, hp | hs⟩ := hm e he
    · exact claim_parallel hM hp hm hxy IH
    · apply (claim_dual M x y).mp
      apply claim_parallel hM.dual hs (mates_dual hm) hyx
      intro N hsize hN
      exact ih _ (by simpa only [RkMat.dual_E, hn] using hsize) N rfl hN y x hyx hxy

theorem matroid_sufficiency {α : Type*} (M : Matroid α) [M.Finite] (hM : IsAdmissible M)
    {x y : ℝ} (hxy : ScalarInputs x y) (hyx : ScalarInputs y x) :
    tutte M 1 1 ^ 2 ≤ tutte M x 0 * tutte M 0 y := by
  classical
  simpa only [tutte_eq_Z, eval, Claim] using
    rankMat_sufficiency (toRk M) (admissible_toRk M hM) hxy hyx

end AsymmetricTutte
