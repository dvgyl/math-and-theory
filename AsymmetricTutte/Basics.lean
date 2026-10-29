module
public import Results.TutteThreshold.Solution.Bridge
public import Results.TutteThreshold.Solution.Posit


@[expose] public section

/-!
Additional finite-matroid lemmas for the asymmetric universal Tutte inequality.
The underlying rank-sum definition and its bridge to Mathlib's `Matroid` are
imported from the pinned public `tutte-threshold` dependency.
-/

open Finset
open Matroid
open Results.TutteThreshold

namespace AsymmetricTutte

variable {ι : Type*} [DecidableEq ι]

abbrev unitWeight (_ : ι) : Wt := (1, 1)

noncomputable def eval (M : RkMat ι) (x y : ℝ) : ℝ :=
  M.Z (x - 1) (y - 1) unitWeight

def Loopless (M : RkMat ι) : Prop := ∀ e ∈ M.E, M.r {e} = 1

def Coloopless (M : RkMat ι) : Prop := ∀ e ∈ M.E, M.r (M.E.erase e) = M.r M.E

lemma eval_congr {M N : RkMat ι} (h : M.Same N) (x y : ℝ) :
    eval M x y = eval N x y :=
  RkMat.Z_congr (x - 1) (y - 1) h (fun _ _ => rfl)

lemma eval_dual (M : RkMat ι) (x y : ℝ) : eval M.dual x y = eval M y x := by
  unfold eval
  rw [RkMat.Z_dual]

lemma eval_empty {M : RkMat ι} (h : M.E = ∅) (x y : ℝ) : eval M x y = 1 :=
  M.Z_empty (x - 1) (y - 1) unitWeight h

lemma eval_axis_nonneg (M : RkMat ι) {x : ℝ} (hx : 1 ≤ x) : 0 ≤ eval M x 0 := by
  simpa [eval] using M.Z_nonneg_alpha (x - 1) unitWeight (by linarith) (by
    intro f hf
    exact ⟨zero_le_one, le_refl _⟩)

lemma eval_basis_pos (M : RkMat ι) : 0 < eval M 1 1 := by
  simpa [eval] using M.Zb_pos unitWeight (by
    intro f hf
    exact ⟨zero_lt_one, zero_lt_one⟩)

lemma eval_ord {M : RkMat ι} {e : ι} (he : e ∈ M.E)
    (h1 : M.r {e} = 1) (hc : M.r (M.E.erase e) = M.r M.E) (x y : ℝ) :
    eval M x y = eval (M.del e) x y + eval (M.con e he) x y := by
  simpa [eval, unitWeight] using M.Z_ord (x - 1) (y - 1) unitWeight he h1 hc

lemma eval_coloop {M : RkMat ι} {e : ι} (he : e ∈ M.E)
    (hc : M.r (M.E.erase e) + 1 = M.r M.E) (x y : ℝ) :
    eval M x y = x * eval (M.del e) x y := by
  simpa [eval, unitWeight] using M.Z_coloop (x - 1) (y - 1) unitWeight he hc

lemma eval_loop {M : RkMat ι} {e : ι} (he : e ∈ M.E)
    (h0 : M.r {e} = 0) (x y : ℝ) : eval M x y = y * eval (M.del e) x y := by
  simpa [eval, unitWeight] using M.Z_loop (x - 1) (y - 1) unitWeight he h0

lemma eval_sep {M : RkMat ι} {P : Finset ι} (hP : M.IsSep P) (x y : ℝ) :
    eval M x y = eval (M.restrict P hP.1) x y *
      eval (M.restrict (M.E \ P) sdiff_subset) x y :=
  M.Z_sep (x - 1) (y - 1) unitWeight hP

lemma nbc_a {M : RkMat ι} {e : ι} (he : e ∈ M.E)
    (h1 : M.r {e} = 1) (hc : M.r (M.E.erase e) = M.r M.E)
    {x : ℝ} (hx : 1 ≤ x) :
    (x - 1) * eval (M.con e he) x 0 ≤ eval (M.del e) x 0 := by
  simpa [eval] using M.nbc_alpha (x - 1) unitWeight (by linarith) he h1 hc (by
    intro g hg hge
    exact ⟨zero_le_one, le_refl _⟩)

lemma nbc_b {M : RkMat ι} {e : ι} (he : e ∈ M.E)
    (h1 : M.r {e} = 1) (hc : M.r (M.E.erase e) = M.r M.E)
    {y : ℝ} (hy : 1 ≤ y) :
    (y - 1) * eval (M.del e) 0 y ≤ eval (M.con e he) 0 y := by
  simpa [eval] using M.nbc_beta (y - 1) unitWeight (by linarith) he h1 hc (by
    intro g hg hge
    exact ⟨zero_le_one, le_refl _⟩)

lemma toRk_dual_same {α : Type*} [DecidableEq α] (M : Matroid α) [M.Finite] :
    (toRk M✶).Same (toRk M).dual := by
  refine ⟨by ext e; simp [Bridge.mem_toRk_E], fun S hS => ?_⟩
  have hSM : (S : Set α) ⊆ M.E := by
    intro e he
    exact (Bridge.mem_toRk_E M).mp (hS he)
  have h := M.eRk_dual_add_eRank (S : Set α) hSM
  rw [← Matroid.eRk_ground, ← Bridge.cast_rk M✶ (S : Set α),
    ← Bridge.cast_rk M M.E, ← Bridge.cast_rk M (M.E \ (S : Set α)),
    Set.encard_coe_eq_coe_finsetCard] at h
  have hn : rk M✶ (S : Set α) + rk M M.E =
      rk M (M.E \ (S : Set α)) + S.card := by exact_mod_cast h
  simp only [toRk_r, RkMat.dual_r, toRk_E, Finset.coe_sdiff,
    Set.Finite.coe_toFinset]
  omega

lemma tutte_dual {α : Type*} (M : Matroid α) [M.Finite] (x y : ℝ) :
    tutte M✶ x y = tutte M y x := by
  classical
  rw [tutte_eq_Z, RkMat.Z_congr (x - 1) (y - 1) (toRk_dual_same M) (fun _ _ => rfl),
    RkMat.Z_dual, tutte_eq_Z]

lemma admissible_dual {α : Type*} (M : Matroid α) [M.Finite] (hM : IsAdmissible M) :
    IsAdmissible M✶ := by
  constructor
  · exact hM.2
  · simpa only [Matroid.IsColoop, Matroid.dual_dual] using hM.1

end AsymmetricTutte
