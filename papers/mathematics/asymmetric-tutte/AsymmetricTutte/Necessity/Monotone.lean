import AsymmetricTutte.Necessity.Base

namespace AsymmetricMerinoWelsh

open Finset Matroid
open Results.TutteThreshold

noncomputable section

variable {ι : Type*} [DecidableEq ι]

def rawEval (M : RkMat ι) (x y : ℝ) : ℝ := M.Z (x - 1) (y - 1) unitWeights

theorem rawEval_loop (M : RkMat ι) (x y : ℝ) {e : ι} (he : e ∈ M.E)
    (hloop : M.r {e} = 0) : rawEval M x y = y * rawEval (M.del e) x y := by
  unfold rawEval
  rw [M.Z_loop (x - 1) (y - 1) unitWeights he hloop]
  simp only [unitWeights]
  ring

theorem rawEval_coloop (M : RkMat ι) (x y : ℝ) {e : ι} (he : e ∈ M.E)
    (hcoloop : M.r (M.E.erase e) + 1 = M.r M.E) :
    rawEval M x y = x * rawEval (M.del e) x y := by
  unfold rawEval
  rw [M.Z_coloop (x - 1) (y - 1) unitWeights he hcoloop]
  simp only [unitWeights]
  ring

theorem rawEval_ord (M : RkMat ι) (x y : ℝ) {e : ι} (he : e ∈ M.E)
    (h1 : M.r {e} = 1) (hcoloop : M.r (M.E.erase e) = M.r M.E) :
    rawEval M x y = rawEval (M.del e) x y + rawEval (M.con e he) x y := by
  unfold rawEval
  rw [M.Z_ord (x - 1) (y - 1) unitWeights he h1 hcoloop]
  simp [unitWeights]

theorem rawEval_nonneg (M : RkMat ι) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ rawEval M x y := by
  induction hn : M.E.card using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases hE : M.E = ∅
    · rw [rawEval, M.Z_empty (x - 1) (y - 1) unitWeights hE]
      exact zero_le_one
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hE
      have hc : (M.E.erase e).card < n := by
        have := card_erase_lt_of_mem he
        omega
      have hd := ih _ hc (M.del e) rfl
      rcases M.posit_trichotomy he with hl | hc' | ⟨h1, hc'⟩
      · rw [rawEval_loop M x y he hl]
        exact mul_nonneg hy hd
      · rw [rawEval_coloop M x y he hc']
        exact mul_nonneg hx hd
      · rw [rawEval_ord M x y he h1 hc']
        exact add_nonneg hd (ih _ hc (M.con e he) rfl)

theorem rawEval_mono (M : RkMat ι) {x y x' y' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxx : x ≤ x') (hyy : y ≤ y') : rawEval M x y ≤ rawEval M x' y' := by
  induction hn : M.E.card using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases hE : M.E = ∅
    · rw [rawEval, rawEval, M.Z_empty (x - 1) (y - 1) unitWeights hE,
        M.Z_empty (x' - 1) (y' - 1) unitWeights hE]
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hE
      have hc : (M.E.erase e).card < n := by
        have := card_erase_lt_of_mem he
        omega
      have hd := ih _ hc (M.del e) rfl
      rcases M.posit_trichotomy he with hl | hc' | ⟨h1, hc'⟩
      · rw [rawEval_loop M x y he hl, rawEval_loop M x' y' he hl]
        exact mul_le_mul hyy hd (rawEval_nonneg _ hx hy) (hy.trans hyy)
      · rw [rawEval_coloop M x y he hc', rawEval_coloop M x' y' he hc']
        exact mul_le_mul hxx hd (rawEval_nonneg _ hx hy) (hx.trans hxx)
      · rw [rawEval_ord M x y he h1 hc', rawEval_ord M x' y' he h1 hc']
        exact add_le_add hd (ih _ hc (M.con e he) rfl)

theorem tutte_nonneg {α : Type*} (M : Matroid α) [M.Finite]
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ tutte M x y := by
  classical
  rw [tutte_eq_Z]
  exact rawEval_nonneg (toRk M) hx hy

theorem tutte_mono {α : Type*} (M : Matroid α) [M.Finite]
    {x y x' y' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxx : x ≤ x') (hyy : y ≤ y') :
    tutte M x y ≤ tutte M x' y' := by
  classical
  rw [tutte_eq_Z, tutte_eq_Z]
  exact rawEval_mono (toRk M) hx hy hxx hyy

end

end AsymmetricMerinoWelsh
