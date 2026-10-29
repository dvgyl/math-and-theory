import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary entropy of finite probability distributions

This file proves the finite entropy tools used in the quartic
ranking theorem directly from the logarithmic inequality `log x ≤ x - 1`.
All maps are literal pushforwards, with no independence assumption.
-/

noncomputable section
open scoped BigOperators

namespace PermEntropy

structure FinDist (α : Type*) [Fintype α] where
  mass : α → ℝ
  mass_nonneg : ∀ a, 0 ≤ mass a
  mass_sum : ∑ a, mass a = 1

namespace FinDist

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

local instance : DecidableEq α := Classical.decEq α
local instance : DecidableEq β := Classical.decEq β
local instance : DecidableEq γ := Classical.decEq γ

@[ext] theorem ext {p q : FinDist α} (h : ∀ a, p.mass a = q.mass a) : p = q := by
  cases p
  cases q
  congr
  funext a
  exact h a

def expect (p : FinDist α) (f : α → ℝ) : ℝ := ∑ a, p.mass a * f a

def entropy (p : FinDist α) : ℝ := ∑ a, Real.negMulLog (p.mass a)

def map (p : FinDist α) (f : α → β) : FinDist β := by
  classical
  exact
    { mass := fun b => ∑ a, if f a = b then p.mass a else 0
      mass_nonneg := fun b => Finset.sum_nonneg fun a _ => by
        split_ifs
        · exact p.mass_nonneg a
        · exact le_rfl
      mass_sum := by
        rw [Finset.sum_comm]
        simpa using p.mass_sum }

@[simp] theorem map_mass (p : FinDist α) (f : α → β) (b : β) :
    (p.map f).mass b = ∑ a, if f a = b then p.mass a else 0 := rfl

theorem nonempty (p : FinDist α) : Nonempty α := by
  classical
  by_contra h
  haveI : IsEmpty α := not_nonempty_iff.mp h
  simpa using p.mass_sum

theorem mass_le_one (p : FinDist α) (a : α) : p.mass a ≤ 1 := by
  classical
  calc
    p.mass a ≤ ∑ b, p.mass b :=
      Finset.single_le_sum (fun b _ => p.mass_nonneg b) (Finset.mem_univ a)
    _ = 1 := p.mass_sum

theorem mass_le_map (p : FinDist α) (f : α → β) (a : α) :
    p.mass a ≤ (p.map f).mass (f a) := by
  classical
  simpa only [map_mass, if_pos rfl] using
    (Finset.single_le_sum
      (f := fun x => if f x = f a then p.mass x else 0)
      (fun x _ => by
        dsimp only
        split_ifs
        · exact p.mass_nonneg x
        · exact le_rfl) (Finset.mem_univ a))

@[simp] theorem expect_const (p : FinDist α) (c : ℝ) :
    p.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, p.mass_sum]

@[simp] theorem expect_zero (p : FinDist α) : p.expect (fun _ => 0) = 0 :=
  p.expect_const 0

theorem expect_add (p : FinDist α) (f g : α → ℝ) :
    p.expect (fun a => f a + g a) = p.expect f + p.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (p : FinDist α) (f g : α → ℝ) :
    p.expect (fun a => f a - g a) = p.expect f - p.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_neg (p : FinDist α) (f : α → ℝ) :
    p.expect (fun a => -f a) = -p.expect f := by
  simp [expect, Finset.sum_neg_distrib]

theorem expect_mul_const (p : FinDist α) (f : α → ℝ) (c : ℝ) :
    p.expect (fun a => f a * c) = p.expect f * c := by
  simp [expect, mul_assoc, Finset.sum_mul]

theorem expect_const_mul (p : FinDist α) (c : ℝ) (f : α → ℝ) :
    p.expect (fun a => c * f a) = c * p.expect f := by
  simpa only [mul_comm c] using p.expect_mul_const f c

theorem expect_mono (p : FinDist α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    p.expect f ≤ p.expect g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (p.mass_nonneg a)

theorem expect_nonneg (p : FinDist α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ p.expect f := Finset.sum_nonneg fun a _ => mul_nonneg (p.mass_nonneg a) (h a)

theorem expect_congr (p : FinDist α) {f g : α → ℝ} (h : ∀ a, f a = g a) :
    p.expect f = p.expect g := by
  unfold expect
  exact Finset.sum_congr rfl fun a _ => congrArg (p.mass a * ·) (h a)

theorem expect_sum (p : FinDist α) {ι : Type*} (s : Finset ι) (f : ι → α → ℝ) :
    p.expect (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, p.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem exists_expect_le (p : FinDist α) (f : α → ℝ) :
    ∃ a, p.expect f ≤ f a := by
  classical
  haveI : Nonempty α := p.nonempty
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  refine ⟨a, ?_⟩
  calc
    p.expect f ≤ p.expect (fun _ => f a) :=
      p.expect_mono (fun b => ha b (Finset.mem_univ b))
    _ = f a := p.expect_const _

@[simp] theorem map_expect (p : FinDist α) (f : α → β) (g : β → ℝ) :
    (p.map f).expect g = p.expect (fun a => g (f a)) := by
  classical
  simp only [expect, map_mass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

theorem map_mass_eq_expect (p : FinDist α) (f : α → β) (b : β) :
    (p.map f).mass b = p.expect (fun a => if f a = b then 1 else 0) := by
  classical
  simp [map_mass, expect, mul_ite]

@[simp] theorem map_map (p : FinDist α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map (fun a => g (f a)) := by
  ext c
  rw [map_mass_eq_expect, map_expect, map_mass_eq_expect]

@[simp] theorem map_id (p : FinDist α) : p.map id = p := by
  classical
  ext a
  simp [map_mass]

theorem map_congr (p : FinDist α) {f g : α → β} (h : ∀ a, f a = g a) :
    p.map f = p.map g := by
  congr 1
  exact funext h

theorem entropy_eq_expect (p : FinDist α) :
    p.entropy = p.expect (fun a => -Real.log (p.mass a)) := by
  simp [entropy, expect, Real.negMulLog, neg_mul, mul_neg]

theorem entropy_nonneg (p : FinDist α) : 0 ≤ p.entropy :=
  Finset.sum_nonneg fun a _ => Real.negMulLog_nonneg (p.mass_nonneg a) (p.mass_le_one a)

theorem map_mass_apply_of_injective (p : FinDist α) (f : α → β)
    (hf : Function.Injective f) (a : α) : (p.map f).mass (f a) = p.mass a := by
  classical
  simp only [map_mass, hf.eq_iff]
  simp

theorem entropy_map_injective (p : FinDist α) (f : α → β)
    (hf : Function.Injective f) : (p.map f).entropy = p.entropy := by
  rw [entropy_eq_expect, map_expect, entropy_eq_expect]
  apply p.expect_congr
  intro a
  rw [p.map_mass_apply_of_injective f hf a]

theorem entropy_map_le (p : FinDist α) (f : α → β) :
    (p.map f).entropy ≤ p.entropy := by
  rw [entropy_eq_expect, map_expect, entropy_eq_expect]
  unfold expect
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : p.mass a = 0
  · simp [ha]
  · have hp : 0 < p.mass a := lt_of_le_of_ne (p.mass_nonneg a) (Ne.symm ha)
    exact mul_le_mul_of_nonneg_left
      (neg_le_neg (Real.log_le_log hp (p.mass_le_map f a))) (p.mass_nonneg a)

private theorem entropy_term_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hpos : 0 < x → 0 < y) : Real.negMulLog x ≤ y - x - x * Real.log y := by
  by_cases h : x = 0
  · simpa [h] using hy
  · have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm h)
    have hy' := hpos hx'
    have hh := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hy' hx')) hx
    rw [Real.log_div (ne_of_gt hy') (ne_of_gt hx')] at hh
    have hcancel : x * (y / x - 1) = y - x := by field_simp
    rw [hcancel] at hh
    dsimp [Real.negMulLog]
    nlinarith

theorem entropy_le_cross_entropy (p q : FinDist α)
    (hpos : ∀ a, 0 < p.mass a → 0 < q.mass a) :
    p.entropy ≤ p.expect (fun a => -Real.log (q.mass a)) := by
  have h := Finset.sum_le_sum fun a (_ : a ∈ (Finset.univ : Finset α)) =>
    entropy_term_le (p.mass a) (q.mass a) (p.mass_nonneg a) (q.mass_nonneg a) (hpos a)
  simpa [entropy, expect, Finset.sum_sub_distrib, p.mass_sum, q.mass_sum,
    Finset.sum_neg_distrib] using h

def prod (p : FinDist α) (q : FinDist β) : FinDist (α × β) where
  mass := fun x => p.mass x.1 * q.mass x.2
  mass_nonneg := fun x => mul_nonneg (p.mass_nonneg x.1) (q.mass_nonneg x.2)
  mass_sum := by
    simp [Fintype.sum_prod_type, ← Finset.mul_sum, p.mass_sum, q.mass_sum]

theorem entropy_pair_le_add (p : FinDist α) (f : α → β) (g : α → γ) :
    (p.map (fun a => (f a, g a))).entropy ≤ (p.map f).entropy + (p.map g).entropy := by
  let r := p.map (fun a => (f a, g a))
  let s := (p.map f).prod (p.map g)
  have hm1 : r.map Prod.fst = p.map f := by simp [r]
  have hm2 : r.map Prod.snd = p.map g := by simp [r]
  have hp1 (x : β × γ) (hx : 0 < r.mass x) : 0 < (p.map f).mass x.1 := by
    have h := r.mass_le_map Prod.fst x
    rw [hm1] at h
    exact hx.trans_le h
  have hp2 (x : β × γ) (hx : 0 < r.mass x) : 0 < (p.map g).mass x.2 := by
    have h := r.mass_le_map Prod.snd x
    rw [hm2] at h
    exact hx.trans_le h
  have hh := r.entropy_le_cross_entropy s (fun x hx => mul_pos (hp1 x hx) (hp2 x hx))
  have he : r.expect (fun x => -Real.log (s.mass x)) =
      r.expect (fun x => -Real.log ((p.map f).mass x.1)) +
      r.expect (fun x => -Real.log ((p.map g).mass x.2)) := by
    rw [← expect_add]
    unfold expect
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : r.mass x = 0
    · simp [hx]
    · have hr : 0 < r.mass x := lt_of_le_of_ne (r.mass_nonneg x) (Ne.symm hx)
      change r.mass x * -Real.log ((p.map f).mass x.1 * (p.map g).mass x.2) =
        r.mass x * (-Real.log ((p.map f).mass x.1) + -Real.log ((p.map g).mass x.2))
      rw [Real.log_mul (ne_of_gt (hp1 x hr)) (ne_of_gt (hp2 x hr))]
      ring
  rw [he] at hh
  have h1 : r.expect (fun x => -Real.log ((p.map f).mass x.1)) = (p.map f).entropy := by
    rw [← r.map_expect Prod.fst (fun b => -Real.log ((p.map f).mass b)), hm1,
      ← entropy_eq_expect]
  have h2 : r.expect (fun x => -Real.log ((p.map g).mass x.2)) = (p.map g).entropy := by
    rw [← r.map_expect Prod.snd (fun b => -Real.log ((p.map g).mass b)), hm2,
      ← entropy_eq_expect]
  rwa [h1, h2] at hh

theorem entropy_le_log_partition_sub_expect (p : FinDist α) (S : Finset α)
    (hsupp : ∀ a, a ∉ S → p.mass a = 0) (f : α → ℝ) :
    p.entropy ≤ Real.log (∑ a ∈ S, Real.exp (f a)) - p.expect f := by
  classical
  let Z : ℝ := ∑ a ∈ S, Real.exp (f a)
  have hS : S.Nonempty := by
    by_contra h
    have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hmass : ∀ a, p.mass a = 0 := fun a => hsupp a (by simp [hzero])
    have hh := p.mass_sum
    simp [hmass] at hh
  have hZ : 0 < Z := by
    obtain ⟨a, ha⟩ := hS
    exact Finset.sum_pos' (fun b hb => le_of_lt (Real.exp_pos (f b)))
      ⟨a, ha, Real.exp_pos (f a)⟩
  let q : FinDist α :=
    { mass := fun a => if a ∈ S then Real.exp (f a) / Z else 0
      mass_nonneg := fun a => by split_ifs <;> positivity
      mass_sum := by
        simp only [Finset.sum_ite_mem, Finset.univ_inter, div_eq_mul_inv,
          ← Finset.sum_mul]
        exact mul_inv_cancel₀ (ne_of_gt hZ) }
  have hpos (a : α) (ha : 0 < p.mass a) : a ∈ S := by
    by_contra h
    rw [hsupp a h] at ha
    exact (lt_irrefl 0 ha)
  have hh := p.entropy_le_cross_entropy q (fun a ha => by
    dsimp [q]
    rw [if_pos (hpos a ha)]
    exact div_pos (Real.exp_pos _) hZ)
  have he : p.expect (fun a => -Real.log (q.mass a)) = Real.log Z - p.expect f := by
    have hterm : p.expect (fun a => -Real.log (q.mass a)) =
        p.expect (fun a => Real.log Z - f a) := by
      unfold expect
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : p.mass a = 0
      · simp [ha]
      · have hp : 0 < p.mass a := lt_of_le_of_ne (p.mass_nonneg a) (Ne.symm ha)
        simp [q, hpos a hp, Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ),
          Real.log_exp]
    rw [hterm, expect_sub, expect_const]
  rwa [he] at hh

theorem entropy_le_log_card (p : FinDist α) :
    p.entropy ≤ Real.log (Fintype.card α : ℝ) := by
  have h := p.entropy_le_log_partition_sub_expect Finset.univ
    (fun a ha => False.elim (ha (Finset.mem_univ a))) (fun _ => 0)
  simpa using h

theorem entropy_le_log_card_support (p : FinDist α) (S : Finset α)
    (hsupp : ∀ a, a ∉ S → p.mass a = 0) :
    p.entropy ≤ Real.log (S.card : ℝ) := by
  simpa using p.entropy_le_log_partition_sub_expect S hsupp (fun _ => 0)

theorem support_nonempty (p : FinDist α) (S : Finset α)
    (hsupp : ∀ a, a ∉ S → p.mass a = 0) : S.Nonempty := by
  classical
  by_contra h
  have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hmass : ∀ a, p.mass a = 0 := fun a => hsupp a (by simp [hzero])
  have hh := p.mass_sum
  simp [hmass] at hh

theorem partition_pos_of_support (p : FinDist α) (S : Finset α)
    (hsupp : ∀ a, a ∉ S → p.mass a = 0) (f : α → ℝ) :
    0 < ∑ a ∈ S, Real.exp (f a) := by
  obtain ⟨a, ha⟩ := p.support_nonempty S hsupp
  exact Finset.sum_pos' (fun b hb => le_of_lt (Real.exp_pos (f b)))
    ⟨a, ha, Real.exp_pos (f a)⟩

/-- Gibbs' variational inequality optimized against a subgaussian partition
bound. The underlying distribution need not be uniform on its support. -/
theorem entropy_le_log_card_sub_mean_sq_of_partition_bound (p : FinDist α)
    (S : Finset α) (hsupp : ∀ a, a ∉ S → p.mass a = 0) (C : α → ℝ)
    (N K : ℝ) (hN : 0 < N) (hK : 0 < K)
    (hmgf : ∀ t : ℝ, (∑ a ∈ S, Real.exp (t * C a)) ≤ N * Real.exp (K * t^2 / 2)) :
    p.entropy ≤ Real.log N - (p.expect C)^2 / (2 * K) := by
  let D := p.expect C
  let t := D / K
  have hG := p.entropy_le_log_partition_sub_expect S hsupp (fun a => t * C a)
  rw [p.expect_const_mul] at hG
  have hlog := Real.log_le_log (p.partition_pos_of_support S hsupp (fun a => t * C a))
    (hmgf t)
  rw [Real.log_mul (ne_of_gt hN) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hh := hG.trans (sub_le_sub_right hlog (t * p.expect C))
  have he : Real.log N + K * t^2 / 2 - t * p.expect C =
      Real.log N - (p.expect C)^2 / (2 * K) := by
    dsimp [t, D]
    field_simp [ne_of_gt hK]
    ring
  rwa [he] at hh

theorem entropy_of_subsingleton (p : FinDist α) [Subsingleton α] : p.entropy = 0 := by
  obtain ⟨a⟩ := p.nonempty
  have hcard : Fintype.card α = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨a, fun b => Subsingleton.elim b a⟩
  have h := p.entropy_le_log_card
  rw [hcard] at h
  have h' : p.entropy ≤ 0 := by simpa using h
  exact le_antisymm h' p.entropy_nonneg

end FinDist
end PermEntropy
