module

public import MathAndTheory.Mathematics.Hofstadter.Counterexample

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace MathAndTheory.Hofstadter

theorem iter_succ_right {α : Type} (f : α → α) (t : Nat) (x : α) :
    iter f (t + 1) x = iter f t (f x) := by
  induction t with
  | zero => rfl
  | succ t ih => exact congrArg f ih

theorem iter_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a + b) x = iter f a (iter f b x) := by
  induction a with
  | zero => simp only [Nat.zero_add, iter]
  | succ a ih =>
    simpa only [Nat.succ_add, iter] using congrArg f ih

theorem iter_zero_value (k t : Nat) : iter (F k) t 0 = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [iter, ih, F_zero]

/-- A map whose adjacent values increase by zero or one preserves adjacent
ordered pairs throughout a bounded interval. -/
theorem bounded_step_pair (f : Nat → Nat) (N : Nat)
    (h : ∀ m, m < N → f m ≤ f (m + 1) ∧ f (m + 1) ≤ f m + 1)
    (a b : Nat) (hab : a ≤ b) (hba : b ≤ a + 1) (hb : b ≤ N) :
    f a ≤ f b ∧ f b ≤ f a + 1 := by
  by_cases heq : a = b
  · subst b; omega
  · have heq' : b = a + 1 := by omega
    subst b
    exact h a (by omega)

theorem bounded_iter_step (f : Nat → Nat) (hf : ∀ m, f m ≤ m)
    (N : Nat)
    (h : ∀ m, m < N → f m ≤ f (m + 1) ∧ f (m + 1) ≤ f m + 1)
    (t n : Nat) (hn : n + 1 ≤ N) :
    iter f t n ≤ iter f t (n + 1) ∧
      iter f t (n + 1) ≤ iter f t n + 1 := by
  induction t with
  | zero => simp only [iter]; omega
  | succ t ih =>
    exact bounded_step_pair f N h _ _ ih.1 ih.2
      (Nat.le_trans (iter_le f hf t (n + 1)) hn)

theorem F_step (k n : Nat) :
    F k n ≤ F k (n + 1) ∧ F k (n + 1) ≤ F k n + 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp only [F_zero, F_succ, iter_zero_value]; omega
    | succ n =>
      have hs := bounded_iter_step (F k) (F_le k) (n + 1)
        (fun m hm => ih m hm) k n (Nat.le_refl _)
      have hbound := iter_le (F k) (F_le k) k n
      rw [F_succ k n, F_succ k (n + 1)]
      omega

theorem F_mono (k : Nat) {a b : Nat} (h : a ≤ b) : F k a ≤ F k b := by
  induction b generalizing a with
  | zero =>
    have ha : a = 0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases hab : a ≤ b
    · exact Nat.le_trans (ih hab) (F_step k b).1
    · have ha : a = b + 1 := by omega
      subst a
      exact Nat.le_refl _

theorem iter_F_mono (k t : Nat) {a b : Nat} (h : a ≤ b) :
    iter (F k) t a ≤ iter (F k) t b := by
  induction t with
  | zero => exact h
  | succ t ih => exact F_mono k ih

theorem iter_F_step (k t n : Nat) :
    iter (F k) t n ≤ iter (F k) t (n + 1) ∧
      iter (F k) t (n + 1) ≤ iter (F k) t n + 1 :=
  bounded_iter_step (F k) (F_le k) (n + 1)
    (fun m _ => F_step k m) t n (Nat.le_refl _)

@[expose] def L (k n : Nat) : Nat := n + iter (F k) (k - 1) n

theorem L_zero (k : Nat) : L k 0 = 0 := by
  simp [L, iter_zero_value]

theorem le_L (k n : Nat) : n ≤ L k n := Nat.le_add_right _ _

theorem L_step (k n : Nat) :
    L k n + 1 ≤ L k (n + 1) ∧ L k (n + 1) ≤ L k n + 2 := by
  have h := iter_F_step k (k - 1) n
  simp only [L]
  omega

theorem iter_k_peel (k : Nat) (hk : 1 ≤ k) (n : Nat) :
    iter (F k) k n = iter (F k) (k - 1) (F k n) := by
  have heq : k = (k - 1) + 1 := by omega
  calc
    iter (F k) k n = iter (F k) ((k - 1) + 1) n :=
      congrArg (fun t => iter (F k) t n) heq
    _ = iter (F k) (k - 1) (F k n) := iter_succ_right (F k) (k - 1) n

theorem F_L_succ_of_F_L (k : Nat) (hk : 1 ≤ k) (n : Nat)
    (h : F k (L k n) = n) : F k (L k n + 1) = n + 1 := by
  rw [F_succ, iter_k_peel k hk, h]
  simp only [L]
  omega

theorem F_L (k : Nat) (hk : 1 ≤ k) (n : Nat) : F k (L k n) = n := by
  induction n with
  | zero => rw [L_zero, F_zero]
  | succ n ih =>
    have hs := F_L_succ_of_F_L k hk n ih
    have hstep := L_step k n
    by_cases heq : L k (n + 1) = L k n + 1
    · rw [heq]; exact hs
    · have heq' : L k (n + 1) = L k n + 2 := by omega
      have hr := F_succ k (L k n + 1)
      rw [iter_k_peel k hk, hs] at hr
      have hdef : L k (n + 1) = n + 1 + iter (F k) (k - 1) (n + 1) := rfl
      have harg : L k n + 1 + 1 = L k (n + 1) := by omega
      rw [harg] at hr
      omega

theorem F_L_succ (k : Nat) (hk : 1 ≤ k) (n : Nat) :
    F k (L k n + 1) = n + 1 := F_L_succ_of_F_L k hk n (F_L k hk n)

theorem F_galois (k : Nat) (hk : 1 ≤ k) (n m : Nat) :
    F k n ≤ m ↔ n ≤ L k m := by
  constructor
  · intro h
    by_cases hn : n ≤ L k m
    · exact hn
    · have harg : L k m + 1 ≤ n := by omega
      have hm := F_mono k harg
      rw [F_L_succ k hk m] at hm
      omega
  · intro h
    have hm := F_mono k h
    rw [F_L k hk m] at hm
    exact hm

theorem iter_galois (k : Nat) (hk : 1 ≤ k) (t n m : Nat) :
    iter (F k) t n ≤ m ↔ n ≤ iter (L k) t m := by
  induction t generalizing m with
  | zero => rfl
  | succ t ih =>
    change F k (iter (F k) t n) ≤ m ↔ n ≤ L k (iter (L k) t m)
    rw [F_galois k hk, ih]
    have hcomm := iter_succ_right (L k) t m
    change L k (iter (L k) t m) = iter (L k) t (L k m) at hcomm
    rw [hcomm]

theorem iter_F_iter_L (k : Nat) (hk : 1 ≤ k) (t n : Nat) :
    iter (F k) t (iter (L k) t n) = n := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [iter_succ_right (F k)]
    change iter (F k) t (F k (L k (iter (L k) t n))) = n
    rw [F_L k hk, ih]

#print axioms F_step
#print axioms F_L
#print axioms iter_galois

end MathAndTheory.Hofstadter
