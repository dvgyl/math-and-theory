module

public import MathAndTheory.Mathematics.Hofstadter.Foundation

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace MathAndTheory.Hofstadter.Family

open MathAndTheory.Hofstadter

theorem iter_compose {α : Type} (f : α → α) (r s : Nat) (x : α) :
    iter f (r + s) x = iter f r (iter f s x) := by
  induction r with
  | zero => simp [iter]
  | succ r ih =>
    rw [Nat.succ_add]
    simp only [iter]
    exact congrArg f ih

theorem iter_right {α : Type} (f : α → α) (r : Nat) (x : α) :
    iter f (r + 1) x = iter f r (f x) := by
  simpa only [iter] using iter_compose f r 1 x

@[expose] def prefixSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSum f n + f n

theorem prefixSum_congr (a b : Nat → Nat) (n : Nat)
    (h : ∀ i, i < n → a i = b i) : prefixSum a n = prefixSum b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prefixSum]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem recurrence_sum (a : Nat → Nat) (k : Nat) (hk : 1 ≤ k)
    (ha : ∀ t, a (t + k) = a (t + k - 1) + a t) (s : Nat) :
    a (k + s) = a (k - 1) + prefixSum a (s + 1) := by
  induction s with
  | zero =>
    simpa [prefixSum] using ha 0
  | succ s ih =>
    have ht := ha (s + 1)
    have he1 : s + 1 + k = k + (s + 1) := by omega
    have he2 : k + (s + 1) - 1 = k + s := by omega
    rw [he1, he2, ih] at ht
    simpa [prefixSum, Nat.add_assoc] using ht

/-- An elementary comparison of two nearby additive recurrences. -/
theorem recurrence_gap (a b : Nat → Nat) (k : Nat) (hk : 4 ≤ k)
    (ha : ∀ t, a (t + k) = a (t + k - 1) + a t)
    (hb : ∀ t, b (t + (k + 1)) = b (t + (k + 1) - 1) + b t)
    (hab : ∀ t, t < k → a t = b t)
    (ha0 : a 0 = k + 3) (ha1 : a 1 = k + 6)
    (hbk : b k = a (k - 1) + (k + 2)) :
    b (2 * k + 2) = a (2 * k + 1) + (k - 3) := by
  have hs := prefixSum_congr a b k hab
  have ea := recurrence_sum a k (by omega) ha (k + 1)
  have eb := recurrence_sum b (k + 1) (by omega) hb (k + 1)
  have ea0 := ha 0
  have ea1 := ha 1
  have eb0 := hb 0
  have hab0 := hab 0 (by omega)
  have e1 : k + (k + 1) = 2 * k + 1 := by omega
  have e2 : (k + 1) + (k + 1) = 2 * k + 2 := by omega
  rw [e1] at ea
  rw [e2] at eb
  simp only [prefixSum] at ea eb
  simp only [Nat.zero_add, Nat.add_sub_cancel] at ea0 eb0
  have e3 : 1 + k = k + 1 := by omega
  have e4 : k + 1 - 1 = k := by omega
  rw [e3, e4] at ea1
  have e5 : k + 1 - 1 = k := by omega
  rw [e5] at eb
  omega

@[expose] def decrement (n : Nat) : Nat := if n = 0 then 0 else n - 2 + 1

theorem iter_decrement (t n : Nat) :
    iter decrement t (n + 1) = n - t + 1 := by
  induction t with
  | zero => simp [iter]
  | succ t ih =>
    simp only [iter, ih, decrement]
    have h : n - t + 1 ≠ 0 := by omega
    simp only [h, ↓reduceIte]
    omega

theorem iter_zero (k t : Nat) : iter (F k) t 0 = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [iter, ih, F_zero]

theorem F_initial (k n : Nat) (hn : n ≤ k + 2) : F k n = decrement n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [F_zero, decrement]
    | succ n =>
      rw [F_succ]
      cases n with
      | zero => simp [iter_zero, decrement]
      | succ m =>
        have he : iter (F k) k (m + 1) = iter decrement k (m + 1) := by
          apply iter_congr_bounded (F k) decrement (F_le k)
          intro i hi
          exact ih i (by omega) (by omega)
        rw [he, iter_decrement]
        simp only [decrement]
        have hne : m + 1 + 1 ≠ 0 := by omega
        simp only [hne, ↓reduceIte]
        omega

theorem F_boundary (k : Nat) : F k (k + 3) = k + 1 := by
  have he : iter (F k) k (k + 2) = iter decrement k (k + 2) := by
    apply iter_congr_bounded (F k) decrement (F_le k)
    intro i hi
    exact F_initial k i hi
  have hs := F_succ k (k + 2)
  rw [he] at hs
  have hd := iter_decrement k (k + 1)
  have harg : k + 1 + 1 = k + 2 := by omega
  rw [harg] at hd
  rw [hd] at hs
  have harg2 : k + 2 + 1 = k + 3 := by omega
  rw [harg2] at hs
  omega

theorem iter_F_initial (k n r : Nat) (hn : n ≤ k + 2)
    (hn1 : 1 ≤ n) (hr : r < n) :
    iter (F k) r n = n - r := by
  have he : iter (F k) r n = iter decrement r n := by
    apply iter_congr_bounded (F k) decrement (F_le k)
    intro i hi
    exact F_initial k i (by omega)
  have hd := iter_decrement r (n - 1)
  have hn' : n - 1 + 1 = n := by omega
  rw [hn'] at hd
  omega

theorem iter_F_boundary (k r : Nat) (hr1 : 1 ≤ r) (hr : r ≤ k + 1) :
    iter (F k) r (k + 3) = k + 2 - r := by
  have hr' : r = (r - 1) + 1 := by omega
  rw [hr', iter_right, F_boundary]
  have hi := iter_F_initial k (k + 1) (r - 1) (by omega) (by omega) (by omega)
  rw [hi]
  omega

theorem iter_F_L_cancel (k : Nat) (hk : 1 ≤ k) (r s n : Nat)
    (hrs : s ≤ r) :
    iter (F k) r (iter (L k) s n) = iter (F k) (r - s) n := by
  calc
    iter (F k) r (iter (L k) s n) =
        iter (F k) (r - s) (iter (F k) s (iter (L k) s n)) := by
      rw [← iter_compose]
      have he : r - s + s = r := by omega
      rw [he]
    _ = iter (F k) (r - s) n := by rw [iter_F_iter_L k hk]

theorem L_initial_step (k : Nat) (hk : 1 ≤ k) (n t : Nat)
    (ht : t ≤ k - 1) :
    iter (L k) (t + 1) n =
      iter (L k) t n + iter (F k) (k - 1 - t) n := by
  change iter (L k) t n + iter (F k) (k - 1) (iter (L k) t n) = _
  rw [iter_F_L_cancel k hk (k - 1) t n ht]

theorem L_orbit_recurrence (k : Nat) (hk : 1 ≤ k) (n t : Nat) :
    iter (L k) (t + k) n =
      iter (L k) (t + k - 1) n + iter (L k) t n := by
  have he : t + k = (k - 1 + 1) + t := by omega
  calc
    iter (L k) (t + k) n = L k (iter (L k) (k - 1) (iter (L k) t n)) := by
      rw [he, iter_compose]
      rfl
    _ = iter (L k) (k - 1) (iter (L k) t n) + iter (L k) t n := by
      simp only [L]
      rw [iter_F_iter_L k hk]
    _ = iter (L k) (t + k - 1) n + iter (L k) t n := by
      rw [← iter_compose]
      have he' : k - 1 + t = t + k - 1 := by omega
      rw [he']

theorem left_initial_step (k : Nat) (hk : 4 ≤ k) (t : Nat)
    (ht : t < k - 1) :
    iter (L k) (t + 1) (k + 3) = iter (L k) t (k + 3) + (t + 3) := by
  have hs := L_initial_step k (by omega) (k + 3) t (by omega)
  have hi := iter_F_boundary k (k - 1 - t) (by omega) (by omega)
  rw [hi] at hs
  have he : k + 2 - (k - 1 - t) = t + 3 := by omega
  rw [he] at hs
  exact hs

theorem right_initial_step (k : Nat) (hk : 4 ≤ k) (t : Nat)
    (ht : t < k) :
    iter (L (k + 1)) (t + 1) (k + 3) =
      iter (L (k + 1)) t (k + 3) + (t + 3) := by
  have hs := L_initial_step (k + 1) (by omega) (k + 3) t (by omega)
  have hi := iter_F_initial (k + 1) (k + 3) (k + 1 - 1 - t)
    (by omega) (by omega) (by omega)
  rw [hi] at hs
  have he : k + 3 - (k + 1 - 1 - t) = t + 3 := by omega
  rw [he] at hs
  exact hs

theorem initial_orbits_equal (k : Nat) (hk : 4 ≤ k) (t : Nat) :
    t < k → iter (L k) t (k + 3) = iter (L (k + 1)) t (k + 3) := by
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    rw [left_initial_step k hk t (by omega),
      right_initial_step k hk t (by omega), ih (by omega)]

/-- The exact positive gap between the two inverse iterates that produces
the general counterexample family. -/
theorem inverse_iterate_gap (k : Nat) (hk : 4 ≤ k) :
    iter (L (k + 1)) (2 * k + 2) (k + 3) =
      iter (L k) (2 * k + 1) (k + 3) + (k - 3) := by
  apply recurrence_gap
    (fun t => iter (L k) t (k + 3))
    (fun t => iter (L (k + 1)) t (k + 3)) k hk
  · intro t
    exact L_orbit_recurrence k (by omega) (k + 3) t
  · intro t
    exact L_orbit_recurrence (k + 1) (by omega) (k + 3) t
  · exact initial_orbits_equal k hk
  · rfl
  · have hs := left_initial_step k hk 0 (by omega)
    simp only [iter] at hs
    simp only [iter]
    omega
  · have hs := right_initial_step k hk (k - 1) (by omega)
    have he : k - 1 + 1 = k := by omega
    rw [he, ← initial_orbits_equal k hk (k - 1) (by omega)] at hs
    have he' : k - 1 + 3 = k + 2 := by omega
    rw [he'] at hs
    exact hs

@[expose] def familyWitness (k : Nat) : Nat := iter (L (k + 1)) (2 * k + 2) (k + 3)

/-- Every parameter k ≥ 4 supplies a counterexample to the conjectured
comparison, already at the first allowed iteration index 2k+1. -/
theorem general_counterexample (k : Nat) (hk : 4 ≤ k) :
    iter (F (k + 1)) (2 * k + 2) (familyWitness k) <
      iter (F k) (2 * k + 1) (familyWitness k) := by
  have hright : iter (F (k + 1)) (2 * k + 2) (familyWitness k) = k + 3 := by
    exact iter_F_iter_L (k + 1) (by omega) (2 * k + 2) (k + 3)
  have hgap := inverse_iterate_gap k hk
  have hleft : ¬ iter (F k) (2 * k + 1) (familyWitness k) ≤ k + 3 := by
    intro h
    have hg := (iter_galois k (by omega) (2 * k + 1) (familyWitness k) (k + 3)).mp h
    unfold familyWitness at hg
    omega
  omega

theorem infinitely_many_parameter_counterexamples :
    ∀ k : Nat, 4 ≤ k → ∃ n : Nat,
      iter (F (k + 1)) (2 * k + 2) n < iter (F k) (2 * k + 1) n := by
  intro k hk
  exact ⟨familyWitness k, general_counterexample k hk⟩

#print axioms inverse_iterate_gap
#print axioms general_counterexample
#print axioms infinitely_many_parameter_counterexamples

end MathAndTheory.Hofstadter.Family
