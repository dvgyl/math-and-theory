import SingerC3.System

/-!
# A kernel-checked search for the 61-variable system

`go` is a depth-first search over partial assignments. A partial assignment is a pair of bit
masks `(o, z)`: the orbit indices fixed to `true` and to `false`. The search only ever takes the
following steps, each of which is checked:

* close the current node, because some line already meets at least five chosen points
  (`5 ≤ cntU o t`) or all of its points are excluded (`cntU z t = 14`);
* exclude a point `p` after checking that choosing it would close the node;
* choose a point `p` after checking that excluding it would close the node;
* exclude every free point of a line that already meets four chosen points;
* split on a point `p`.

Which step is taken, and on which line or point, is decided by `plan`, a heuristic on packed
line counts `c1, cf, cd` carried along the search. `go_sound` holds for arbitrary values of
these counts and of `plan`: they only affect the size of the search, never its soundness.
A predicate `cut` lets one search assume that other searches have already closed given nodes.
-/

namespace SingerC3

/-! ### Partial assignments -/

/-- A solution of the line conditions. -/
def Valid (x : Nat → Bool) : Prop := ∀ s < 61, 1 ≤ rowCount x s ∧ rowCount x s ≤ 4

/-- `x` extends the partial assignment `(o, z)`. -/
def Cons (x : Nat → Bool) (o z : Nat) : Prop :=
  ∀ j, (o.testBit j = true → x j = true) ∧ (z.testBit j = true → x j = false)

/-- No solution extends the partial assignment `(o, z)`. -/
def NoSol (o z : Nat) : Prop := ∀ x, Cons x o z → ¬ Valid x

/-! ### Checked line counts -/

/-- `rowCount (testBit o) t`, unrolled (`cntU_eq`). -/
def cntU (o t : Nat) : Nat :=
  ((o >>> ((1 + t) % 61)) % 2 +
    ((o >>> ((2 + t) % 61)) % 2 +
    ((o >>> ((4 + t) % 61)) % 2 +
    ((o >>> ((17 + t) % 61)) % 2 +
    ((o >>> ((24 + t) % 61)) % 2 +
    ((o >>> ((29 + t) % 61)) % 2 +
    ((o >>> ((43 + t) % 61)) % 2 +
    ((o >>> ((77 + t) % 61)) % 2 +
    ((o >>> ((83 + t) % 61)) % 2 +
    ((o >>> ((87 + t) % 61)) % 2 +
    ((o >>> ((120 + t) % 61)) % 2 +
    ((o >>> ((138 + t) % 61)) % 2 +
    ((o >>> ((155 + t) % 61)) % 2 +
    ((o >>> ((176 + t) % 61)) % 2 + 0))))))))))))))

/-- The node is closed by line `t`. -/
def closeAt (t o z : Nat) : Bool := decide (t < 61) && (decide (5 ≤ cntU o t) || cntU z t == 14)

/-- Line `t` already meets four chosen points. -/
def fillOk (t o : Nat) : Bool := decide (t < 61) && decide (4 ≤ cntU o t)

/-- The 61 orbit indices. -/
def FULL : Nat := 2 ^ 61 - 1

/-- The orbit indices `(d + t) mod 61`, `d ∈ D`, as a bit mask. -/
def rowMask (t : Nat) : Nat := D.foldr (fun d m => 2 ^ ((d + t) % 61) ||| m) 0

/-- The free orbit indices. -/
def freeM (o z : Nat) : Nat := FULL ^^^ (o ||| z)

/-! ### The search heuristic

Packed vectors have one byte per line. `c1` counts the chosen points on each line, `cf` the free
points (with multiplicity) and `cd` whether the doubled point `(t + 16) mod 61` of line `t` is
free. None of this is used by the soundness proof. -/

/-- One in every byte. -/
def R1 : Nat := 0x1010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101
/-- The top bit of every byte. -/
def HB : Nat := 0x80808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080
/-- 127 in every byte. -/
def K127 : Nat := 0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f
/-- 123 in every byte. -/
def K123 : Nat := 0x7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b
/-- All 61 bytes. -/
def FULL8 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
/-- Byte `t` counts the `d ∈ D` with `d + t ≡ 0 (mod 61)`. -/
def P0 : Nat := 0x1010001000000000000000000000002010000000001000100010000010000000100000000000000000001000000000000000000000100000000010000
/-- Byte 45, the line whose doubled point is `0`. -/
def Q0 : Nat := 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

/-- Rotate a packed vector by `p` bytes. -/
def rotF (X p : Nat) : Nat := ((X <<< (8 * p)) ||| (X >>> (8 * (61 - p)))) &&& FULL8
/-- The lines through orbit index `p`, with multiplicity. -/
def Pv (p : Nat) : Nat := rotF P0 p
/-- The line whose doubled point is `p`. -/
def Qv (p : Nat) : Nat := rotF Q0 p
/-- Bytes that are positive (bytes below 128). -/
def posF (Y : Nat) : Nat := (Y + K127) &&& HB
/-- Bytes that are zero. -/
def zeroF (Y : Nat) : Nat := HB ^^^ posF Y
/-- Bytes equal to `k`. -/
def eqF (Y k : Nat) : Nat := zeroF (Y ^^^ (k * R1))
/-- Bytes at least five. -/
def ge5F (Y : Nat) : Nat := (Y + K123) &&& HB

/-- One step of a binary search for the highest set bit. -/
def lgStep (m acc k : Nat) (cont : Nat → Nat → Nat) : Nat :=
  if m >>> k != 0 then cont (m >>> k) (acc + k) else cont m acc

/-- The highest set bit of a number below `2 ^ 64`. -/
def lg (m : Nat) : Nat :=
  lgStep m 0 32 fun m a => lgStep m a 16 fun m a => lgStep m a 8 fun m a =>
  lgStep m a 4 fun m a => lgStep m a 2 fun m a => lgStep m a 1 fun _ a => a

/-- The line of the highest set top bit of a packed vector. -/
def rowOf (m : Nat) : Nat :=
  lgStep m 0 256 fun m a => lgStep m a 128 fun m a => lgStep m a 64 fun m a =>
  lgStep m a 32 fun m a => lgStep m a 16 fun m a => lgStep m a 8 fun _ a => a / 8

/-- `rowMask t`, computed by a rotation. -/
def rowMaskH (t : Nat) : Nat :=
  ((0x840080225430016 <<< t) ||| (0x840080225430016 >>> (61 - t))) &&& 0x1fffffffffffffff

/-- `∑ g j` over the set bits `j` of `m` (at most `n` of them). -/
def sumBits : Nat → Nat → (Nat → Nat) → Nat
  | 0, _, _ => 0
  | n + 1, m, g => if m == 0 then 0 else g (lg m) + sumBits n (m ^^^ 2 ^ lg m) g

/-- The first line with no chosen point and exactly `k`, `k + 1`, … free points. -/
def branchRows (z0 dist : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k => if z0 &&& eqF dist k != 0 then z0 &&& eqF dist k else branchRows z0 dist n (k + 1)

/-- A search step. -/
inductive Act where
  | close (t : Nat)
  | zero (t p : Nat)
  | one (t p : Nat)
  | fill (t : Nat)
  | split (p : Nat)
  | stop

/-- The heuristic choice of the next step. -/
def plan (o z c1 cf cd : Nat) : Act :=
  if ge5F c1 ||| zeroF (c1 + cf) != 0 then .close (rowOf (ge5F c1 ||| zeroF (c1 + cf)))
  else if eqF c1 4 &&& posF cf != 0 then .fill (rowOf (eqF c1 4 &&& posF cf))
  else if eqF c1 3 &&& posF cd != 0 then
    .zero (rowOf (eqF c1 3 &&& posF cd)) ((rowOf (eqF c1 3 &&& posF cd) + 16) % 61)
  else if zeroF c1 &&& eqF (cf - cd) 1 != 0 then
    .one (rowOf (zeroF c1 &&& eqF (cf - cd) 1))
      (lg (rowMaskH (rowOf (zeroF c1 &&& eqF (cf - cd) 1)) &&& freeM o z))
  else if branchRows (zeroF c1) (cf - cd) 12 2 == 0 then .stop
  else .split (lg (rowMaskH (rowOf (branchRows (zeroF c1) (cf - cd) 12 2)) &&& freeM o z))

/-- Carry out a search step; `rec` continues the search. -/
def runAct (rec : Nat → Nat → Nat → Nat → Nat → Bool) (o z c1 cf cd : Nat) : Act → Bool
  | .close t => closeAt t o z
  | .zero t p => closeAt t (o ||| 2 ^ p) z && rec o (z ||| 2 ^ p) c1 (cf - Pv p) (cd - Qv p)
  | .one t p => closeAt t o (z ||| 2 ^ p) && rec (o ||| 2 ^ p) z (c1 + Pv p) (cf - Pv p) (cd - Qv p)
  | .fill t =>
    fillOk t o && rec o (z ||| (rowMask t &&& freeM o z)) c1
      (cf - sumBits 16 (rowMask t &&& freeM o z) Pv) (cd - sumBits 16 (rowMask t &&& freeM o z) Qv)
  | .split p =>
    rec (o ||| 2 ^ p) z (c1 + Pv p) (cf - Pv p) (cd - Qv p) &&
      rec o (z ||| 2 ^ p) c1 (cf - Pv p) (cd - Qv p)
  | .stop => false

/-- One search node. -/
def node (rec : Nat → Nat → Nat → Nat → Nat → Bool) (o z c1 cf cd : Nat) : Bool :=
  runAct rec o z c1 cf cd (plan o z c1 cf cd)

/-- The search. It returns `true` only if every extension of `(o, z)` violates a line condition,
or reaches a node accepted by `cut`. -/
def go (cut : Nat → Nat → Bool) : Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _, _, _ => false
  | f + 1, o, z, c1, cf, cd => cut o z || node (go cut f) o z c1 cf cd

/-- The search from `(o, z)` with freshly computed packed counts. -/
def searchCut (cut : Nat → Nat → Bool) (o z : Nat) : Bool :=
  go cut 128 o z (sumBits 64 o Pv) (sumBits 64 (freeM o z) Pv) (sumBits 64 (freeM o z) Qv)

/-- The search from `(o, z)` with no cut. -/
def search (o z : Nat) : Bool := searchCut (fun _ _ => false) o z

/-- No solution extends any of the listed partial assignments. -/
def AllNoSol : List (Nat × Nat) → Prop
  | [] => True
  | p :: l => NoSol p.1 p.2 ∧ AllNoSol l

/-! ### Soundness -/

theorem filter_length_le {l : List Nat} {p q : Nat → Bool} (h : ∀ a, p a = true → q a = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons]
    by_cases hp : p a = true
    · simp [hp, h a hp, ih]
    · cases hq : q a <;> simp [hp] <;> omega

theorem filter_length_lt {l : List Nat} {p q : Nat → Bool} (h : ∀ a, p a = true → q a = true)
    {b : Nat} (hb : b ∈ l) (hqb : q b = true) (hpb : p b = false) :
    (l.filter p).length + 1 ≤ (l.filter q).length := by
  induction l with
  | nil => simp at hb
  | cons a l ih =>
    simp only [List.filter_cons]
    rcases List.mem_cons.1 hb with rfl | hb
    · simp only [hpb, hqb, ite_true, List.length_cons, Bool.false_eq_true, ite_false]
      exact Nat.succ_le_succ (filter_length_le h)
    · have := ih hb
      by_cases hp : p a = true
      · simp [hp, h a hp]; omega
      · cases hq : q a <;> simp [hp] <;> omega

theorem filter_length_disj {l : List Nat} {p q : Nat → Bool}
    (h : ∀ a, p a = true → q a = false) :
    (l.filter p).length + (l.filter q).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons, List.length_cons]
    by_cases hp : p a = true
    · simp [hp, h a hp]; omega
    · cases hq : q a <;> simp [hp] <;> omega

theorem cntU_eq (o t : Nat) : cntU o t = rowCount (fun j => o.testBit j) t := by
  have key : ∀ l : List Nat, (l.filter fun d => o.testBit ((d + t) % 61)).length =
      (l.map fun d => (o >>> ((d + t) % 61)) % 2).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.filter_cons, List.map_cons, List.sum_cons, ← ih, Nat.shiftRight_eq_div_pow,
        ← Nat.toNat_testBit]
      cases o.testBit ((a + t) % 61) <;> simp [Nat.add_comm]
  rw [rowCount, key]
  simp only [cntU, D, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

theorem cons_one {x : Nat → Bool} {o z p : Nat} (h : Cons x o z) (hp : x p = true) :
    Cons x (o ||| 2 ^ p) z := by
  intro j
  refine ⟨fun hj => ?_, (h j).2⟩
  rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hj
  rcases hj with hj | rfl
  · exact (h j).1 hj
  · exact hp

theorem cons_zeros {x : Nat → Bool} {o z m : Nat} (h : Cons x o z)
    (hm : ∀ j, m.testBit j = true → x j = false) : Cons x o (z ||| m) := by
  intro j
  refine ⟨(h j).1, fun hj => ?_⟩
  rw [Nat.testBit_or, Bool.or_eq_true] at hj
  rcases hj with hj | hj
  · exact (h j).2 hj
  · exact hm j hj

theorem cons_zero {x : Nat → Bool} {o z p : Nat} (h : Cons x o z) (hp : x p = false) :
    Cons x o (z ||| 2 ^ p) :=
  cons_zeros h fun j hj => by
    rw [Nat.testBit_two_pow, decide_eq_true_eq] at hj
    exact hj ▸ hp

theorem D_length : D.length = 14 := rfl

theorem closeAt_sound {x : Nat → Bool} {t o z : Nat} (hc : closeAt t o z = true) (h : Cons x o z) :
    ¬ Valid x := by
  intro hv
  simp only [closeAt, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨ht, hc⟩ := hc
  have hrow := hv t ht
  rcases hc with hc | hc
  · rw [cntU_eq] at hc
    have : rowCount (fun j => o.testBit j) t ≤ rowCount x t :=
      filter_length_le fun d hd => (h _).1 hd
    omega
  · rw [cntU_eq] at hc
    have : rowCount (fun j => z.testBit j) t + rowCount x t ≤ D.length :=
      filter_length_disj fun d hd => by
        have := (h ((d + t) % 61)).2 hd
        simpa using this
    rw [D_length] at this
    omega

theorem rowMask_mem {t j : Nat} (hj : (rowMask t).testBit j = true) :
    ∃ d ∈ D, (d + t) % 61 = j := by
  have key : ∀ l : List Nat, (l.foldr (fun d m => 2 ^ ((d + t) % 61) ||| m) 0).testBit j = true →
      ∃ d ∈ l, (d + t) % 61 = j := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro h
      rw [List.foldr_cons, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
        decide_eq_true_eq] at h
      rcases h with h | h
      · exact ⟨a, List.mem_cons_self, h⟩
      · obtain ⟨d, hd, e⟩ := ih h
        exact ⟨d, List.mem_cons_of_mem _ hd, e⟩
  exact key D hj

theorem fill_sound {x : Nat → Bool} {t o z : Nat} (hf : fillOk t o = true) (h : Cons x o z)
    (hv : Valid x) : ∀ j, (rowMask t &&& freeM o z).testBit j = true → x j = false := by
  intro j hj
  simp only [fillOk, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨ht, h4⟩ := hf
  rw [Nat.testBit_and, Bool.and_eq_true] at hj
  obtain ⟨d, hd, rfl⟩ := rowMask_mem hj.1
  have hfree := hj.2
  rw [freeM, Nat.testBit_xor, FULL, Nat.testBit_two_pow_sub_one, Nat.testBit_or] at hfree
  have hlt : (d + t) % 61 < 61 := Nat.mod_lt _ (by decide)
  have ho : o.testBit ((d + t) % 61) = false := by
    revert hfree; cases o.testBit ((d + t) % 61) <;> simp [hlt]
  cases hx' : x ((d + t) % 61)
  · rfl
  have hlt' : rowCount (fun j => o.testBit j) t + 1 ≤ rowCount x t :=
    filter_length_lt (fun a ha => (h _).1 ha) hd hx' ho
  rw [cntU_eq] at h4
  have := (hv t ht).2
  omega

theorem runAct_sound {rec : Nat → Nat → Nat → Nat → Nat → Bool}
    (hrec : ∀ o z c1 cf cd, rec o z c1 cf cd = true → NoSol o z) {o z c1 cf cd : Nat} :
    ∀ a, runAct rec o z c1 cf cd a = true → NoSol o z := by
  intro a h x hx hv
  cases a with
  | close t => exact closeAt_sound h hx hv
  | zero t p =>
    rw [runAct, Bool.and_eq_true] at h
    cases hp : x p
    · exact hrec _ _ _ _ _ h.2 x (cons_zero hx hp) hv
    · exact closeAt_sound h.1 (cons_one hx hp) hv
  | one t p =>
    rw [runAct, Bool.and_eq_true] at h
    cases hp : x p
    · exact closeAt_sound h.1 (cons_zero hx hp) hv
    · exact hrec _ _ _ _ _ h.2 x (cons_one hx hp) hv
  | fill t =>
    rw [runAct, Bool.and_eq_true] at h
    exact hrec _ _ _ _ _ h.2 x (cons_zeros hx (fill_sound h.1 hx hv)) hv
  | split p =>
    rw [runAct, Bool.and_eq_true] at h
    cases hp : x p
    · exact hrec _ _ _ _ _ h.2 x (cons_zero hx hp) hv
    · exact hrec _ _ _ _ _ h.1 x (cons_one hx hp) hv
  | stop => exact absurd h Bool.false_ne_true

theorem go_sound (cut : Nat → Nat → Bool) (hcut : ∀ o z, cut o z = true → NoSol o z) :
    ∀ f o z c1 cf cd, go cut f o z c1 cf cd = true → NoSol o z := by
  intro f
  induction f with
  | zero => intro o z c1 cf cd h; exact absurd h Bool.false_ne_true
  | succ f ih =>
    intro o z c1 cf cd h
    have h' : (cut o z || node (go cut f) o z c1 cf cd) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact hcut o z h'
    · exact runAct_sound ih _ h'

theorem search_sound {o z : Nat} (h : search o z = true) : NoSol o z :=
  go_sound _ (fun _ _ h => absurd h Bool.false_ne_true) _ _ _ _ _ _ h

theorem AllNoSol.mem : ∀ {l : List (Nat × Nat)}, AllNoSol l → ∀ p ∈ l, NoSol p.1 p.2
  | [], _, _, hp => absurd hp List.not_mem_nil
  | _ :: _, h, _, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h.1
    · exact AllNoSol.mem h.2 _ hp

theorem AllNoSol.append {l m : List (Nat × Nat)} (hl : AllNoSol l) (hm : AllNoSol m) :
    AllNoSol (l ++ m) := by
  induction l with
  | nil => exact hm
  | cons p l ih => exact ⟨hl.1, ih hl.2⟩

theorem searchCut_sound {l : List (Nat × Nat)} (hl : AllNoSol l) {o z : Nat}
    (h : searchCut (fun o z => l.contains (o, z)) o z = true) : NoSol o z :=
  go_sound _ (fun o z hc => AllNoSol.mem hl (o, z) (List.contains_iff_mem.1 hc)) _ _ _ _ _ _ h

/-- No solution of the 61-variable system exists if no solution extends `(1, 0)`. -/
theorem not_systemSolvable_of_noSol (h : NoSol 1 0) : ¬ SystemSolvable := by
  rintro ⟨x, hx0, hx⟩
  refine h x (fun j => ⟨fun hj => ?_, fun hj => ?_⟩) hx
  · have : j = 0 := by
      cases j with
      | zero => rfl
      | succ j =>
        rw [Nat.testBit_succ] at hj
        exact absurd hj (by simp)
    exact this ▸ hx0
  · exact absurd hj (by simp)

end SingerC3
