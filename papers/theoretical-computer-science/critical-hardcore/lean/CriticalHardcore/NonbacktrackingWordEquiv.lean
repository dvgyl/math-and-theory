import CriticalHardcore.NonbacktrackingChoices

/-! The finite-alphabet parametrization is bijective, including for self-avoiding paths. -/

set_option autoImplicit false

namespace CriticalHardcore.NBChoices

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d : ℕ} (regular : G.IsRegularOfDegree (d + 1))

def pathEdge {length : ℕ} (p : NBPath G length) (i : ℕ) (hi : i < length) : G.Dart :=
  ⟨(p.vertex G i, p.vertex G (i + 1)), (p.isNB G).1 i hi⟩

noncomputable def encode {n : ℕ} (p : NBPath G (n + 1)) (i : Fin n) : Fin d :=
  (nextEquiv G regular (pathEdge G p i.val (by omega))).symm
    ⟨p.vertex G (i.val + 2), (p.isNB G).1 (i.val + 1) (by omega),
      ((p.isNB G).2 i.val (by omega)).symm⟩

theorem encode_step_snd {n : ℕ} (p : NBPath G (n + 1)) (i : Fin n) :
    (step G regular (pathEdge G p i.val (by omega)) (encode G regular p i)).snd =
      p.vertex G (i.val + 2) := by
  simp only [step, encode, Equiv.apply_symm_apply]

theorem state_encode [NeZero d] (e : G.Dart) {n : ℕ} (p : NBPath G (n + 1))
    (h0 : p.vertex G 0 = e.fst) (h1 : p.vertex G 1 = e.snd) {k : ℕ} (hk : k ≤ n) :
    state G regular e (wordAt (encode G regular p)) k = pathEdge G p k (by omega) := by
  induction k with
  | zero =>
    apply SimpleGraph.Dart.ext
    exact Prod.ext h0.symm h1.symm
  | succ k ih =>
    rw [state_succ, ih (by omega)]
    have hk' : k < n := by omega
    have hw : wordAt (encode G regular p) k = encode G regular p ⟨k, hk'⟩ :=
      wordAt_fin _ ⟨k, hk'⟩
    rw [hw]
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · rfl
    · exact encode_step_snd G regular p ⟨k, hk'⟩

theorem path_encode [NeZero d] (e : G.Dart) {n : ℕ} (p : NBPath G (n + 1))
    (h0 : p.vertex G 0 = e.fst) (h1 : p.vertex G 1 = e.snd) :
    path G regular e (encode G regular p) = p := by
  apply NBPath.ext
  intro i hi
  rw [path_vertex G regular e _ hi]
  cases i with
  | zero => exact h0.symm
  | succ k =>
    rw [vertex_succ, state_encode G regular e p h0 h1 (by omega)]
    rfl

theorem pathEdge_path [NeZero d] (e : G.Dart) {n : ℕ} (word : Fin n → Fin d)
    {i : ℕ} (hi : i ≤ n) :
    pathEdge G (path G regular e word) i (by omega) =
      state G regular e (wordAt word) i := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · change (path G regular e word).vertex G i = _
    rw [path_vertex G regular e word (by omega), state_fst]
  · change (path G regular e word).vertex G (i + 1) = _
    rw [path_vertex G regular e word (by omega)]
    rfl

theorem encode_path [NeZero d] (e : G.Dart) {n : ℕ} (word : Fin n → Fin d) :
    encode G regular (path G regular e word) = word := by
  funext i
  apply step_snd_injective G regular (pathEdge G (path G regular e word) i.val (by omega))
  dsimp only
  rw [encode_step_snd]
  rw [pathEdge_path G regular e word (by omega)]
  rw [path_vertex G regular e word (by omega)]
  change (step G regular (state G regular e (wordAt word) i.val)
      (wordAt word i.val)).snd = _
  rw [wordAt_fin]

theorem path_injective [NeZero d] (e : G.Dart) (n : ℕ) :
    Function.Injective (path G regular e : (Fin n → Fin d) → NBPath G (n + 1)) := by
  intro a b h
  have h' := congrArg (encode G regular) h
  simpa only [encode_path] using h'

def EdgePath (e : G.Dart) (n : ℕ) :=
  {p : NBPath G (n + 1) // p.vertex G 0 = e.fst ∧ p.vertex G 1 = e.snd}

noncomputable instance (e : G.Dart) (n : ℕ) : Fintype (EdgePath G e n) := by
  classical
  unfold EdgePath
  infer_instance

noncomputable def wordEquiv [NeZero d] (e : G.Dart) (n : ℕ) :
    (Fin n → Fin d) ≃ EdgePath G e n where
  toFun word := ⟨path G regular e word, by
    constructor
    · rw [path_vertex G regular e word (by omega)]; rfl
    · rw [path_vertex G regular e word (by omega)]; rfl⟩
  invFun p := encode G regular p.val
  left_inv := encode_path G regular e
  right_inv p := Subtype.ext (path_encode G regular e p.val p.property.1 p.property.2)

include regular in
theorem card_edgePath [NeZero d] (e : G.Dart) (n : ℕ) :
    Fintype.card (EdgePath G e n) = d ^ n := by
  rw [← Fintype.card_congr (wordEquiv G regular e n)]
  simp

noncomputable def aliveWordEquiv [NeZero d] (e : G.Dart) (n : ℕ) :
    {word : Fin n → Fin d // Function.Injective (path G regular e word).val} ≃
      OrientedPath G e.fst e.snd n where
  toFun word := ⟨path G regular e word.val,
    (wordEquiv G regular e n word.val).property.1,
    (wordEquiv G regular e n word.val).property.2, word.property⟩
  invFun p := ⟨encode G regular p.val, by
    rw [path_encode G regular e p.val p.property.1 p.property.2.1]
    exact p.property.2.2⟩
  left_inv word := Subtype.ext (encode_path G regular e word.val)
  right_inv p := Subtype.ext (path_encode G regular e p.val p.property.1 p.property.2.1)

theorem orientedCount_eq_aliveWords [NeZero d] (e : G.Dart) (n : ℕ) :
    orientedCount G e.fst e.snd n =
      Fintype.card {word : Fin n → Fin d // Function.Injective (path G regular e word).val} := by
  classical
  exact (Fintype.card_congr (aliveWordEquiv G regular e n)).symm

include regular in
theorem orientedCount_le [NeZero d] (e : G.Dart) (n : ℕ) :
    orientedCount G e.fst e.snd n ≤ d ^ n := by
  classical
  rw [orientedCount_eq_aliveWords G regular e n]
  calc
    _ ≤ Fintype.card (Fin n → Fin d) := Fintype.card_subtype_le _
    _ = d ^ n := by simp

/-- Exact oriented-edge survival probability after `n` further steps. -/
noncomputable def survival [NeZero d] (e : G.Dart) (n : ℕ) : ℝ :=
  (orientedCount G e.fst e.snd n : ℝ) / (d : ℝ) ^ n

/-- The same exact graph walk, using a finite list of choice letters. -/
noncomputable def wordPath [NeZero d] (e : G.Dart) (w : List (Fin d)) :
    NBPath G (w.length + 1) := path G regular e w.get

def AliveWord [NeZero d] (e : G.Dart) (w : List (Fin d)) : Prop :=
  Function.Injective (wordPath G regular e w).val

noncomputable def GoodAtWord [NeZero d] (e : G.Dart) (w : List (Fin d)) (h : ℕ) : Prop :=
  d ^ h ≤ 2 * Fintype.card
    (FrontierAt G (wordPath G regular e w).val (h + 1) (Fin.last w.length))

theorem wordAt_get_of_prefix [NeZero d] {a b : List (Fin d)} (hp : a <+: b)
    {i : ℕ} (hi : i < a.length) : wordAt a.get i = wordAt b.get i := by
  have hib : i < b.length := lt_of_lt_of_le hi hp.length_le
  simp only [wordAt, dif_pos hi, dif_pos hib, List.get_eq_getElem]
  exact hp.getElem hi

theorem wordPath_vertex_of_prefix [NeZero d] (e : G.Dart)
    {a b : List (Fin d)} (hp : a <+: b) {i : ℕ} (hi : i ≤ a.length + 1) :
    (wordPath G regular e a).vertex G i = (wordPath G regular e b).vertex G i := by
  rw [wordPath, wordPath, path_vertex G regular e _ hi,
    path_vertex G regular e _ (by have := hp.length_le; omega)]
  exact vertex_congr G regular e _ _ (fun j hj =>
    wordAt_get_of_prefix hp (by omega))

theorem aliveWord_of_prefix [NeZero d] (e : G.Dart)
    {a b : List (Fin d)} (hp : a <+: b) (hb : AliveWord G regular e b) :
    AliveWord G regular e a := by
  intro i j hij
  have hle := hp.length_le
  let i' : Fin (b.length + 1 + 1) := ⟨i.val, by omega⟩
  let j' : Fin (b.length + 1 + 1) := ⟨j.val, by omega⟩
  have heq : (wordPath G regular e b).val i' = (wordPath G regular e b).val j' := by
    rw [← pathAt_fin (wordPath G regular e b).val i',
      ← pathAt_fin (wordPath G regular e b).val j']
    change (wordPath G regular e b).vertex G i.val =
      (wordPath G regular e b).vertex G j.val
    rw [← wordPath_vertex_of_prefix G regular e hp (by omega),
      ← wordPath_vertex_of_prefix G regular e hp (by omega)]
    simpa only [NBPath.vertex, pathAt_fin] using hij
  have hh := hb heq
  exact Fin.ext (congrArg (fun x : Fin (b.length + 1 + 1) => x.val) hh)

theorem deadWord_append [NeZero d] (e : G.Dart) (a b : List (Fin d))
    (ha : ¬ AliveWord G regular e a) : ¬ AliveWord G regular e (a ++ b) := by
  intro hab
  exact ha (aliveWord_of_prefix G regular e (List.prefix_append a b) hab)

theorem pastAt_wordPrefix [NeZero d] (e : G.Dart) {a b : List (Fin d)}
    (hp : a <+: b) :
    pastAt (wordPath G regular e a).val (Fin.last a.length) =
      pastAt (wordPath G regular e b).val ⟨a.length, by have := hp.length_le; omega⟩ := by
  ext v
  constructor
  · rintro ⟨j, hj, hv⟩
    change j.val ≤ a.length + 1 at hj
    let j' : Fin (b.length + 1 + 1) := ⟨j.val, by have := hp.length_le; omega⟩
    refine ⟨j', hj, ?_⟩
    have hsame := wordPath_vertex_of_prefix G regular e hp (i := j.val) (by omega)
    have hsame' : (wordPath G regular e a).val j = (wordPath G regular e b).val j' := by
      change pathAt (wordPath G regular e a).val j.val =
        pathAt (wordPath G regular e b).val j.val at hsame
      rw [pathAt_eq _ (by omega), pathAt_eq _ (by have := hp.length_le; omega)] at hsame
      exact hsame
    exact hsame'.symm.trans hv
  · rintro ⟨j, hj, hv⟩
    change j.val ≤ a.length + 1 at hj
    let j' : Fin (a.length + 1 + 1) := ⟨j.val, by omega⟩
    refine ⟨j', hj, ?_⟩
    have hsame := wordPath_vertex_of_prefix G regular e hp (i := j.val) (by omega)
    have hsame' : (wordPath G regular e a).val j' = (wordPath G regular e b).val j := by
      change pathAt (wordPath G regular e a).val j.val =
        pathAt (wordPath G regular e b).val j.val at hsame
      rw [pathAt_eq _ (by omega), pathAt_eq _ (by omega)] at hsame
      exact hsame
    exact hsame'.trans hv

theorem card_frontierAt_wordPrefix [NeZero d] (e : G.Dart) {a b : List (Fin d)}
    (hp : a <+: b) (h : ℕ) :
    Fintype.card (FrontierAt G (wordPath G regular e a).val (h + 1) (Fin.last a.length)) =
      Fintype.card (FrontierAt G (wordPath G regular e b).val (h + 1)
        ⟨a.length, by have := hp.length_le; omega⟩) := by
  let i : Fin (b.length + 1) := ⟨a.length, by have := hp.length_le; omega⟩
  have hfirst : (wordPath G regular e a).val (Fin.last a.length).castSucc =
      (wordPath G regular e b).val i.castSucc := by
    have hh := wordPath_vertex_of_prefix G regular e hp (i := a.length) (by omega)
    change pathAt (wordPath G regular e a).val a.length =
      pathAt (wordPath G regular e b).val a.length at hh
    rw [pathAt_eq _ (by omega), pathAt_eq _ (by have := hp.length_le; omega)] at hh
    exact hh
  have hsecond : (wordPath G regular e a).val (Fin.last a.length).succ =
      (wordPath G regular e b).val i.succ := by
    have hh := wordPath_vertex_of_prefix G regular e hp (i := a.length + 1) (by omega)
    change pathAt (wordPath G regular e a).val (a.length + 1) =
      pathAt (wordPath G regular e b).val (a.length + 1) at hh
    rw [pathAt_eq _ (by omega), pathAt_eq _ (by have := hp.length_le; omega)] at hh
    exact hh
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro p
  rw [hfirst, hsecond, pastAt_wordPrefix G regular e hp]

theorem goodAtWord_mem_goodPositions [NeZero d] (e : G.Dart)
    {a b : List (Fin d)} (hp : a <+: b) (h : ℕ)
    (hg : GoodAtWord G regular e a h) :
    a.length ∈ (goodPositions G (wordPath G regular e b).val (h + 1) d).image Fin.val := by
  classical
  let i : Fin (b.length + 1) := ⟨a.length, by have := hp.length_le; omega⟩
  refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change d ^ (h + 1 - 1) ≤ 2 * Fintype.card (FrontierAt G (wordPath G regular e b).val (h + 1) i)
  simpa only [GoodAtWord, Nat.add_sub_cancel, card_frontierAt_wordPrefix G regular e hp h, i] using hg

end CriticalHardcore.NBChoices
