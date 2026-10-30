import CriticalHardcore.NonbacktrackingAppend
import CriticalHardcore.WordTrialMass
import Mathlib.Tactic.FieldSimp

/-! Exact word counts, normalization, and monotonicity of graph survival. -/

set_option autoImplicit false

namespace CriticalHardcore.NBChoices

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d : ℕ} (regular : G.IsRegularOfDegree (d + 1)) [NeZero d]

theorem wordPath_ofFn_vertex (e : G.Dart) {n : ℕ} (word : Fin n → Fin d)
    {i : ℕ} (hi : i ≤ n + 1) :
    (wordPath G regular e (List.ofFn word)).vertex G i = (path G regular e word).vertex G i := by
  calc
    (wordPath G regular e (List.ofFn word)).vertex G i =
        vertex G regular e (wordAt (List.ofFn word).get) i :=
      path_vertex G regular e _ (by simpa using hi)
    _ = vertex G regular e (wordAt word) i :=
      vertex_congr G regular e _ _ (fun j _ => wordAt_get_ofFn word j)
    _ = (path G regular e word).vertex G i := (path_vertex G regular e word hi).symm

theorem aliveWord_ofFn_iff (e : G.Dart) {n : ℕ} (word : Fin n → Fin d) :
    AliveWord G regular e (List.ofFn word) ↔ Function.Injective (path G regular e word).val := by
  constructor
  · intro hw i j heq
    apply Fin.ext
    apply aliveWord_vertex_injective G regular e (List.ofFn word) hw
      (by simpa using Nat.le_of_lt_succ i.isLt) (by simpa using Nat.le_of_lt_succ j.isLt)
    rw [wordPath_ofFn_vertex G regular e word (by omega),
      wordPath_ofFn_vertex G regular e word (by omega)]
    simpa only [NBPath.vertex, pathAt_fin] using heq
  · intro hw
    apply (aliveWord_iff_vertex_injective G regular e _).mpr
    intro i j hi hj heq
    have hi' : i ≤ n + 1 := by simpa using hi
    have hj' : j ≤ n + 1 := by simpa using hj
    rw [wordPath_ofFn_vertex G regular e word hi', wordPath_ofFn_vertex G regular e word hj'] at heq
    change pathAt (path G regular e word).val i = pathAt (path G regular e word).val j at heq
    rw [pathAt_eq _ hi', pathAt_eq _ hj'] at heq
    exact congrArg (fun z : Fin (n + 1 + 1) => z.val) (hw heq)

theorem orientedCount_eq_continuations (e : G.Dart) (n : ℕ) :
    orientedCount G e.fst e.snd n =
      (WordTrials.continuations (AliveWord G regular e) [] n).card := by
  classical
  rw [orientedCount_eq_aliveWords G regular e n, Fintype.card_subtype]
  let S : Finset (Fin n → Fin d) :=
    Finset.univ.filter fun word => Function.Injective (path G regular e word).val
  change S.card = _
  have himage : S.image List.ofFn = WordTrials.continuations (AliveWord G regular e) [] n := by
    ext w
    constructor
    · intro hw
      obtain ⟨word, hword, rfl⟩ := Finset.mem_image.mp hw
      apply (WordTrials.mem_continuations _ _ _ _).mpr
      exact ⟨List.length_ofFn, by
        simpa only [List.nil_append] using
          (aliveWord_ofFn_iff G regular e word).mpr (Finset.mem_filter.mp hword).2⟩
    · intro hw
      obtain ⟨hlen, halive⟩ := (WordTrials.mem_continuations _ _ _ _).mp hw
      refine Finset.mem_image.mpr ⟨lettersOfList w hlen, ?_, ofFn_lettersOfList w hlen⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply (aliveWord_ofFn_iff G regular e _).mp
      rw [ofFn_lettersOfList]
      simpa only [List.nil_append] using halive
  rw [← himage, Finset.card_image_of_injective _ List.ofFn_injective]

theorem survival_eq_continuations (e : G.Dart) (n : ℕ) :
    survival G (d := d) e n =
      ((WordTrials.continuations (AliveWord G regular e) [] n).card : ℝ) / (d : ℝ) ^ n := by
  rw [survival, orientedCount_eq_continuations G regular e n]

theorem continuations_card_le (e : G.Dart) (p : List (Fin d)) (n : ℕ) :
    (WordTrials.continuations (AliveWord G regular e) p n).card ≤ d ^ n := by
  classical
  calc
    _ ≤ (WordTrials.words (A := Fin d) n).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = d ^ n := by simp

include regular in
theorem survival_add_le (e : G.Dart) (m k : ℕ) :
    survival G (d := d) e (m + k) ≤ survival G (d := d) e m := by
  classical
  have hpref : ∀ p q, AliveWord G regular e (p ++ q) → AliveWord G regular e p := by
    intro p q hpq
    exact aliveWord_of_prefix G regular e (List.prefix_append p q) hpq
  have hc : (WordTrials.continuations (AliveWord G regular e) [] (m + k)).card ≤
      (WordTrials.continuations (AliveWord G regular e) [] m).card * d ^ k := by
    rw [WordTrials.continuations_card_split _ hpref [] m k]
    calc
      _ ≤ ∑ _b ∈ WordTrials.continuations (AliveWord G regular e) [] m, d ^ k :=
        Finset.sum_le_sum fun b _ => continuations_card_le G regular e ([] ++ b) k
      _ = _ := by simp
  have hcR : ((WordTrials.continuations (AliveWord G regular e) [] (m + k)).card : ℝ) ≤
      ((WordTrials.continuations (AliveWord G regular e) [] m).card : ℝ) * (d : ℝ) ^ k := by
    exact_mod_cast hc
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  rw [survival_eq_continuations G regular, survival_eq_continuations G regular]
  calc
    _ ≤ (((WordTrials.continuations (AliveWord G regular e) [] m).card : ℝ) * (d : ℝ) ^ k) /
        (d : ℝ) ^ (m + k) := div_le_div_of_nonneg_right hcR (pow_nonneg hd.le _)
    _ = _ := by rw [pow_add, mul_div_mul_right _ _ (pow_ne_zero _ hd.ne')]

include regular in
theorem survival_antitone (e : G.Dart) : Antitone (survival G (d := d) e) := by
  intro m n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact survival_add_le G regular e m k

theorem survival_nonneg (e : G.Dart) (n : ℕ) : 0 ≤ survival G (d := d) e n := by
  unfold survival
  positivity

include regular in
theorem survival_le_one (e : G.Dart) (n : ℕ) : survival G (d := d) e n ≤ 1 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  apply (div_le_one (pow_pos hd n)).mpr
  exact_mod_cast orientedCount_le G regular e n

include regular in
theorem survival_eq_zero_of_card_le (e : G.Dart) {n : ℕ}
    (hn : Fintype.card V ≤ n + 1) : survival G (d := d) e n = 0 := by
  classical
  have hempty : WordTrials.continuations (AliveWord G regular e) [] n = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro w hw
    obtain ⟨hlen, halive⟩ := (WordTrials.mem_continuations _ _ _ _).mp hw
    have hb := aliveWord_length_bound G regular e w (by simpa using halive)
    omega
  rw [survival_eq_continuations G regular, hempty]
  simp

end CriticalHardcore.NBChoices
