import BergeTriangle.FinSystems

/-!
# The saturated system `J(p,q)` at the threshold

On `Fin n`, with `n = 2p + q` and `q ≥ 3`, take the pairs `Pᵢ = {2i, 2i+1}` for `i < p`,
with `P₁ = {x, y} = {0, 1}`, the two vertices `u = 2p` and `v = 2p+1`, and the set
`S = {2p+2, …, n-1}` of `q - 2` vertices.  The edges of `J(p,q)` are `Pᵢ ∪ {z}` for every
pair and every `z ∈ S`, `Pᵢ ∪ {v}` for every pair other than `P₁`, and `{x, u, v}`.
It is the pair system with base `{v} ∪ S`, minus `P₁ ∪ {v}`, plus `{x, u, v}`.
-/

namespace BergeTriangle

open Finset

section Sharp

variable (n p : ℕ)

/-- The edge `{x, u, v} = {0, 2p, 2p+1}`. -/
def jC : Finset (Fin n) :=
  univ.filter fun v => v.val = 0 ∨ v.val = 2 * p ∨ v.val = 2 * p + 1

/-- The product triple `P₁ ∪ {v} = {0, 1, 2p+1}`, which `J(p,q)` omits. -/
def jBad : Finset (Fin n) :=
  univ.filter fun v => v.val = 0 ∨ v.val = 1 ∨ v.val = 2 * p + 1

/-- The pair system with pairs `{2i, 2i+1}` (`i < p`) and base `{v} ∪ S = {2p+1, …, n-1}`. -/
def jSys (h : 2 * p + 3 ≤ n) : PairSystem (Fin n) :=
  finSystem n p (2 * p + 1) (by omega) (by omega)

/-- The triple system `J(p, n - 2p)` on `Fin n`: every triple `Pᵢ ∪ {b}` with `2p+1 ≤ b`
except `P₁ ∪ {v}`, together with `{x, u, v}`. -/
def sharpSystem (h : 2 * p + 3 ≤ n) : Finset (Finset (Fin n)) :=
  insert (jC n p) ((jSys n p h).edges.erase (jBad n p))

variable {n p}

/-- The vertex `x = 0`. -/
def j0 (h : 2 * p + 3 ≤ n) : Fin n := ⟨0, by omega⟩
/-- The vertex `y = 1`. -/
def j1 (h : 2 * p + 3 ≤ n) : Fin n := ⟨1, by omega⟩
/-- The vertex `u = 2p`. -/
def jU (h : 2 * p + 3 ≤ n) : Fin n := ⟨2 * p, by omega⟩
/-- The vertex `v = 2p+1`. -/
def jW (h : 2 * p + 3 ≤ n) : Fin n := ⟨2 * p + 1, by omega⟩
/-- The vertex `2p+2` of `S`. -/
def jZ (h : 2 * p + 3 ≤ n) : Fin n := ⟨2 * p + 2, by omega⟩

/-- The pair `Pᵢ₊₁ = {2i, 2i+1}`. -/
abbrev jPair (h : 2 * p + 3 ≤ n) (i : Fin p) : Finset (Fin n) :=
  finPair n p (by omega) i

@[simp] theorem j0_val (h : 2 * p + 3 ≤ n) : (j0 h).val = 0 := rfl
@[simp] theorem j1_val (h : 2 * p + 3 ≤ n) : (j1 h).val = 1 := rfl
@[simp] theorem jU_val (h : 2 * p + 3 ≤ n) : (jU h).val = 2 * p := rfl
@[simp] theorem jW_val (h : 2 * p + 3 ≤ n) : (jW h).val = 2 * p + 1 := rfl
@[simp] theorem jZ_val (h : 2 * p + 3 ≤ n) : (jZ h).val = 2 * p + 2 := rfl

theorem mem_edge_iff {hp : 2 * p ≤ n} {i : Fin p} {b v : Fin n} :
    v ∈ insert b (finPair n p hp i) ↔
      v.val = b.val ∨ v.val = 2 * i.val ∨ v.val = 2 * i.val + 1 := by
  rw [mem_insert, mem_finPair, Fin.ext_iff]

theorem mem_jC {v : Fin n} : v ∈ jC n p ↔ v.val = 0 ∨ v.val = 2 * p ∨ v.val = 2 * p + 1 := by
  simp only [jC, mem_filter, mem_univ, true_and]

theorem mem_jBad {v : Fin n} : v ∈ jBad n p ↔ v.val = 0 ∨ v.val = 1 ∨ v.val = 2 * p + 1 := by
  simp only [jBad, mem_filter, mem_univ, true_and]

/-- Discharges vertex-membership and vertex-inequality side goals by arithmetic. -/
macro "vtac" : tactic =>
  `(tactic| (simp only [mem_edge_iff, mem_jC, mem_jBad, j0_val, j1_val, jU_val, jW_val, jZ_val,
    ne_eq, Fin.ext_iff, or_true, true_or] <;> omega))

theorem jSys_mem_edges (h : 2 * p + 3 ≤ n) {T : Finset (Fin n)} :
    T ∈ (jSys n p h).edges ↔
      ∃ i : Fin p, ∃ b : Fin n, 2 * p + 1 ≤ b.val ∧ insert b (jPair h i) = T :=
  finSystem_mem_edges

theorem jSys_mem_pairs (h : 2 * p + 3 ≤ n) {P : Finset (Fin n)} :
    P ∈ (jSys n p h).pairs ↔ ∃ i, jPair h i = P :=
  finSystem_mem_pairs

theorem jSys_mem_base (h : 2 * p + 3 ≤ n) {v : Fin n} :
    v ∈ (jSys n p h).base ↔ 2 * p + 1 ≤ v.val :=
  finSystem_mem_base

theorem edge_eq_bad_iff (h : 2 * p + 3 ≤ n) {i : Fin p} {b : Fin n} (hb : 2 * p + 1 ≤ b.val) :
    insert b (jPair h i) = jBad n p ↔ i.val = 0 ∧ b.val = 2 * p + 1 := by
  constructor
  · intro e
    have h₁ : b ∈ jBad n p := by rw [← e]; exact mem_insert_self _ _
    have h₂ : j0 h ∈ insert b (jPair h i) := by rw [e, mem_jBad]; exact Or.inl rfl
    rw [mem_jBad] at h₁
    rw [mem_edge_iff, j0_val] at h₂
    omega
  · intro hi
    ext v
    rw [mem_edge_iff, mem_jBad]
    omega

theorem mem_sharpSystem (h : 2 * p + 3 ≤ n) {e : Finset (Fin n)} :
    e ∈ sharpSystem n p h ↔ e = jC n p ∨ (e ≠ jBad n p ∧ e ∈ (jSys n p h).edges) := by
  simp only [sharpSystem, mem_insert, mem_erase]

theorem edge_mem_sharpSystem (h : 2 * p + 3 ≤ n) {i : Fin p} {b : Fin n}
    (hb : 2 * p + 1 ≤ b.val) (hne : ¬ (i.val = 0 ∧ b.val = 2 * p + 1)) :
    insert b (jPair h i) ∈ sharpSystem n p h :=
  (mem_sharpSystem h).2 (Or.inr ⟨fun e => hne ((edge_eq_bad_iff h hb).1 e),
    (jSys_mem_edges h).2 ⟨i, b, hb, rfl⟩⟩)

theorem jC_mem_sharpSystem (h : 2 * p + 3 ≤ n) : jC n p ∈ sharpSystem n p h :=
  mem_insert_self _ _

theorem jU_not_mem_edge (h : 2 * p + 3 ≤ n) {i : Fin p} {b : Fin n} (hb : 2 * p + 1 ≤ b.val) :
    jU h ∉ insert b (jPair h i) := by
  rw [mem_edge_iff, jU_val]
  have := i.isLt
  omega

theorem jU_mem_jC (h : 2 * p + 3 ≤ n) : jU h ∈ jC n p := by
  rw [mem_jC, jU_val]
  exact Or.inr (Or.inl rfl)

theorem jC_ne_edge (h : 2 * p + 3 ≤ n) {i : Fin p} {b : Fin n} (hb : 2 * p + 1 ≤ b.val) :
    jC n p ≠ insert b (jPair h i) :=
  ne_of_mem_of_not_mem' (jU_mem_jC h) (jU_not_mem_edge h hb)

theorem jC_not_mem_jSys (h : 2 * p + 3 ≤ n) : jC n p ∉ (jSys n p h).edges := by
  intro hC
  obtain ⟨i, b, hb, e⟩ := (jSys_mem_edges h).1 hC
  exact jC_ne_edge h hb e.symm

/-- In `J`, the only edge containing `u` is `{x, u, v}`. -/
theorem eq_jC_of_jU_mem (h : 2 * p + 3 ≤ n) {e : Finset (Fin n)} (he : e ∈ sharpSystem n p h)
    (hu : jU h ∈ e) : e = jC n p := by
  rcases (mem_sharpSystem h).1 he with e' | ⟨-, e'⟩
  · exact e'
  · obtain ⟨i, b, hb, rfl⟩ := (jSys_mem_edges h).1 e'
    exact absurd hu (jU_not_mem_edge h hb)

theorem jC_eq (h : 2 * p + 3 ≤ n) : jC n p = {j0 h, jU h, jW h} := by
  ext v
  simp only [mem_jC, mem_insert, mem_singleton, Fin.ext_iff, j0_val, jU_val, jW_val]

/-- The edges of `J(p, n - 2p)` are `{x, u, v}`, the triples `Pᵢ ∪ {z}` with `z ∈ S`, and the
triples `Pᵢ ∪ {v}` with `Pᵢ ≠ P₁`. -/
theorem mem_sharpSystem_iff (h : 2 * p + 3 ≤ n) {e : Finset (Fin n)} :
    e ∈ sharpSystem n p h ↔ e = {j0 h, jU h, jW h} ∨
      (∃ i : Fin p, ∃ z : Fin n, 2 * p + 2 ≤ z.val ∧ e = insert z (jPair h i)) ∨
      (∃ i : Fin p, i.val ≠ 0 ∧ e = insert (jW h) (jPair h i)) := by
  rw [mem_sharpSystem, ← jC_eq h]
  constructor
  · rintro (rfl | ⟨hne, he⟩)
    · exact Or.inl rfl
    · obtain ⟨i, b, hb, rfl⟩ := (jSys_mem_edges h).1 he
      right
      by_cases hbW : b.val = 2 * p + 1
      · have hb' : b = jW h := Fin.ext hbW
        subst hb'
        exact Or.inr ⟨i, fun hi => hne ((edge_eq_bad_iff h hb).2 ⟨hi, hbW⟩), rfl⟩
      · exact Or.inl ⟨i, b, by omega, rfl⟩
  · rintro (rfl | ⟨i, z, hz, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨fun e => ?_, (jSys_mem_edges h).2 ⟨i, z, by omega, rfl⟩⟩
      have := ((edge_eq_bad_iff h (by omega)).1 e).2
      omega
    · exact Or.inr ⟨fun e => hi ((edge_eq_bad_iff h (by simp)).1 e).1,
        (jSys_mem_edges h).2 ⟨i, jW h, by simp, rfl⟩⟩

theorem card_jC (h : 2 * p + 3 ≤ n) (hp : 1 ≤ p) : (jC n p).card = 3 := by
  rw [jC_eq h, card_eq_three]
  refine ⟨j0 h, jU h, jW h, ?_, ?_, ?_, rfl⟩ <;> vtac

/-- `J` is Berge-triangle-free. -/
theorem sharpSystem_free (h : 2 * p + 3 ≤ n) : BergeTriangleFree (sharpSystem n p h) := by
  have key : ∀ {x y z : Fin n} {h₁ h₂ : Finset (Fin n)},
      h₁ ∈ sharpSystem n p h → h₂ ∈ sharpSystem n p h → h₁ ≠ jC n p → h₂ ≠ jC n p →
      x ≠ y → y ≠ z → z ≠ x → x ∈ h₁ → y ∈ h₁ → y ∈ h₂ → z ∈ h₂ → z ∈ jC n p →
      x ∈ jC n p → False := by
    intro x y z h₁ h₂ m₁ m₂ c₁ c₂ hxy hyz hzx hx₁ hy₁ hy₂ hz₂ hzC hxC
    obtain ⟨n₁, e₁⟩ := ((mem_sharpSystem h).1 m₁).resolve_left c₁
    obtain ⟨n₂, e₂⟩ := ((mem_sharpSystem h).1 m₂).resolve_left c₂
    obtain ⟨i₁, b₁, hb₁, rfl⟩ := (jSys_mem_edges h).1 e₁
    obtain ⟨i₂, b₂, hb₂, rfl⟩ := (jSys_mem_edges h).1 e₂
    have nb₁ : ¬ (i₁.val = 0 ∧ b₁.val = 2 * p + 1) := fun e => n₁ ((edge_eq_bad_iff h hb₁).2 e)
    have nb₂ : ¬ (i₂.val = 0 ∧ b₂.val = 2 * p + 1) := fun e => n₂ ((edge_eq_bad_iff h hb₂).2 e)
    rw [mem_edge_iff] at hx₁ hy₁ hy₂ hz₂
    rw [mem_jC] at hzC hxC
    rw [ne_eq, Fin.ext_iff] at hxy hyz hzx
    have := i₁.isLt
    have := i₂.isLt
    omega
  rintro ⟨x, y, z, h₁, h₂, h₃, m₁, m₂, m₃, hxy, hyz, hzx, h₁₂, h₂₃, h₃₁,
    hx₁, hy₁, hy₂, hz₂, hz₃, hx₃⟩
  by_cases c₁ : h₁ = jC n p
  · subst c₁
    exact key m₂ m₃ (Ne.symm h₁₂) h₃₁ hyz hzx hxy hy₂ hz₂ hz₃ hx₃ hx₁ hy₁
  by_cases c₂ : h₂ = jC n p
  · subst c₂
    exact key m₃ m₁ (Ne.symm h₂₃) c₁ hzx hxy hyz hz₃ hx₃ hx₁ hy₁ hy₂ hz₂
  by_cases c₃ : h₃ = jC n p
  · subst c₃
    exact key m₁ m₂ c₁ c₂ hxy hyz hzx hx₁ hy₁ hy₂ hz₂ hz₃ hx₃
  have e₁ := (((mem_sharpSystem h).1 m₁).resolve_left c₁).2
  have e₂ := (((mem_sharpSystem h).1 m₂).resolve_left c₂).2
  have e₃ := (((mem_sharpSystem h).1 m₃).resolve_left c₃).2
  exact (jSys n p h).free ⟨x, y, z, h₁, h₂, h₃, e₁, e₂, e₃, hxy, hyz, hzx, h₁₂, h₂₃, h₃₁,
    hx₁, hy₁, hy₂, hz₂, hz₃, hx₃⟩

/-- `J` is saturated. -/
theorem sharpSystem_saturated (h : 2 * p + 3 ≤ n) (hp : 1 ≤ p) :
    IsSaturated (sharpSystem n p h) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin p, i.val = 0 := ⟨⟨0, hp⟩, rfl⟩
  have A0_mem : ∀ z : Fin n, 2 * p + 2 ≤ z.val → insert z (jPair h i₀) ∈ sharpSystem n p h :=
    fun z hz => edge_mem_sharpSystem h (by omega) (by omega)
  refine ⟨?_, sharpSystem_free h, fun T hT3 hT => ?_⟩
  · intro e he
    rcases (mem_sharpSystem h).1 he with rfl | ⟨-, e'⟩
    · exact card_jC h hp
    · exact (jSys n p h).isThreeUniform e e'
  by_cases hU : jU h ∈ T
  · have hsub : ¬ T ⊆ jC n p := fun hsub => hT (by
      rw [eq_of_subset_of_card_le hsub (by rw [hT3, card_jC h hp])]
      exact jC_mem_sharpSystem h)
    obtain ⟨t, htT, htC⟩ := not_subset.1 hsub
    rw [mem_jC] at htC
    have htU : jU h ≠ t := by vtac
    rcases (by omega : t.val = 1 ∨ 2 * p + 2 ≤ t.val ∨ (2 ≤ t.val ∧ t.val < 2 * p)) with
      h1 | hz | ⟨h2, h2p⟩
    · exact hasBergeTriangle_insert_of_path (w := j0 h) hT hU htT htU (by vtac) (by vtac)
        (jC_mem_sharpSystem h) (A0_mem (jZ h) (by simp)) (jC_ne_edge h (by simp))
        (by vtac) (by vtac) (by vtac) (by vtac)
    · exact hasBergeTriangle_insert_of_path (w := j0 h) hT hU htT htU (by vtac) (by vtac)
        (jC_mem_sharpSystem h) (A0_mem t hz) (jC_ne_edge h (by omega))
        (by vtac) (by vtac) (by vtac) (by vtac)
    · have hi : t.val / 2 < p := by omega
      have hmem : insert (jW h) (jPair h ⟨t.val / 2, hi⟩) ∈ sharpSystem n p h :=
        edge_mem_sharpSystem h (by simp) (by simp only [jW_val]; omega)
      exact hasBergeTriangle_insert_of_path (w := jW h) hT hU htT htU (by vtac) (by vtac)
        (jC_mem_sharpSystem h) hmem (jC_ne_edge h (by simp)) (by vtac) (by vtac) (by vtac)
        (by simp only [mem_edge_iff, jW_val]; omega)
  · have hcov : ∀ v ∈ T, v ∈ (jSys n p h).base ∨ ∃ P ∈ (jSys n p h).pairs, v ∈ P := by
      intro v hv
      have hvU : v.val ≠ 2 * p := fun e => hU (by rwa [show v = jU h from Fin.ext e] at hv)
      by_cases hb : 2 * p + 1 ≤ v.val
      · exact Or.inl ((jSys_mem_base h).2 hb)
      · refine Or.inr ⟨jPair h ⟨v.val / 2, by omega⟩, (jSys_mem_pairs h).2 ⟨_, rfl⟩, ?_⟩
        rw [mem_finPair]
        simp only
        omega
    by_cases hTS : T ∈ (jSys n p h).edges
    · have hTbad : T = jBad n p := by
        by_contra hne
        exact hT ((mem_sharpSystem h).2 (Or.inr ⟨hne, hTS⟩))
      have h1T : j1 h ∈ T := by rw [hTbad, mem_jBad, j1_val]; omega
      have hWT : jW h ∈ T := by rw [hTbad, mem_jBad, jW_val]; omega
      exact hasBergeTriangle_insert_of_path (w := j0 h) hT h1T hWT (by vtac) (by vtac)
        (by vtac) (A0_mem (jZ h) (by simp)) (jC_mem_sharpSystem h)
        (Ne.symm (jC_ne_edge h (by simp))) (by vtac) (by vtac) (by vtac) (by vtac)
    · obtain ⟨a, ha, b, hb, hab, hsplit⟩ := (jSys n p h).exists_split hT3 hcov hTS
      rcases hsplit with ⟨haB, hbB⟩ | ⟨P, hP, Q, hQ, hPQ, haP, hbQ⟩
      · rw [jSys_mem_base] at haB hbB
        have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
        by_cases haW : a.val = 2 * p + 1
        · exact hasBergeTriangle_insert_of_path (w := j0 h) hT ha hb hab (by vtac) (by vtac)
            (jC_mem_sharpSystem h) (A0_mem b (by omega)) (jC_ne_edge h (by omega))
            (by vtac) (by vtac) (by vtac) (by vtac)
        by_cases hbW : b.val = 2 * p + 1
        · exact hasBergeTriangle_insert_of_path (w := j0 h) hT ha hb hab (by vtac) (by vtac)
            (A0_mem a (by omega)) (jC_mem_sharpSystem h) (Ne.symm (jC_ne_edge h (by omega)))
            (by vtac) (by vtac) (by vtac) (by vtac)
        · refine hasBergeTriangle_insert_of_path (w := j0 h) hT ha hb hab (by vtac) (by vtac)
            (A0_mem a (by omega)) (A0_mem b (by omega)) ?_ (by vtac) (by vtac) (by vtac)
            (by vtac)
          exact ne_of_mem_of_not_mem' (mem_insert_self a _) (by vtac)
      · obtain ⟨i, rfl⟩ := (jSys_mem_pairs h).1 hP
        obtain ⟨i', rfl⟩ := (jSys_mem_pairs h).1 hQ
        rw [mem_finPair] at haP hbQ
        have hii : i.val ≠ i'.val := fun e => hPQ (by rw [Fin.ext e])
        have := i.isLt
        have := i'.isLt
        refine hasBergeTriangle_insert_of_path (w := jZ h) hT ha hb hab (by vtac) (by vtac)
          (edge_mem_sharpSystem h (b := jZ h) (i := i) (by simp) (by simp))
          (edge_mem_sharpSystem h (b := jZ h) (i := i') (by simp) (by simp)) ?_ (by vtac)
          (by vtac) (by vtac) (by vtac)
        exact ne_of_mem_of_not_mem' (v := a) (by vtac) (by vtac)

theorem card_sharpSystem (h : 2 * p + 3 ≤ n) (hp : 1 ≤ p) :
    (sharpSystem n p h).card = p * (n - 2 * p - 1) := by
  have hbad : jBad n p ∈ (jSys n p h).edges :=
    (jSys_mem_edges h).2 ⟨⟨0, hp⟩, jW h, by simp, (edge_eq_bad_iff h (by simp)).2 ⟨rfl, rfl⟩⟩
  have hE : (jSys n p h).edges.card = p * (n - (2 * p + 1)) := finSystem_card_edges _ _ _ _ _
  rw [sharpSystem, card_insert_of_notMem (fun e => jC_not_mem_jSys h (mem_of_mem_erase e)),
    card_erase_of_mem hbad, hE]
  have : 0 < p * (n - (2 * p + 1)) := mul_pos (by omega) (by omega)
  rw [show n - 2 * p - 1 = n - (2 * p + 1) by omega]
  omega

/-- For `p ≥ 2`, `J` is not a paired product. -/
theorem sharpSystem_not_product (h : 2 * p + 3 ≤ n) (hp : 2 ≤ p) :
    ¬ IsPairedProduct (sharpSystem n p h) := by
  rintro ⟨S, hS⟩
  have h1 : 1 < p := hp
  set e₁ := insert (jW h) (jPair h ⟨1, h1⟩) with he₁
  set e₂ := insert (jZ h) (jPair h ⟨0, by omega⟩) with he₂
  have m₁ : e₁ ∈ S.edges := hS ▸ edge_mem_sharpSystem h (by simp) (by simp)
  have m₂ : e₂ ∈ S.edges := hS ▸ edge_mem_sharpSystem h (by simp) (by simp)
  have hdisj : ∀ v, v ∈ e₁ → v ∉ e₂ := by
    intro v hv hv'
    rw [he₁, mem_edge_iff] at hv
    rw [he₂, mem_edge_iff] at hv'
    simp only [jW_val, jZ_val] at hv hv'
    omega
  have hU : ∀ e ∈ S.edges, jU h ∈ e → e = jC n p := fun e he hu =>
    eq_jC_of_jU_mem h (hS ▸ he) hu
  rcases S.cover (jU h) with hUB | ⟨P₀, hP₀, hUP⟩
  · obtain ⟨P₁, hP₁, b₁, hb₁, h₁⟩ := S.mem_edges.1 m₁
    have hC : insert (jU h) P₁ = jC n p :=
      hU _ (S.insert_mem_edges hP₁ hUB) (mem_insert_self _ _)
    obtain ⟨a, b, hab, hP⟩ := card_eq_two.1 (S.card_pair P₁ hP₁)
    have ha₁ : a ∈ e₁ := h₁ ▸ mem_insert_of_mem (by rw [hP]; simp)
    have hb₁ : b ∈ e₁ := h₁ ▸ mem_insert_of_mem (by rw [hP]; simp)
    have haC : a ∈ jC n p := hC ▸ mem_insert_of_mem (by rw [hP]; simp)
    have hbC : b ∈ jC n p := hC ▸ mem_insert_of_mem (by rw [hP]; simp)
    rw [he₁, mem_edge_iff] at ha₁ hb₁
    rw [mem_jC] at haC hbC
    simp only [jW_val] at ha₁ hb₁
    exact hab (Fin.ext (by omega))
  · obtain ⟨P₁, hP₁, b₁, hb₁, h₁⟩ := S.mem_edges.1 m₁
    obtain ⟨P₂, hP₂, b₂, hb₂, h₂⟩ := S.mem_edges.1 m₂
    have c₁ : insert b₁ P₀ = jC n p :=
      hU _ (S.insert_mem_edges hP₀ hb₁) (mem_insert_of_mem hUP)
    have c₂ : insert b₂ P₀ = jC n p :=
      hU _ (S.insert_mem_edges hP₀ hb₂) (mem_insert_of_mem hUP)
    have hb : b₁ = b₂ := S.eq_base_of_mem hP₀ hb₁ (by rw [c₂, ← c₁]; exact mem_insert_self _ _)
    have hb₁e : b₁ ∈ e₁ := h₁ ▸ mem_insert_self _ _
    have hb₂e : b₂ ∈ e₂ := h₂ ▸ mem_insert_self _ _
    exact hdisj b₁ hb₁e (hb ▸ hb₂e)

end Sharp

end BergeTriangle
