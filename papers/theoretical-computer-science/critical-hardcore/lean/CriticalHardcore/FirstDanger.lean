import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Infix
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# First-danger prefixes and finite witness insertion

For each word that encounters danger, stop at its first dangerous prefix.
Insert a chosen padded killing witness there and retain the original suffix.
The first dangerous prefix is recoverable from the encoded word, so this
map is injective. It gives the required conditional collision probability
without conditioning on an arbitrarily chosen dangerous leaf.
-/

set_option autoImplicit false

namespace CriticalHardcore
namespace WordTrials

variable {A : Type*}

def Encounters (D : List A → Prop) (w : List A) : Prop :=
  ∃ p, p <+: w ∧ D p

/-- Minimality is only along the prefix order, which is the temporal order. -/
def IsFirstDanger (D : List A → Prop) (p : List A) : Prop :=
  D p ∧ ∀ q, q <+: p → D q → q = p

theorem exists_firstDanger (D : List A → Prop) (w : List A)
    (h : Encounters D w) : ∃ p, p <+: w ∧ IsFirstDanger D p := by
  classical
  obtain ⟨p, hp, hDp⟩ := h
  have hex : ∃ n : ℕ, n ≤ w.length ∧ D (w.take n) := by
    refine ⟨p.length, hp.length_le, ?_⟩
    simpa only [← List.prefix_iff_eq_take.mp hp] using hDp
  let n : ℕ := Nat.find hex
  have hn : n ≤ w.length ∧ D (w.take n) := Nat.find_spec hex
  refine ⟨w.take n, List.take_prefix n w, hn.2, ?_⟩
  intro q hq hDq
  have hqw : q <+: w := hq.trans (List.take_prefix n w)
  have hqD : D (w.take q.length) := by
    simpa only [← List.prefix_iff_eq_take.mp hqw] using hDq
  have hmin : n ≤ q.length := Nat.find_min' hex ⟨hqw.length_le, hqD⟩
  apply hq.eq_of_length_le
  simpa only [List.length_take_of_le hn.1] using hmin

noncomputable def firstDanger (D : List A → Prop) (w : List A) : List A := by
  classical
  exact if h : Encounters D w then Classical.choose (exists_firstDanger D w h) else []

theorem firstDanger_spec (D : List A → Prop) (w : List A)
    (h : Encounters D w) :
    firstDanger D w <+: w ∧ IsFirstDanger D (firstDanger D w) := by
  classical
  simpa only [firstDanger, dif_pos h] using Classical.choose_spec (exists_firstDanger D w h)

theorem firstDanger_prefix_unique {D : List A → Prop} {p q z : List A}
    (hp : IsFirstDanger D p) (hq : IsFirstDanger D q)
    (hpz : p <+: z) (hqz : q <+: z) : p = q := by
  rcases List.prefix_or_prefix_of_prefix hpz hqz with hpq | hqp
  · exact hq.2 p hpq hp.1
  · exact (hp.2 q hqp hq.1).symm

variable [Fintype A] [DecidableEq A]

/-- All words of a prescribed length over the finite alphabet. -/
def words (n : ℕ) : Finset (List A) :=
  Finset.univ.image (List.ofFn : (Fin n → A) → List A)

@[simp] theorem mem_words (n : ℕ) (w : List A) : w ∈ words n ↔ w.length = n := by
  constructor
  · intro h
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp h
    exact List.length_ofFn
  · intro h
    rw [← h]
    exact Finset.mem_image.mpr ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

@[simp] theorem card_words (n : ℕ) : (words (A := A) n).card = Fintype.card A ^ n := by
  unfold words
  rw [Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ]
  exact Fintype.card_pi_const A n

noncomputable def dangerousWords (D : List A → Prop) (h : ℕ) : Finset (List A) := by
  classical
  exact (words h).filter (Encounters D)

noncomputable def deadWords (dead : List A → Prop) (n : ℕ) : Finset (List A) := by
  classical
  exact (words n).filter dead

@[simp] theorem mem_dangerousWords (D : List A → Prop) (h : ℕ) (w : List A) :
    w ∈ dangerousWords D h ↔ w.length = h ∧ Encounters D w := by
  classical
  simp [dangerousWords]

@[simp] theorem mem_deadWords (dead : List A → Prop) (n : ℕ) (w : List A) :
    w ∈ deadWords dead n ↔ w.length = n ∧ dead w := by
  classical
  simp [deadWords]

/-- Exact counting form of the first-danger argument. Each dangerous prefix
has some killing continuation of length at most `L`; death is absorbing. -/
theorem dangerous_card_le_dead_card (a₀ : A) (D dead : List A → Prop)
    (h L : ℕ)
    (hdead : ∀ p t : List A, dead p → dead (p ++ t))
    (hwitness : ∀ p : List A, D p → ∃ t : List A, t.length ≤ L ∧ dead (p ++ t)) :
    (dangerousWords D h).card ≤ (deadWords dead (h + L)).card := by
  classical
  let rawKill : List A → List A := fun p =>
    if hp : D p then Classical.choose (hwitness p hp) else []
  have hraw : ∀ p, D p → (rawKill p).length ≤ L ∧ dead (p ++ rawKill p) := by
    intro p hp
    simpa only [rawKill, dif_pos hp] using Classical.choose_spec (hwitness p hp)
  let kill : List A → List A := fun p =>
    rawKill p ++ List.replicate (L - (rawKill p).length) a₀
  have hkill_len : ∀ p, D p → (kill p).length = L := by
    intro p hp
    simp only [kill, List.length_append, List.length_replicate]
    exact Nat.add_sub_of_le (hraw p hp).1
  have hkill_dead : ∀ p, D p → dead (p ++ kill p) := by
    intro p hp
    simpa only [kill, List.append_assoc] using
      hdead (p ++ rawKill p) (List.replicate (L - (rawKill p).length) a₀) (hraw p hp).2
  let encode : List A → List A := fun w =>
    firstDanger D w ++ (kill (firstDanger D w) ++ w.drop (firstDanger D w).length)
  have henc_prefix : ∀ w, firstDanger D w <+: encode w := by
    intro w
    exact List.prefix_append _ _
  have henc_mem : ∀ w ∈ dangerousWords D h, encode w ∈ deadWords dead (h + L) := by
    intro w hw
    obtain ⟨hwlen, hwD⟩ := (mem_dangerousWords D h w).mp hw
    obtain ⟨hpref, hfirst⟩ := firstDanger_spec D w hwD
    apply (mem_deadWords dead (h + L) (encode w)).mpr
    constructor
    · have hle := hpref.length_le
      have hklen := hkill_len (firstDanger D w) hfirst.1
      dsimp [encode]
      simp only [List.length_append, List.length_drop, hklen]
      omega
    · simpa only [encode, List.append_assoc] using
        hdead (firstDanger D w ++ kill (firstDanger D w))
          (w.drop (firstDanger D w).length) (hkill_dead _ hfirst.1)
  have hinj : Set.InjOn encode (↑(dangerousWords D h) : Set (List A)) := by
    intro w hw v hv heq
    have hwD := ((mem_dangerousWords D h w).mp hw).2
    have hvD := ((mem_dangerousWords D h v).mp hv).2
    obtain ⟨hpw, hfirstw⟩ := firstDanger_spec D w hwD
    obtain ⟨hpv, hfirstv⟩ := firstDanger_spec D v hvD
    have hp : firstDanger D w = firstDanger D v :=
      firstDanger_prefix_unique hfirstw hfirstv (by simpa only [heq] using henc_prefix w)
        (henc_prefix v)
    change firstDanger D w ++ (kill (firstDanger D w) ++ w.drop (firstDanger D w).length) =
      firstDanger D v ++ (kill (firstDanger D v) ++ v.drop (firstDanger D v).length) at heq
    rw [hp] at heq
    have htail := List.append_cancel_left (List.append_cancel_left heq)
    calc
      w = firstDanger D w ++ w.drop (firstDanger D w).length :=
        (List.prefix_iff_eq_append.mp hpw).symm
      _ = firstDanger D v ++ v.drop (firstDanger D v).length := by rw [hp, htail]
      _ = v := List.prefix_iff_eq_append.mp hpv
  exact Finset.card_le_card_of_injOn encode henc_mem hinj

/-- If at least half of the depth-`h` words encounter danger, uniform
depth-`h+L` sampling dies with probability at least `1/(2*card(A)^L)`. -/
theorem half_danger_killing_probability (a₀ : A) (D dead : List A → Prop)
    (h L : ℕ)
    (hdead : ∀ p t : List A, dead p → dead (p ++ t))
    (hwitness : ∀ p : List A, D p → ∃ t : List A, t.length ≤ L ∧ dead (p ++ t))
    (hhalf : (words (A := A) h).card ≤ 2 * (dangerousWords D h).card) :
    1 / (2 * (Fintype.card A : ℝ) ^ L) ≤
      ((deadWords dead (h + L)).card : ℝ) / (Fintype.card A : ℝ) ^ (h + L) := by
  have hc : (dangerousWords D h).card ≤ (deadWords dead (h + L)).card :=
    dangerous_card_le_dead_card a₀ D dead h L hdead hwitness
  have hcount : Fintype.card A ^ h ≤ 2 * (deadWords dead (h + L)).card := by
    rw [card_words] at hhalf
    omega
  have hcountR : (Fintype.card A : ℝ) ^ h ≤ 2 * ((deadWords dead (h + L)).card : ℝ) := by
    exact_mod_cast hcount
  have hcard : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨a₀⟩
  have hcardR : 0 < (Fintype.card A : ℝ) := by exact_mod_cast hcard
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (Fintype.card A : ℝ) ^ L)
    (pow_pos hcardR (h + L))).mpr
  rw [pow_add]
  nlinarith [mul_le_mul_of_nonneg_right hcountR (pow_nonneg hcardR.le L)]

end WordTrials
end CriticalHardcore
