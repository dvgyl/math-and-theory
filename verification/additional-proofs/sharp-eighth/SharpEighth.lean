import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Data.List.Basic

/-!
# Sharp level-one Fourier weight at density one eighth

Lean 4.19.0; mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
The exact optimum is 3/64, attained in every dimension n >= 3.
All finite certificate data and arbitrary-dimension bridges are proved here.
The main results are in namespace `SharpEighth`, near the end of this file.
-/

/-! ## SymmetricCertificate -/
namespace SharpEighth

abbrev Part := List ℕ
abbrev SymPoly := List (Part × ℚ)

def canon (p : Part) : Part := List.insertionSort (· ≥ ·) p
def incPart (p : Part) (i k : ℕ) : Part := canon (p.modify i (fun a => a + k))
def raisePart (p : Part) : List Part :=
  canon (p ++ [1]) :: (List.range p.length).map (fun i => incPart p i 1)

def symEval (O : Part → ℝ) : SymPoly → ℝ
  | [] => 0
  | (p, c) :: l => (c : ℝ) * O p + symEval O l

def insertTerm (p : Part) (c : ℚ) : SymPoly → SymPoly
  | [] => [(p, c)]
  | (q, d) :: l => if p = q then (q, c+d) :: l else (q,d) :: insertTerm p c l

def collectTerms : SymPoly → SymPoly
  | [] => []
  | (p,c) :: l => insertTerm p c (collectTerms l)

def scalePoly (c : ℚ) (l : SymPoly) : SymPoly := l.map (fun (p,d) => (p,c*d))
def addPoly (l r : SymPoly) : SymPoly := collectTerms (l ++ r)
def vMulPoly (l : SymPoly) : SymPoly :=
  collectTerms (l.flatMap (fun (p,c) => (raisePart p).map (fun q => (q,c))))
def homogenize (k : ℕ) (l : SymPoly) : SymPoly :=
  Nat.rec l (fun _ r => vMulPoly r) k

@[simp] theorem symEval_nil (O : Part → ℝ) : symEval O [] = 0 := rfl
@[simp] theorem symEval_cons (O : Part → ℝ) (p : Part) (c : ℚ) (l : SymPoly) :
    symEval O ((p,c)::l) = (c:ℝ)*O p + symEval O l := rfl

theorem symEval_append (O : Part → ℝ) (l r : SymPoly) :
    symEval O (l ++ r) = symEval O l + symEval O r := by
  induction l with
  | nil => simp [symEval]
  | cons t l ih => rcases t with ⟨p,c⟩; simp [symEval, ih, add_assoc]

theorem symEval_insert (O : Part → ℝ) (p : Part) (c : ℚ) (l : SymPoly) :
    symEval O (insertTerm p c l) = (c:ℝ)*O p + symEval O l := by
  induction l with
  | nil => simp [insertTerm, symEval]
  | cons t l ih =>
    rcases t with ⟨q,d⟩
    by_cases h : p = q
    · subst q; simp [insertTerm, symEval, Rat.cast_add]; ring
    · simp [insertTerm, h, symEval, ih]; ring

theorem symEval_collect (O : Part → ℝ) (l : SymPoly) :
    symEval O (collectTerms l) = symEval O l := by
  induction l with
  | nil => rfl
  | cons t l ih => rcases t with ⟨p,c⟩; simp [collectTerms, symEval_insert, ih]

theorem symEval_scale (O : Part → ℝ) (c : ℚ) (l : SymPoly) :
    symEval O (scalePoly c l) = (c:ℝ)*symEval O l := by
  induction l with
  | nil => simp [scalePoly, symEval]
  | cons t l ih =>
    rcases t with ⟨p,d⟩
    simp [scalePoly, symEval, Rat.cast_mul] at ih ⊢
    rw [ih]; ring

theorem symEval_add (O : Part → ℝ) (l r : SymPoly) :
    symEval O (addPoly l r) = symEval O l + symEval O r := by
  simp [addPoly, symEval_collect, symEval_append]

theorem symEval_constMap (O : Part → ℝ) (c : ℚ) (ps : List Part) :
    symEval O (ps.map (fun p => (p,c))) = (c:ℝ)*(ps.map O).sum := by
  induction ps with
  | nil => simp [symEval]
  | cons p ps ih => simp [symEval, ih]; ring

theorem symEval_vMul (O : Part → ℝ) (V : ℝ)
    (hMul : ∀ p, (raisePart p |>.map O).sum = V * O p) (l : SymPoly) :
    symEval O (vMulPoly l) = V * symEval O l := by
  unfold vMulPoly
  rw [symEval_collect]
  induction l with
  | nil => simp [symEval]
  | cons t l ih =>
    rcases t with ⟨p,c⟩
    simp only [List.flatMap_cons, symEval_append, symEval_cons]
    rw [symEval_constMap, hMul, ih]
    ring

theorem symEval_homogenize (O : Part → ℝ) (V : ℝ)
    (hMul : ∀ p, (raisePart p |>.map O).sum = V * O p) (k : ℕ) (l : SymPoly) :
    symEval O (homogenize k l) = V^k * symEval O l := by
  induction k with
  | zero => simp [homogenize]
  | succ k ih =>
    change symEval O (vMulPoly (homogenize k l)) = _
    rw [symEval_vMul O V hMul, ih, pow_succ]
    ring


def normalizePoly (l : SymPoly) : SymPoly :=
  List.insertionSort (fun a b => compare a.1 b.1 ≠ Ordering.gt)
    ((collectTerms l).filter (fun t => t.2 != 0))

theorem symEval_eq_sum (O : Part → ℝ) (l : SymPoly) :
    symEval O l = (l.map (fun t => (t.2:ℝ)*O t.1)).sum := by
  induction l with
  | nil => rfl
  | cons t l ih => rcases t with ⟨p,c⟩; simp [symEval, ih]

theorem symEval_perm (O : Part → ℝ) {l r : SymPoly} (h : l.Perm r) :
    symEval O l = symEval O r := by
  rw [symEval_eq_sum, symEval_eq_sum]
  exact (h.map _).sum_eq

theorem symEval_filter (O : Part → ℝ) (l : SymPoly) :
    symEval O (l.filter (fun t => t.2 != 0)) = symEval O l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    rcases t with ⟨p,c⟩
    by_cases h : c = 0
    · subst c; simp [symEval, ih]
    · simp [symEval, h, ih]

theorem symEval_normalize (O : Part → ℝ) (l : SymPoly) :
    symEval O (normalizePoly l) = symEval O l := by
  unfold normalizePoly
  rw [symEval_perm O (List.perm_insertionSort _ _), symEval_filter, symEval_collect]

theorem symEval_of_normalize_eq (O : Part → ℝ) (l r : SymPoly)
    (h : normalizePoly l = normalizePoly r) : symEval O l = symEval O r := by
  rw [← symEval_normalize O l, ← symEval_normalize O r, h]

end SharpEighth


/-! ## OrbitBridge -/
open scoped BigOperators Classical
open Finset

namespace SharpEighth

noncomputable section

variable {ι : Type*} [Fintype ι]

def orbitTerm (p : List ℕ) (z : ι → ℝ) (e : Fin p.length ↪ ι) : ℝ :=
  ∏ k, z (e k) ^ p.get k

def orbit (p : List ℕ) (z : ι → ℝ) : ℝ := ∑ e : Fin p.length ↪ ι, orbitTerm p z e

theorem orbit_nonneg (p : List ℕ) (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ orbit p z := by
  apply sum_nonneg
  intro e _
  apply prod_nonneg
  intro k _
  exact pow_nonneg (hz _) _

theorem orbit_reindex (p q : List ℕ) (z : ι → ℝ)
    (a : Fin p.length ≃ Fin q.length) (ha : ∀ k, q.get (a k) = p.get k) :
    orbit p z = orbit q z := by
  unfold orbit
  apply Fintype.sum_equiv (Equiv.embeddingCongr a (Equiv.refl ι))
  intro e
  unfold orbitTerm
  apply Fintype.prod_equiv a
  intro k
  simp [ha, Function.Embedding.congr]
  simpa only [List.get_eq_getElem] using congrArg (fun t => z (e k) ^ t) (ha k).symm

theorem list_perm_get_equiv {α : Type*} {p q : List α} (h : p.Perm q) :
    ∃ a : Fin p.length ≃ Fin q.length, ∀ k, q.get (a k) = p.get k := by
  induction h with
  | nil =>
      refine ⟨Equiv.refl _, ?_⟩
      intro k
      rfl
  | @cons x p q h ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨(finSuccEquiv p.length).trans
        ((Equiv.optionCongr a).trans (finSuccEquiv q.length).symm), ?_⟩
      intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp
      · simpa using ha k
  | swap x y p =>
      refine ⟨Equiv.swap (0 : Fin (p.length + 2)) (1 : Fin (p.length + 2)), ?_⟩
      intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp
      · refine Fin.cases ?_ (fun k => ?_) k
        · simp
        · have h0 : k.succ.succ ≠ (0 : Fin (p.length + 2)) := by simp
          have h1 : k.succ.succ ≠ (1 : Fin (p.length + 2)) := by
            intro h
            have := congrArg Fin.val h
            simp only [Fin.val_succ, Fin.val_one] at this
            omega
          simp [Equiv.swap_apply_of_ne_of_ne h0 h1]
  | @trans p q r hpq hqr ihpq ihqr =>
      obtain ⟨a, ha⟩ := ihpq
      obtain ⟨b, hb⟩ := ihqr
      exact ⟨a.trans b, fun k => (hb (a k)).trans (ha k)⟩

theorem orbit_perm {p q : List ℕ} (h : p.Perm q) (z : ι → ℝ) :
    orbit p z = orbit q z := by
  obtain ⟨a, ha⟩ := list_perm_get_equiv h
  exact orbit_reindex p q z a ha

theorem orbit_nil (z : ι → ℝ) : orbit [] z = 1 := by
  haveI : Unique (Fin 0 ↪ ι) :=
    ⟨⟨Function.Embedding.ofIsEmpty⟩, fun e => DFunLike.ext _ _ isEmptyElim⟩
  simp [orbit, orbitTerm]

theorem orbit_canon (p : List ℕ) (z : ι → ℝ) : orbit (canon p) z = orbit p z := by
  apply orbit_perm
  exact List.perm_insertionSort _ _

theorem orbit_cons (d : ℕ) (p : List ℕ) (z : ι → ℝ) :
    orbit (d :: p) z = ∑ e : Fin p.length ↪ ι,
      ∑ x : {i : ι // i ∉ Set.range e}, z x.val ^ d * orbitTerm p z e := by
  unfold orbit
  rw [← Fintype.sum_sigma']
  apply Fintype.sum_equiv (Equiv.embeddingFinSucc p.length ι)
  intro e
  simp [orbitTerm, Fin.prod_univ_succ]

theorem sum_embedding_range_compl {p : List ℕ} (e : Fin p.length ↪ ι) (z : ι → ℝ) :
    (∑ i, z i) = (∑ k, z (e k)) + ∑ i : {i : ι // i ∉ Set.range e}, z i.val := by
  have h : (∑ i : {i : ι // i ∈ Set.range e}, z i.val) +
      (∑ i : {i : ι // i ∉ Set.range e}, z i.val) = ∑ i, z i := by
    convert Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ Set.range e) z
  have himage : (∑ i : {i : ι // i ∈ Set.range e}, z i.val) = ∑ k, z (e k) := by
    symm
    apply Fintype.sum_equiv (Equiv.ofInjective e e.injective)
    intro k
    rfl
  rw [himage] at h
  exact h.symm

theorem orbit_eq_cast_sum (p : List ℕ) (z : ι → ℝ) {k : ℕ} (h : p.length = k) :
    orbit p z = ∑ e : Fin k ↪ ι,
      ∏ j : Fin k, z (e j) ^ p.get (Fin.cast h.symm j) := by
  unfold orbit
  apply Fintype.sum_equiv (Equiv.embeddingCongr (finCongr h) (Equiv.refl ι))
  intro e
  unfold orbitTerm
  apply Fintype.prod_equiv (finCongr h)
  intro j
  simp [Function.Embedding.congr]

theorem orbit_modify (p : List ℕ) (z : ι → ℝ) (i : Fin p.length) (r : ℕ) :
    orbit (p.modify i.val (fun a => a + r)) z =
      ∑ e : Fin p.length ↪ ι, orbitTerm p z e * z (e i) ^ r := by
  rw [orbit_eq_cast_sum _ z (List.length_modify _ _ _)]
  apply sum_congr rfl
  intro e _
  have hterm (k : Fin p.length) :
      z (e k) ^ (p.modify i.val (fun a => a + r)).get
          (Fin.cast (List.length_modify _ _ _).symm k) =
        z (e k) ^ p.get k * (if k = i then z (e i) ^ r else 1) := by
    by_cases hk : k = i
    · subst k
      simp [List.get_eq_getElem, List.getElem_modify, pow_add]
    · have hkval : k.val ≠ i.val := fun h => hk (Fin.ext h)
      simp [List.get_eq_getElem, List.getElem_modify, hk, hkval, Ne.symm hkval]
  simp_rw [hterm]
  rw [prod_mul_distrib, Fintype.prod_ite_eq']
  rfl

theorem orbit_mul_sum (p : List ℕ) (z : ι → ℝ) :
    (∑ j, z j) * orbit p z =
      orbit (1 :: p) z + ∑ i : Fin p.length, orbit (p.modify i.val (fun a => a + 1)) z := by
  have hselected : (∑ e : Fin p.length ↪ ι, (∑ k, z (e k)) * orbitTerm p z e) =
      ∑ i : Fin p.length, orbit (p.modify i.val (fun a => a + 1)) z := by
    simp_rw [orbit_modify, pow_one]
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    rw [sum_mul]
    apply sum_congr rfl
    intro i _
    ring
  have hnew : (∑ e : Fin p.length ↪ ι,
      (∑ i : {i : ι // i ∉ Set.range e}, z i.val) * orbitTerm p z e) =
      orbit (1 :: p) z := by
    rw [orbit_cons]
    simp_rw [sum_mul, pow_one]
  change (∑ j, z j) * (∑ e : Fin p.length ↪ ι, orbitTerm p z e) = _
  rw [mul_sum]
  calc
    (∑ e : Fin p.length ↪ ι, (∑ j, z j) * orbitTerm p z e) =
        ∑ e : Fin p.length ↪ ι,
          ((∑ k, z (e k)) * orbitTerm p z e +
            (∑ i : {i : ι // i ∉ Set.range e}, z i.val) * orbitTerm p z e) := by
      apply sum_congr rfl
      intro e _
      rw [sum_embedding_range_compl e z]
      ring
    _ = _ := by rw [sum_add_distrib, hselected, hnew]; ring

theorem orbit_raisePart (p : Part) (z : ι → ℝ) :
    ((raisePart p).map (fun q => orbit q z)).sum = (∑ j, z j) * orbit p z := by
  rw [orbit_mul_sum]
  simp only [raisePart, List.map_cons, List.sum_cons, List.map_map]
  rw [orbit_canon]
  have happ : orbit (p ++ [1]) z = orbit (1 :: p) z :=
    orbit_perm (List.perm_append_singleton _ _) z
  rw [happ]
  congr 1
  change ((List.range p.length).map (fun i => orbit (canon (p.modify i (fun a => a + 1))) z)).sum = _
  simp_rw [orbit_canon]
  rw [← List.sum_toFinset _ List.nodup_range]
  have hrange : (List.range p.length).toFinset = Finset.range p.length := by
    ext i
    simp
  rw [hrange]
  exact (Fin.sum_univ_eq_sum_range (fun i => orbit (p.modify i (fun a => a + 1)) z)
    p.length).symm


end

end SharpEighth


/-! ## OptionEmbeddings -/
open scoped BigOperators Classical
open Finset

namespace SharpEighth

noncomputable section

variable {α β : Type*}

def embeddingSome (e : α ↪ β) : α ↪ Option β :=
  e.trans Function.Embedding.some

def embeddingNoneAt (i : α) (e : {j : α // j ≠ i} ↪ β) : α ↪ Option β :=
  (Equiv.optionSubtypeNe i).symm.toEmbedding.trans e.optionMap

@[simp] theorem embeddingSome_apply (e : α ↪ β) (i : α) :
    embeddingSome e i = some (e i) := rfl

@[simp] theorem embeddingNoneAt_self (i : α) (e : {j : α // j ≠ i} ↪ β) :
    embeddingNoneAt i e i = none := by
  simp [embeddingNoneAt, Equiv.optionSubtypeNe_symm_self]

@[simp] theorem embeddingNoneAt_other (i : α) (e : {j : α // j ≠ i} ↪ β)
    (j : α) (h : j ≠ i) :
    embeddingNoneAt i e j = some (e ⟨j, h⟩) := by
  simp [embeddingNoneAt, Equiv.optionSubtypeNe_symm_of_ne h]

def optionEmbeddingFrom : (α ↪ β) ⊕ (Σ i : α, {j : α // j ≠ i} ↪ β) →
    (α ↪ Option β)
  | .inl e => embeddingSome e
  | .inr ⟨i, e⟩ => embeddingNoneAt i e

theorem optionEmbeddingFrom_injective : Function.Injective
    (@optionEmbeddingFrom α β) := by
  intro x y h
  cases x with
  | inl e =>
    cases y with
    | inl f =>
      apply congrArg Sum.inl
      ext i
      exact Option.some.inj (congrArg (fun g : α ↪ Option β => g i) h)
    | inr q =>
      rcases q with ⟨i, f⟩
      have hi := congrArg (fun g : α ↪ Option β => g i) h
      simp [optionEmbeddingFrom] at hi
  | inr q =>
    rcases q with ⟨i, e⟩
    cases y with
    | inl f =>
      have hi := congrArg (fun g : α ↪ Option β => g i) h
      simp [optionEmbeddingFrom] at hi
    | inr r =>
      rcases r with ⟨j, f⟩
      have hij : i = j := by
        by_contra hn
        have hi := congrArg (fun g : α ↪ Option β => g i) h
        simp [optionEmbeddingFrom, embeddingNoneAt_other j f i hn] at hi
      subst j
      have hef : e = f := by
        ext k
        have hk := congrArg (fun g : α ↪ Option β => g k.val) h
        simpa [optionEmbeddingFrom, embeddingNoneAt_other i e k.val k.property,
          embeddingNoneAt_other i f k.val k.property] using hk
      subst f
      rfl

theorem optionEmbeddingFrom_surjective : Function.Surjective
    (@optionEmbeddingFrom α β) := by
  intro f
  by_cases hn : ∃ i, f i = none
  · obtain ⟨i, hi⟩ := hn
    have hs (j : {j : α // j ≠ i}) : (f j.val).isSome := by
      apply Option.isSome_iff_ne_none.mpr
      intro hj
      exact j.property (f.injective (hj.trans hi.symm))
    let e : {j : α // j ≠ i} ↪ β :=
      ⟨fun j => (f j.val).get (hs j), by
        intro j k h
        apply Subtype.ext
        apply f.injective
        have hh := congrArg some h
        simpa only [Option.some_get] using hh⟩
    refine ⟨.inr ⟨i, e⟩, ?_⟩
    apply DFunLike.ext
    intro j
    by_cases hj : j = i
    · subst j
      simpa [optionEmbeddingFrom] using hi.symm
    · change embeddingNoneAt i e j = f j
      rw [embeddingNoneAt_other i e j hj]
      exact Option.some_get (hs ⟨j, hj⟩)
  · have hs (i : α) : (f i).isSome := by
      apply Option.isSome_iff_ne_none.mpr
      intro hi
      exact hn ⟨i, hi⟩
    let e : α ↪ β :=
      ⟨fun i => (f i).get (hs i), by
        intro i j h
        apply f.injective
        have hh := congrArg some h
        simpa only [Option.some_get] using hh⟩
    refine ⟨.inl e, ?_⟩
    apply DFunLike.ext
    intro i
    exact Option.some_get (hs i)

def embeddingOptionEquiv :
    ((α ↪ β) ⊕ (Σ i : α, {j : α // j ≠ i} ↪ β)) ≃ (α ↪ Option β) :=
  Equiv.ofBijective optionEmbeddingFrom
    ⟨optionEmbeddingFrom_injective, optionEmbeddingFrom_surjective⟩

end

end SharpEighth


/-! ## TupleOrbits -/
open scoped BigOperators Classical
open Finset

namespace SharpEighth

noncomputable section

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def tupleOrbit (d : α → ℕ) (z : β → ℝ) : ℝ :=
  ∑ e : α ↪ β, ∏ i, z (e i) ^ d i

theorem tupleOrbit_reindex (d : α → ℕ) (r : γ → ℕ) (z : β → ℝ)
    (a : α ≃ γ) (ha : ∀ i, r (a i) = d i) :
    tupleOrbit d z = tupleOrbit r z := by
  unfold tupleOrbit
  apply Fintype.sum_equiv (Equiv.embeddingCongr a (Equiv.refl β))
  intro e
  apply Fintype.prod_equiv a
  intro i
  simp [ha, Function.Embedding.congr]

theorem tupleOrbit_reindex_codomain (d : α → ℕ) (z : β → ℝ) (w : γ → ℝ)
    (a : β ≃ γ) (ha : ∀ i, w (a i) = z i) :
    tupleOrbit d z = tupleOrbit d w := by
  unfold tupleOrbit
  apply Fintype.sum_equiv (Equiv.embeddingCongr (Equiv.refl α) a)
  intro e
  apply prod_congr rfl
  intro i _
  simp [ha, Function.Embedding.congr]

def optionValue (t : ℝ) (z : β → ℝ) : Option β → ℝ
  | none => t
  | some i => z i

variable [DecidableEq α]

omit [Fintype β] in
theorem option_monomial_noneAt (d : α → ℕ) (t : ℝ) (z : β → ℝ)
    (i : α) (e : {j : α // j ≠ i} ↪ β) :
    (∏ j, optionValue t z (embeddingNoneAt i e j) ^ d j) =
      t ^ d i * ∏ j : {j : α // j ≠ i}, z (e j) ^ d j.val := by
  calc
    _ = ∏ j : Option {j : α // j ≠ i},
        optionValue t z (embeddingNoneAt i e (Equiv.optionSubtypeNe i j)) ^
          d (Equiv.optionSubtypeNe i j) := by
      symm
      apply Fintype.prod_equiv (Equiv.optionSubtypeNe i)
      intro j
      rfl
    _ = _ := by
      rw [Fintype.prod_option]
      have he (j : {j : α // j ≠ i}) : embeddingNoneAt i e j.val = some (e j) :=
        embeddingNoneAt_other i e j.val j.property
      simp only [Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some,
        embeddingNoneAt_self, he, optionValue]

theorem tupleOrbit_option (d : α → ℕ) (t : ℝ) (z : β → ℝ) :
    tupleOrbit d (optionValue t z) = tupleOrbit d z +
      ∑ i : α, t ^ d i * tupleOrbit (fun j : {j : α // j ≠ i} => d j.val) z := by
  unfold tupleOrbit
  calc
    _ = ∑ s : (α ↪ β) ⊕ (Σ i : α, {j : α // j ≠ i} ↪ β),
        ∏ j, optionValue t z (optionEmbeddingFrom s j) ^ d j := by
      symm
      apply Fintype.sum_equiv embeddingOptionEquiv
      intro s
      rfl
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp only [optionEmbeddingFrom, embeddingSome_apply]
      change (∑ e : α ↪ β, ∏ j, z (e j) ^ d j) +
        (∑ s : Σ i : α, {j : α // j ≠ i} ↪ β,
          ∏ j, optionValue t z (embeddingNoneAt s.fst s.snd j) ^ d j) = _
      congr 1
      rw [Fintype.sum_sigma]
      apply sum_congr rfl
      intro i _
      simp only [option_monomial_noneAt, mul_sum]

end

end SharpEighth


/-! ## EraseIndex -/
namespace SharpEighth

def eraseIndexMap {α : Type*} (p : List α) (i : Fin p.length)
    (k : Fin (p.eraseIdx i.val).length) : {j : Fin p.length // j ≠ i} := by
  have hlen := List.length_eraseIdx_add_one i.isLt
  let j : Fin p.length := ⟨if k.val < i.val then k.val else k.val + 1, by
    split_ifs <;> omega⟩
  refine ⟨j, ?_⟩
  intro h
  have hv := congrArg Fin.val h
  dsimp [j] at hv
  split_ifs at hv <;> omega

def eraseIndexInv {α : Type*} (p : List α) (i : Fin p.length)
    (j : {k : Fin p.length // k ≠ i}) : Fin (p.eraseIdx i.val).length := by
  have hlen := List.length_eraseIdx_add_one i.isLt
  have hne : j.val.val ≠ i.val := fun h => j.property (Fin.ext h)
  exact ⟨if j.val.val < i.val then j.val.val else j.val.val - 1, by
    split_ifs <;> omega⟩

def eraseIndexEquiv {α : Type*} (p : List α) (i : Fin p.length) :
    Fin (p.eraseIdx i.val).length ≃ {k : Fin p.length // k ≠ i} where
  toFun := eraseIndexMap p i
  invFun := eraseIndexInv p i
  left_inv k := by
    apply Fin.ext
    simp only [eraseIndexMap, eraseIndexInv]
    split_ifs <;> omega
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have hne : j.val.val ≠ i.val := fun h => j.property (Fin.ext h)
    simp only [eraseIndexMap, eraseIndexInv]
    split_ifs <;> omega

theorem get_eraseIndexEquiv {α : Type*} (p : List α) (i : Fin p.length)
    (k : Fin (p.eraseIdx i.val).length) :
    (p.eraseIdx i.val).get k = p.get (eraseIndexEquiv p i k).val := by
  simp only [List.get_eq_getElem, eraseIndexEquiv, Equiv.coe_fn_mk, eraseIndexMap]
  rw [List.getElem_eraseIdx]
  split_ifs <;> rfl


end SharpEighth


/-! ## Univariate -/
/-!
# An exact univariate majorant for the density-one-eighth Fourier bound

All rational identities below are proved by `ring` and all sign conditions by
kernel-checked arithmetic.  The JSON files and Python generator are untrusted
inputs; no theorem relies on their execution.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace SharpEighth

noncomputable section

def P (x : ℝ) : ℝ :=
    ((206520445606307043664847109 : ℝ) / 36250000000000000000000000000) +
    ((-1953972563767499921566123351 : ℝ) / 217500000000000000000000000000) * (x)^2 +
    ((281404475232491589380339347 : ℝ) / 489375000000000000000000000000) * (x)^4 +
    ((740901741568680334633155809 : ℝ) / 244687500000000000000000000000) * (x)^6 +
    ((-324786196901061211549628347 : ℝ) / 978750000000000000000000000000) * (x)^8 +
    ((796521088493109 : ℝ) / 50000000000000000000) * (x)^10 +
    ((-41161541352553493 : ℝ) / 100000000000000000000000) * (x)^12 +
    ((29617055737416117 : ℝ) / 5000000000000000000000000) * (x)^14 +
    ((-5574570362723033 : ℝ) / 125000000000000000000000000) * (x)^16 +
    ((341703734117989 : ℝ) / 2500000000000000000000000000) * (x)^18

private def R (x : ℝ) : ℝ :=
    ((206520445606307043664847109 : ℝ) / 36250000000000000000000000000) +
    ((524272783508184602412041957 : ℝ) / 217500000000000000000000000000) * (x)^1 +
    ((-73697007332911394620453909 : ℝ) / 244687500000000000000000000000) * (x)^2 +
    ((7562391736704710454561 : ℝ) / 500000000000000000000000000) * (x)^3 +
    ((-124969323185406014753 : ℝ) / 312500000000000000000000000) * (x)^4 +
    ((14586570165401491147 : ℝ) / 2500000000000000000000000000) * (x)^5 +
    ((-55403999893112341 : ℝ) / 1250000000000000000000000000) * (x)^6 +
    ((341703734117989 : ℝ) / 2500000000000000000000000000) * (x)^7

private theorem R_interval_0 (x : ℝ)
    (hlo : (0 : ℝ) ≤ x) (hhi : x ≤ (32 : ℝ)) : 0 ≤ R x := by
  have hl : 0 ≤ x - (0 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (32 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : R x =
      ((206520445606307043664847109 : ℝ) / 1245540515840000000000000000000000000000) * (x - (0 : ℝ))^0 * ((32 : ℝ) - x)^7 +
      ((12725293893863401555554460601 : ℝ) / 3736621547520000000000000000000000000000) * (x - (0 : ℝ))^1 * ((32 : ℝ) - x)^6 +
      ((268205835574242517876593350387 : ℝ) / 33629593927680000000000000000000000000000) * (x - (0 : ℝ))^2 * ((32 : ℝ) - x)^5 +
      ((60670707785217798405812990753 : ℝ) / 6725918785536000000000000000000000000000) * (x - (0 : ℝ))^3 * ((32 : ℝ) - x)^4 +
      ((216330122714245261862938809269 : ℝ) / 33629593927680000000000000000000000000000) * (x - (0 : ℝ))^4 * ((32 : ℝ) - x)^3 +
      ((101727263354931489651901525571 : ℝ) / 33629593927680000000000000000000000000000) * (x - (0 : ℝ))^5 * ((32 : ℝ) - x)^2 +
      ((28402291989937371396822717841 : ℝ) / 33629593927680000000000000000000000000000) * (x - (0 : ℝ))^6 * ((32 : ℝ) - x)^1 +
      ((3502398112788307280370338903 : ℝ) / 33629593927680000000000000000000000000000) * (x - (0 : ℝ))^7 * ((32 : ℝ) - x)^0 := by
    unfold R
    ring
  rw [hid]
  positivity

private theorem R_interval_1 (x : ℝ)
    (hlo : (32 : ℝ) ≤ x) (hhi : x ≤ (64 : ℝ)) : 0 ≤ R x := by
  have hl : 0 ≤ x - (32 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (64 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : R x =
      ((3502398112788307280370338903 : ℝ) / 33629593927680000000000000000000000000000) * (x - (32 : ℝ))^0 * ((64 : ℝ) - x)^7 +
      ((764121540336997426976371363 : ℝ) / 1245540515840000000000000000000000000000) * (x - (32 : ℝ))^1 * ((64 : ℝ) - x)^6 +
      ((55101200949900844441137379331 : ℝ) / 33629593927680000000000000000000000000000) * (x - (32 : ℝ))^2 * ((64 : ℝ) - x)^5 +
      ((77476463019553389350408268821 : ℝ) / 33629593927680000000000000000000000000000) * (x - (32 : ℝ))^3 * ((64 : ℝ) - x)^4 +
      ((58779316180859136717370433573 : ℝ) / 33629593927680000000000000000000000000000) * (x - (32 : ℝ))^4 * ((64 : ℝ) - x)^3 +
      ((35234975443697678910802456403 : ℝ) / 33629593927680000000000000000000000000000) * (x - (32 : ℝ))^5 * ((64 : ℝ) - x)^2 +
      ((893213590715039519761756079 : ℝ) / 2241972928512000000000000000000000000000) * (x - (32 : ℝ))^6 * ((64 : ℝ) - x)^1 +
      ((81397687228313763670118207 : ℝ) / 1345183757107200000000000000000000000000) * (x - (32 : ℝ))^7 * ((64 : ℝ) - x)^0 := by
    unfold R
    ring
  rw [hid]
  positivity

private theorem R_interval_2 (x : ℝ)
    (hlo : (64 : ℝ) ≤ x) (hhi : x ≤ (80 : ℝ)) : 0 ≤ R x := by
  have hl : 0 ≤ x - (64 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (80 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : R x =
      ((81397687228313763670118207 : ℝ) / 10509248102400000000000000000000000000) * (x - (64 : ℝ))^0 * ((80 : ℝ) - x)^7 +
      ((977852731137971104346190583 : ℝ) / 17515413504000000000000000000000000000) * (x - (64 : ℝ))^1 * ((80 : ℝ) - x)^6 +
      ((44667844526104885479109210787 : ℝ) / 262731202560000000000000000000000000000) * (x - (64 : ℝ))^2 * ((80 : ℝ) - x)^5 +
      ((73001019380695460766706624109 : ℝ) / 262731202560000000000000000000000000000) * (x - (64 : ℝ))^3 * ((80 : ℝ) - x)^4 +
      ((13466293203711909259544847793 : ℝ) / 52546240512000000000000000000000000000) * (x - (64 : ℝ))^4 * ((80 : ℝ) - x)^3 +
      ((33969984988393522982766330443 : ℝ) / 262731202560000000000000000000000000000) * (x - (64 : ℝ))^5 * ((80 : ℝ) - x)^2 +
      ((2883417728107409753996217899 : ℝ) / 87577067520000000000000000000000000000) * (x - (64 : ℝ))^6 * ((80 : ℝ) - x)^1 +
      ((1081621066729579516268786063 : ℝ) / 262731202560000000000000000000000000000) * (x - (64 : ℝ))^7 * ((80 : ℝ) - x)^0 := by
    unfold R
    ring
  rw [hid]
  positivity

private theorem R_interval_3 (x : ℝ)
    (hlo : (80 : ℝ) ≤ x) (hhi : x ≤ (96 : ℝ)) : 0 ≤ R x := by
  have hl : 0 ≤ x - (80 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (96 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : R x =
      ((1081621066729579516268786063 : ℝ) / 262731202560000000000000000000000000000) * (x - (80 : ℝ))^0 * ((96 : ℝ) - x)^7 +
      ((1298488349978376793154870237 : ℝ) / 52546240512000000000000000000000000000) * (x - (80 : ℝ))^1 * ((96 : ℝ) - x)^6 +
      ((21023116381811451205480515371 : ℝ) / 262731202560000000000000000000000000000) * (x - (80 : ℝ))^2 * ((96 : ℝ) - x)^5 +
      ((11241418298064838473175988257 : ℝ) / 52546240512000000000000000000000000000) * (x - (80 : ℝ))^3 * ((96 : ℝ) - x)^4 +
      ((114815978644967856887901533869 : ℝ) / 262731202560000000000000000000000000000) * (x - (80 : ℝ))^4 * ((96 : ℝ) - x)^3 +
      ((145770478989063018652402581203 : ℝ) / 262731202560000000000000000000000000000) * (x - (80 : ℝ))^5 * ((96 : ℝ) - x)^2 +
      ((226938295203575898689565379 : ℝ) / 603979776000000000000000000000000000) * (x - (80 : ℝ))^6 * ((96 : ℝ) - x)^1 +
      ((104232845865819667647181771 : ℝ) / 1006632960000000000000000000000000000) * (x - (80 : ℝ))^7 * ((96 : ℝ) - x)^0 := by
    unfold R
    ring
  rw [hid]
  positivity

private theorem R_interval_4 (x : ℝ)
    (hlo : (96 : ℝ) ≤ x) (hhi : x ≤ (128 : ℝ)) : 0 ≤ R x := by
  have hl : 0 ≤ x - (96 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (128 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : R x =
      ((104232845865819667647181771 : ℝ) / 128849018880000000000000000000000000000) * (x - (96 : ℝ))^0 * ((128 : ℝ) - x)^7 +
      ((4297286337510880074876797783 : ℝ) / 386547056640000000000000000000000000000) * (x - (96 : ℝ))^1 * ((128 : ℝ) - x)^6 +
      ((2170930266783271886498846071331 : ℝ) / 33629593927680000000000000000000000000000) * (x - (96 : ℝ))^2 * ((128 : ℝ) - x)^5 +
      ((6882308407099140889790636745973 : ℝ) / 33629593927680000000000000000000000000000) * (x - (96 : ℝ))^3 * ((128 : ℝ) - x)^4 +
      ((12864271669076278107640089712901 : ℝ) / 33629593927680000000000000000000000000000) * (x - (96 : ℝ))^4 * ((128 : ℝ) - x)^3 +
      ((14193526489316255926258974953843 : ℝ) / 33629593927680000000000000000000000000000) * (x - (96 : ℝ))^5 * ((128 : ℝ) - x)^2 +
      ((342860695196512274533119540169 : ℝ) / 1345183757107200000000000000000000000000) * (x - (96 : ℝ))^6 * ((128 : ℝ) - x)^1 +
      ((2188821823893276369804966837959 : ℝ) / 33629593927680000000000000000000000000000) * (x - (96 : ℝ))^7 * ((128 : ℝ) - x)^0 := by
    unfold R
    ring
  rw [hid]
  positivity

private theorem R_tail (x : ℝ) (hx : (128 : ℝ) ≤ x) : 0 ≤ R x := by
  have hshift : 0 ≤ x - (128 : ℝ) := sub_nonneg.mpr hx
  have hid : R x =
    ((2188821823893276369804966837959 : ℝ) / 978750000000000000000000000000) +
    ((421889711708757982831673710093 : ℝ) / 1957500000000000000000000000000) * (x - (128 : ℝ))^1 +
    ((2131269656151908816453942267 : ℝ) / 244687500000000000000000000000) * (x - (128 : ℝ))^2 +
    ((478565818432147264885157 : ℝ) / 2500000000000000000000000000) * (x - (128 : ℝ))^3 +
    ((773079965295804840527 : ℝ) / 312500000000000000000000000) * (x - (128 : ℝ))^4 +
    ((47053979905152702667 : ℝ) / 2500000000000000000000000000) * (x - (128 : ℝ))^5 +
    ((97679272991746731 : ℝ) / 1250000000000000000000000000) * (x - (128 : ℝ))^6 +
    ((341703734117989 : ℝ) / 2500000000000000000000000000) * (x - (128 : ℝ))^7 := by
    unfold R
    ring
  rw [hid]
  positivity

private theorem R_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ R x := by
  by_cases h0 : x ≤ (32 : ℝ)
  · exact R_interval_0 x (by linarith) h0
  by_cases h1 : x ≤ (64 : ℝ)
  · exact R_interval_1 x (by linarith) h1
  by_cases h2 : x ≤ (80 : ℝ)
  · exact R_interval_2 x (by linarith) h2
  by_cases h3 : x ≤ (96 : ℝ)
  · exact R_interval_3 x (by linarith) h3
  by_cases h4 : x ≤ (128 : ℝ)
  · exact R_interval_4 x (by linarith) h4
  exact R_tail x (by linarith)

private def T (x : ℝ) : ℝ :=
    ((27256340148535435681221615703 : ℝ) / 108750000000000000000000000000) +
    ((9131340148535435681221615703 : ℝ) / 163125000000000000000000000000) * (x)^1 +
    ((16584068327445114165763570867 : ℝ) / 1957500000000000000000000000000) * (x)^2 +
    ((-186512441069528577408851171 : ℝ) / 326250000000000000000000000000) * (x)^3 +
    ((-492731073444848368776907903 : ℝ) / 391500000000000000000000000000) * (x)^4 +
    ((-31626985085482128701051227 : ℝ) / 40781250000000000000000000000) * (x)^5 +
    ((-79744711649463171661440821 : ℝ) / 1957500000000000000000000000000) * (x)^6 +
    ((14752760241327701826051 : ℝ) / 250000000000000000000000000) * (x)^7 +
    ((17490704411085026301981 : ℝ) / 2500000000000000000000000000) * (x)^8 +
    ((-295717888519214308671 : ℝ) / 156250000000000000000000000) * (x)^9 +
    ((-672618587141572214933 : ℝ) / 2500000000000000000000000000) * (x)^10 +
    ((38654149636555313841 : ℝ) / 1250000000000000000000000000) * (x)^11 +
    ((477465995406216249 : ℝ) / 100000000000000000000000000) * (x)^12 +
    ((-158011110060505287 : ℝ) / 625000000000000000000000000) * (x)^13 +
    ((-102265406433274957 : ℝ) / 2500000000000000000000000000) * (x)^14 +
    ((1025111202353967 : ℝ) / 1250000000000000000000000000) * (x)^15 +
    ((341703734117989 : ℝ) / 2500000000000000000000000000) * (x)^16

private theorem T_interval_0 (x : ℝ)
    (hlo : (0 : ℝ) ≤ x) (hhi : x ≤ (4 : ℝ)) : 0 ≤ T x := by
  have hl : 0 ≤ x - (0 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (4 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : T x =
      ((27256340148535435681221615703 : ℝ) / 467077693440000000000000000000000000000) * (x - (0 : ℝ))^0 * ((4 : ℝ) - x)^16 +
      ((172669381039748049768551309921 : ℝ) / 175154135040000000000000000000000000000) * (x - (0 : ℝ))^1 * ((4 : ℝ) - x)^15 +
      ((4107100295063823536785654397407 : ℝ) / 525462405120000000000000000000000000000) * (x - (0 : ℝ))^2 * ((4 : ℝ) - x)^14 +
      ((20275567098364549631217304403369 : ℝ) / 525462405120000000000000000000000000000) * (x - (0 : ℝ))^3 * ((4 : ℝ) - x)^13 +
      ((27873270242874159546239813735117 : ℝ) / 210184962048000000000000000000000000000) * (x - (0 : ℝ))^4 * ((4 : ℝ) - x)^12 +
      ((176447763050973948578158645315579 : ℝ) / 525462405120000000000000000000000000000) * (x - (0 : ℝ))^5 * ((4 : ℝ) - x)^11 +
      ((37716252111400346797410302899553 : ℝ) / 58384711680000000000000000000000000000) * (x - (0 : ℝ))^6 * ((4 : ℝ) - x)^10 +
      ((167931766347200586958052061528323 : ℝ) / 175154135040000000000000000000000000000) * (x - (0 : ℝ))^7 * ((4 : ℝ) - x)^9 +
      ((772823993738574824538694693328783 : ℝ) / 700616540160000000000000000000000000000) * (x - (0 : ℝ))^8 * ((4 : ℝ) - x)^8 +
      ((171739940411880535395347742458459 : ℝ) / 175154135040000000000000000000000000000) * (x - (0 : ℝ))^9 * ((4 : ℝ) - x)^7 +
      ((116743535005197409480964430636739 : ℝ) / 175154135040000000000000000000000000000) * (x - (0 : ℝ))^10 * ((4 : ℝ) - x)^6 +
      ((178970786950698933239503423533571 : ℝ) / 525462405120000000000000000000000000000) * (x - (0 : ℝ))^11 * ((4 : ℝ) - x)^5 +
      ((134033281469055440307659341160449 : ℝ) / 1050924810240000000000000000000000000000) * (x - (0 : ℝ))^12 * ((4 : ℝ) - x)^4 +
      ((17697709226409001555048634230481 : ℝ) / 525462405120000000000000000000000000000) * (x - (0 : ℝ))^13 * ((4 : ℝ) - x)^3 +
      ((3098505606857445448819498362943 : ℝ) / 525462405120000000000000000000000000000) * (x - (0 : ℝ))^14 * ((4 : ℝ) - x)^2 +
      ((21379968750722130029556989957 : ℝ) / 35030827008000000000000000000000000000) * (x - (0 : ℝ))^15 * ((4 : ℝ) - x)^1 +
      ((525196466784178470911193071 : ℝ) / 18683107737600000000000000000000000000) * (x - (0 : ℝ))^16 * ((4 : ℝ) - x)^0 := by
    unfold T
    ring
  rw [hid]
  positivity

private theorem T_interval_1 (x : ℝ)
    (hlo : (4 : ℝ) ≤ x) (hhi : x ≤ (5 : ℝ)) : 0 ≤ T x := by
  have hl : 0 ≤ x - (4 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (5 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : T x =
      ((525196466784178470911193071 : ℝ) / 4350000000000000000000000000) * (x - (4 : ℝ))^0 * ((5 : ℝ) - x)^16 +
      ((57399501266904640607121970693 : ℝ) / 32625000000000000000000000000) * (x - (4 : ℝ))^1 * ((5 : ℝ) - x)^15 +
      ((23359492647210107648699800026943 : ℝ) / 1957500000000000000000000000000) * (x - (4 : ℝ))^2 * ((5 : ℝ) - x)^14 +
      ((843409391541551022747674849461 : ℝ) / 16875000000000000000000000000) * (x - (4 : ℝ))^3 * ((5 : ℝ) - x)^13 +
      ((17688139827561615267689081017037 : ℝ) / 122343750000000000000000000000) * (x - (4 : ℝ))^4 * ((5 : ℝ) - x)^12 +
      ((74888512201373901447647899674527 : ℝ) / 244687500000000000000000000000) * (x - (4 : ℝ))^5 * ((5 : ℝ) - x)^11 +
      ((9992241156883183665808157958587 : ℝ) / 20390625000000000000000000000) * (x - (4 : ℝ))^6 * ((5 : ℝ) - x)^10 +
      ((6165778271166881859796230649781 : ℝ) / 10195312500000000000000000000) * (x - (4 : ℝ))^7 * ((5 : ℝ) - x)^9 +
      ((189457062181786480407539435227891 : ℝ) / 326250000000000000000000000000) * (x - (4 : ℝ))^8 * ((5 : ℝ) - x)^8 +
      ((70914688978700242059105630740237 : ℝ) / 163125000000000000000000000000) * (x - (4 : ℝ))^9 * ((5 : ℝ) - x)^7 +
      ((2574141718251943518932625195301 : ℝ) / 10195312500000000000000000000) * (x - (4 : ℝ))^10 * ((5 : ℝ) - x)^6 +
      ((13747055876436605943988631962639 : ℝ) / 122343750000000000000000000000) * (x - (4 : ℝ))^11 * ((5 : ℝ) - x)^5 +
      ((458603806231522296291722800193 : ℝ) / 12234375000000000000000000000) * (x - (4 : ℝ))^12 * ((5 : ℝ) - x)^4 +
      ((2160149883115601326417848967 : ℝ) / 238952636718750000000000000) * (x - (4 : ℝ))^13 * ((5 : ℝ) - x)^3 +
      ((5668111560316053027186504341 : ℝ) / 3823242187500000000000000000) * (x - (4 : ℝ))^14 * ((5 : ℝ) - x)^2 +
      ((11737783368918704108272513 : ℝ) / 79650878906250000000000000) * (x - (4 : ℝ))^15 * ((5 : ℝ) - x)^1 +
      ((44345681970406237767257 : ℝ) / 6637573242187500000000000) * (x - (4 : ℝ))^16 * ((5 : ℝ) - x)^0 := by
    unfold T
    ring
  rw [hid]
  positivity

private theorem T_interval_2 (x : ℝ)
    (hlo : (5 : ℝ) ≤ x) (hhi : x ≤ ((11 : ℝ) / 2)) : 0 ≤ T x := by
  have hl : 0 ≤ x - (5 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ ((11 : ℝ) / 2) - x := sub_nonneg.mpr hhi
  have hid : T x =
      ((1419061823052999608552224 : ℝ) / 3241002559661865234375) * (x - (5 : ℝ))^0 * (((11 : ℝ) / 2) - x)^16 +
      ((55221317784141155382670076 : ℝ) / 9723007678985595703125) * (x - (5 : ℝ))^1 * (((11 : ℝ) / 2) - x)^15 +
      ((7901061323601964543573110821 : ℝ) / 233352184295654296875000) * (x - (5 : ℝ))^2 * (((11 : ℝ) / 2) - x)^14 +
      ((5728429955137656103147969301 : ℝ) / 46670436859130859375000) * (x - (5 : ℝ))^3 * (((11 : ℝ) / 2) - x)^13 +
      ((4505489991657585950014027624501 : ℝ) / 14934539794921875000000000) * (x - (5 : ℝ))^4 * (((11 : ℝ) / 2) - x)^12 +
      ((1268918214709262106167740355009 : ℝ) / 2389526367187500000000000) * (x - (5 : ℝ))^5 * (((11 : ℝ) / 2) - x)^11 +
      ((1100567712717942079232249021507 : ℝ) / 1593017578125000000000000) * (x - (5 : ℝ))^6 * (((11 : ℝ) / 2) - x)^10 +
      ((216758598928418193523061629020679 : ℝ) / 318603515625000000000000000) * (x - (5 : ℝ))^7 * (((11 : ℝ) / 2) - x)^9 +
      ((668342897473935284842920191459533 : ℝ) / 1274414062500000000000000000) * (x - (5 : ℝ))^8 * (((11 : ℝ) / 2) - x)^8 +
      ((54048484580470523858920374554483 : ℝ) / 159301757812500000000000000) * (x - (5 : ℝ))^9 * (((11 : ℝ) / 2) - x)^7 +
      ((262492871900108881583027629096343 : ℝ) / 1274414062500000000000000000) * (x - (5 : ℝ))^10 * (((11 : ℝ) / 2) - x)^6 +
      ((474852034476071316249453657443207 : ℝ) / 3823242187500000000000000000) * (x - (5 : ℝ))^11 * (((11 : ℝ) / 2) - x)^5 +
      ((2074840630480360024104451885245167 : ℝ) / 30585937500000000000000000000) * (x - (5 : ℝ))^12 * (((11 : ℝ) / 2) - x)^4 +
      ((1770712073258869247377704106109743 : ℝ) / 61171875000000000000000000000) * (x - (5 : ℝ))^13 * (((11 : ℝ) / 2) - x)^3 +
      ((4176800095563323750173290653771203 : ℝ) / 489375000000000000000000000000) * (x - (5 : ℝ))^14 * (((11 : ℝ) / 2) - x)^2 +
      ((82651561527517626726727420975327 : ℝ) / 54375000000000000000000000000) * (x - (5 : ℝ))^15 * (((11 : ℝ) / 2) - x)^1 +
      ((8898502484683941587391910191553 : ℝ) / 72500000000000000000000000000) * (x - (5 : ℝ))^16 * (((11 : ℝ) / 2) - x)^0 := by
    unfold T
    ring
  rw [hid]
  positivity

private theorem T_interval_3 (x : ℝ)
    (hlo : ((11 : ℝ) / 2) ≤ x) (hhi : x ≤ (6 : ℝ)) : 0 ≤ T x := by
  have hl : 0 ≤ x - ((11 : ℝ) / 2) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (6 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : T x =
      ((8898502484683941587391910191553 : ℝ) / 72500000000000000000000000000) * (x - ((11 : ℝ) / 2))^0 * ((6 : ℝ) - x)^16 +
      ((26182499620979394274135684724389 : ℝ) / 10875000000000000000000000000) * (x - ((11 : ℝ) / 2))^1 * ((6 : ℝ) - x)^15 +
      ((10692026533509535277106676011064633 : ℝ) / 489375000000000000000000000000) * (x - ((11 : ℝ) / 2))^2 * ((6 : ℝ) - x)^14 +
      ((37157824157829922250957636476589 : ℝ) / 305859375000000000000000000) * (x - ((11 : ℝ) / 2))^3 * ((6 : ℝ) - x)^13 +
      ((11333453319144445442217506508287959 : ℝ) / 24468750000000000000000000000) * (x - ((11 : ℝ) / 2))^4 * ((6 : ℝ) - x)^12 +
      ((39296353971150013176608067913182499 : ℝ) / 30585937500000000000000000000) * (x - ((11 : ℝ) / 2))^5 * ((6 : ℝ) - x)^11 +
      ((27372395858451693986013268234985963 : ℝ) / 10195312500000000000000000000) * (x - ((11 : ℝ) / 2))^6 * ((6 : ℝ) - x)^10 +
      ((5500594206049667520941893763948449 : ℝ) / 1274414062500000000000000000) * (x - ((11 : ℝ) / 2))^7 * ((6 : ℝ) - x)^9 +
      ((13764912068059246249608676668563237 : ℝ) / 2548828125000000000000000000) * (x - ((11 : ℝ) / 2))^8 * ((6 : ℝ) - x)^8 +
      ((3365495407199516794935172655966183 : ℝ) / 637207031250000000000000000) * (x - ((11 : ℝ) / 2))^9 * ((6 : ℝ) - x)^7 +
      ((2566281063654766155152314561567493 : ℝ) / 637207031250000000000000000) * (x - ((11 : ℝ) / 2))^10 * ((6 : ℝ) - x)^6 +
      ((113309277723879862082129748892909 : ℝ) / 47790527343750000000000000) * (x - ((11 : ℝ) / 2))^11 * ((6 : ℝ) - x)^5 +
      ((17420213164485730386889748465173 : ℝ) / 16479492187500000000000000) * (x - ((11 : ℝ) / 2))^12 * ((6 : ℝ) - x)^4 +
      ((41247130752561476695036409143727 : ℝ) / 119476318359375000000000000) * (x - ((11 : ℝ) / 2))^13 * ((6 : ℝ) - x)^3 +
      ((9310206177340428671068429924087 : ℝ) / 119476318359375000000000000) * (x - ((11 : ℝ) / 2))^14 * ((6 : ℝ) - x)^2 +
      ((75124525456837754945183967 : ℝ) / 6914138793945312500000) * (x - ((11 : ℝ) / 2))^15 * ((6 : ℝ) - x)^1 +
      ((46812086387768845699289969 : ℝ) / 66375732421875000000000) * (x - ((11 : ℝ) / 2))^16 * ((6 : ℝ) - x)^0 := by
    unfold T
    ring
  rw [hid]
  positivity

private theorem T_interval_4 (x : ℝ)
    (hlo : (6 : ℝ) ≤ x) (hhi : x ≤ (7 : ℝ)) : 0 ≤ T x := by
  have hl : 0 ≤ x - (6 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (7 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : T x =
      ((46812086387768845699289969 : ℝ) / 4350000000000000000000000000) * (x - (6 : ℝ))^0 * ((7 : ℝ) - x)^16 +
      ((83811381025168718606081911 : ℝ) / 453125000000000000000000000) * (x - (6 : ℝ))^1 * ((7 : ℝ) - x)^15 +
      ((2852464664177568558235828488487 : ℝ) / 1957500000000000000000000000000) * (x - (6 : ℝ))^2 * ((7 : ℝ) - x)^14 +
      ((68335541377826876781660669193 : ℝ) / 9787500000000000000000000000) * (x - (6 : ℝ))^3 * ((7 : ℝ) - x)^13 +
      ((11134602585110953740877363674191 : ℝ) / 489375000000000000000000000000) * (x - (6 : ℝ))^4 * ((7 : ℝ) - x)^12 +
      ((2613430945631129303547030273619 : ℝ) / 48937500000000000000000000000) * (x - (6 : ℝ))^5 * ((7 : ℝ) - x)^11 +
      ((237548632955496811348341743707 : ℝ) / 2548828125000000000000000000) * (x - (6 : ℝ))^6 * ((7 : ℝ) - x)^10 +
      ((39189032481399666282816659371 : ℝ) / 318603515625000000000000000) * (x - (6 : ℝ))^7 * ((7 : ℝ) - x)^9 +
      ((8061361148620019565960794475251 : ℝ) / 65250000000000000000000000000) * (x - (6 : ℝ))^8 * ((7 : ℝ) - x)^8 +
      ((15362874579002726824538262957749 : ℝ) / 163125000000000000000000000000) * (x - (6 : ℝ))^9 * ((7 : ℝ) - x)^7 +
      ((4390032059679488924332851032731 : ℝ) / 81562500000000000000000000000) * (x - (6 : ℝ))^10 * ((7 : ℝ) - x)^6 +
      ((1377499642355457241337818376681 : ℝ) / 61171875000000000000000000000) * (x - (6 : ℝ))^11 * ((7 : ℝ) - x)^5 +
      ((405270498847690584636583829167 : ℝ) / 61171875000000000000000000000) * (x - (6 : ℝ))^12 * ((7 : ℝ) - x)^4 +
      ((7861997007888457201686025099 : ℝ) / 6117187500000000000000000000) * (x - (6 : ℝ))^13 * ((7 : ℝ) - x)^3 +
      ((2291473845170417568911107187 : ℝ) / 15292968750000000000000000000) * (x - (6 : ℝ))^14 * ((7 : ℝ) - x)^2 +
      ((646000681536968606445989 : ℝ) / 63720703125000000000000000) * (x - (6 : ℝ))^15 * ((7 : ℝ) - x)^1 +
      ((616026418134341254283 : ℝ) / 1062011718750000000000000) * (x - (6 : ℝ))^16 * ((7 : ℝ) - x)^0 := by
    unfold T
    ring
  rw [hid]
  positivity

private theorem T_interval_5 (x : ℝ)
    (hlo : (7 : ℝ) ≤ x) (hhi : x ≤ (8 : ℝ)) : 0 ≤ T x := by
  have hl : 0 ≤ x - (7 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (8 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : T x =
      ((616026418134341254283 : ℝ) / 1062011718750000000000000) * (x - (7 : ℝ))^0 * ((8 : ℝ) - x)^16 +
      ((536770041280966601777371 : ℝ) / 63720703125000000000000000) * (x - (7 : ℝ))^1 * ((8 : ℝ) - x)^15 +
      ((1898243540248810352104082387 : ℝ) / 15292968750000000000000000000) * (x - (7 : ℝ))^2 * ((8 : ℝ) - x)^14 +
      ((38261005465613472783690286577 : ℝ) / 30585937500000000000000000000) * (x - (7 : ℝ))^3 * ((8 : ℝ) - x)^13 +
      ((473420917255784792071852702099 : ℝ) / 61171875000000000000000000000) * (x - (7 : ℝ))^4 * ((8 : ℝ) - x)^12 +
      ((1926029141123446923106038979823 : ℝ) / 61171875000000000000000000000) * (x - (7 : ℝ))^5 * ((8 : ℝ) - x)^11 +
      ((7317333217024128765729857698483 : ℝ) / 81562500000000000000000000000) * (x - (7 : ℝ))^6 * ((8 : ℝ) - x)^10 +
      ((30442153373146724546460565779683 : ℝ) / 163125000000000000000000000000) * (x - (7 : ℝ))^7 * ((8 : ℝ) - x)^9 +
      ((94801140948452445239947366711483 : ℝ) / 326250000000000000000000000000) * (x - (7 : ℝ))^8 * ((8 : ℝ) - x)^8 +
      ((6996565538889384090612588937141 : ℝ) / 20390625000000000000000000000) * (x - (7 : ℝ))^9 * ((8 : ℝ) - x)^7 +
      ((2095474302781241442674078570711 : ℝ) / 6796875000000000000000000000) * (x - (7 : ℝ))^10 * ((8 : ℝ) - x)^6 +
      ((51267804226760268678574779314177 : ℝ) / 244687500000000000000000000000) * (x - (7 : ℝ))^11 * ((8 : ℝ) - x)^5 +
      ((51837069322627548643024231139603 : ℝ) / 489375000000000000000000000000) * (x - (7 : ℝ))^12 * ((8 : ℝ) - x)^4 +
      ((9443622493368678628471509889987 : ℝ) / 244687500000000000000000000000) * (x - (7 : ℝ))^13 * ((8 : ℝ) - x)^3 +
      ((18737116018081424613486809888023 : ℝ) / 1957500000000000000000000000000) * (x - (7 : ℝ))^14 * ((8 : ℝ) - x)^2 +
      ((78573689492805807772654659343 : ℝ) / 54375000000000000000000000000) * (x - (7 : ℝ))^15 * ((8 : ℝ) - x)^1 +
      ((3627960022562123259507376429 : ℝ) / 36250000000000000000000000000) * (x - (7 : ℝ))^16 * ((8 : ℝ) - x)^0 := by
    unfold T
    ring
  rw [hid]
  positivity

private theorem T_interval_6 (x : ℝ)
    (hlo : (8 : ℝ) ≤ x) (hhi : x ≤ (9 : ℝ)) : 0 ≤ T x := by
  have hl : 0 ≤ x - (8 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (9 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : T x =
      ((3627960022562123259507376429 : ℝ) / 36250000000000000000000000000) * (x - (8 : ℝ))^0 * ((9 : ℝ) - x)^16 +
      ((95568391590176108683699409249 : ℝ) / 54375000000000000000000000000) * (x - (8 : ℝ))^1 * ((9 : ℝ) - x)^15 +
      ((27914255150661387105450974837263 : ℝ) / 1957500000000000000000000000000) * (x - (8 : ℝ))^2 * ((9 : ℝ) - x)^14 +
      ((1195967000744271599718488398123 : ℝ) / 16875000000000000000000000000) * (x - (8 : ℝ))^3 * ((9 : ℝ) - x)^13 +
      ((29498958399542383233794649590543 : ℝ) / 122343750000000000000000000000) * (x - (8 : ℝ))^4 * ((9 : ℝ) - x)^12 +
      ((145391582709518904233399359939799 : ℝ) / 244687500000000000000000000000) * (x - (8 : ℝ))^5 * ((9 : ℝ) - x)^11 +
      ((1859214645342931890571873223219 : ℝ) / 1699218750000000000000000000) * (x - (8 : ℝ))^6 * ((9 : ℝ) - x)^10 +
      ((7798935173266716712046990423449 : ℝ) / 5097656250000000000000000000) * (x - (8 : ℝ))^7 * ((9 : ℝ) - x)^9 +
      ((532733402694114458301983249637307 : ℝ) / 326250000000000000000000000000) * (x - (8 : ℝ))^8 * ((9 : ℝ) - x)^8 +
      ((43212215996002333534148647562737 : ℝ) / 32625000000000000000000000000) * (x - (8 : ℝ))^9 * ((9 : ℝ) - x)^7 +
      ((32800415893217508849646742696201 : ℝ) / 40781250000000000000000000000) * (x - (8 : ℝ))^10 * ((9 : ℝ) - x)^6 +
      ((43430682886191595893420214544851 : ℝ) / 122343750000000000000000000000) * (x - (8 : ℝ))^11 * ((9 : ℝ) - x)^5 +
      ((6602762127695332280448535800319 : ℝ) / 61171875000000000000000000000) * (x - (8 : ℝ))^12 * ((9 : ℝ) - x)^4 +
      ((19494233331377396203306179361 : ℝ) / 955810546875000000000000000) * (x - (8 : ℝ))^13 * ((9 : ℝ) - x)^3 +
      ((7173922500227854627663794719 : ℝ) / 3823242187500000000000000000) * (x - (8 : ℝ))^14 * ((9 : ℝ) - x)^2 +
      ((384827051518800378308263 : ℝ) / 15930175781250000000000000) * (x - (8 : ℝ))^15 * ((9 : ℝ) - x)^1 +
      ((159977077876479232291 : ℝ) / 265502929687500000000000) * (x - (8 : ℝ))^16 * ((9 : ℝ) - x)^0 := by
    unfold T
    ring
  rw [hid]
  positivity

private theorem T_interval_7 (x : ℝ)
    (hlo : (9 : ℝ) ≤ x) (hhi : x ≤ ((19 : ℝ) / 2)) : 0 ≤ T x := by
  have hl : 0 ≤ x - (9 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ ((19 : ℝ) / 2) - x := sub_nonneg.mpr hhi
  have hid : T x =
      ((5119266492047335433312 : ℝ) / 129640102386474609375) * (x - (9 : ℝ))^0 * (((19 : ℝ) / 2) - x)^16 +
      ((303627731061839242759268 : ℝ) / 1944601535797119140625) * (x - (9 : ℝ))^1 * (((19 : ℝ) / 2) - x)^15 +
      ((5505753858959815562524186319 : ℝ) / 233352184295654296875000) * (x - (9 : ℝ))^2 * (((19 : ℝ) / 2) - x)^14 +
      ((85440262805743227018297730177 : ℝ) / 233352184295654296875000) * (x - (9 : ℝ))^3 * (((19 : ℝ) / 2) - x)^13 +
      ((39231963233449512796405112333839 : ℝ) / 14934539794921875000000000) * (x - (9 : ℝ))^4 * (((19 : ℝ) / 2) - x)^12 +
      ((27517520536633651989420279508013 : ℝ) / 2389526367187500000000000) * (x - (9 : ℝ))^5 * (((19 : ℝ) / 2) - x)^11 +
      ((38221448908364636703524811144363 : ℝ) / 1106262207031250000000000) * (x - (9 : ℝ))^6 * (((19 : ℝ) / 2) - x)^10 +
      ((23947770942550245164649795936526759 : ℝ) / 318603515625000000000000000) * (x - (9 : ℝ))^7 * (((19 : ℝ) / 2) - x)^9 +
      ((31195380713681858061900487269735497 : ℝ) / 254882812500000000000000000) * (x - (9 : ℝ))^8 * (((19 : ℝ) / 2) - x)^8 +
      ((4830346141856897199032769127514677 : ℝ) / 31860351562500000000000000) * (x - (9 : ℝ))^9 * (((19 : ℝ) / 2) - x)^7 +
      ((61009824849863335200749783061651253 : ℝ) / 424804687500000000000000000) * (x - (9 : ℝ))^10 * (((19 : ℝ) / 2) - x)^6 +
      ((395923332509486701354576573497588851 : ℝ) / 3823242187500000000000000000) * (x - (9 : ℝ))^11 * (((19 : ℝ) / 2) - x)^5 +
      ((342304645885571419485041994367585459 : ℝ) / 6117187500000000000000000000) * (x - (9 : ℝ))^12 * (((19 : ℝ) / 2) - x)^4 +
      ((1344282779265340458567711499245059569 : ℝ) / 61171875000000000000000000000) * (x - (9 : ℝ))^13 * (((19 : ℝ) / 2) - x)^3 +
      ((2901781017485268325524050417619264811 : ℝ) / 489375000000000000000000000000) * (x - (9 : ℝ))^14 * (((19 : ℝ) / 2) - x)^2 +
      ((221409190643734266983055242828969 : ℝ) / 225000000000000000000000000) * (x - (9 : ℝ))^15 * (((19 : ℝ) / 2) - x)^1 +
      ((26372288810842266839804620140691 : ℝ) / 348000000000000000000000000) * (x - (9 : ℝ))^16 * (((19 : ℝ) / 2) - x)^0 := by
    unfold T
    ring
  rw [hid]
  positivity

private theorem T_interval_8 (x : ℝ)
    (hlo : ((19 : ℝ) / 2) ≤ x) (hhi : x ≤ (10 : ℝ)) : 0 ≤ T x := by
  have hl : 0 ≤ x - ((19 : ℝ) / 2) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (10 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : T x =
      ((26372288810842266839804620140691 : ℝ) / 348000000000000000000000000) * (x - ((19 : ℝ) / 2))^0 * ((10 : ℝ) - x)^16 +
      ((9402506757837066361374170042374499 : ℝ) / 6525000000000000000000000000) * (x - ((19 : ℝ) / 2))^1 * ((10 : ℝ) - x)^15 +
      ((215728492251728880060269462689498709 : ℝ) / 16875000000000000000000000000) * (x - ((19 : ℝ) / 2))^2 * ((10 : ℝ) - x)^14 +
      ((2148983131919988602992491391341816041 : ℝ) / 30585937500000000000000000000) * (x - ((19 : ℝ) / 2))^3 * ((10 : ℝ) - x)^13 +
      ((32767627106459801013156139251048928643 : ℝ) / 122343750000000000000000000000) * (x - ((19 : ℝ) / 2))^4 * ((10 : ℝ) - x)^12 +
      ((4594511926379815334772846647028008447 : ℝ) / 6117187500000000000000000000) * (x - ((19 : ℝ) / 2))^5 * ((10 : ℝ) - x)^11 +
      ((3269070273695725143361051820738305783 : ℝ) / 2039062500000000000000000000) * (x - ((19 : ℝ) / 2))^6 * ((10 : ℝ) - x)^10 +
      ((3387041993215671614979156365619791371 : ℝ) / 1274414062500000000000000000) * (x - ((19 : ℝ) / 2))^7 * ((10 : ℝ) - x)^9 +
      ((8815703065795982712706847846822451557 : ℝ) / 2548828125000000000000000000) * (x - ((19 : ℝ) / 2))^8 * ((10 : ℝ) - x)^8 +
      ((2259540330273316465623594110580375383 : ℝ) / 637207031250000000000000000) * (x - ((19 : ℝ) / 2))^9 * ((10 : ℝ) - x)^7 +
      ((1819244255720706553962938359842769501 : ℝ) / 637207031250000000000000000) * (x - ((19 : ℝ) / 2))^10 * ((10 : ℝ) - x)^6 +
      ((426894055141754325888664668549465119 : ℝ) / 238952636718750000000000000) * (x - ((19 : ℝ) / 2))^11 * ((10 : ℝ) - x)^5 +
      ((407106487856014151993506493077183169 : ℝ) / 477905273437500000000000000) * (x - ((19 : ℝ) / 2))^12 * ((10 : ℝ) - x)^4 +
      ((35753793977244001986935179227531431 : ℝ) / 119476318359375000000000000) * (x - ((19 : ℝ) / 2))^13 * ((10 : ℝ) - x)^3 +
      ((8728002969931817882751456087704527 : ℝ) / 119476318359375000000000000) * (x - ((19 : ℝ) / 2))^14 * ((10 : ℝ) - x)^2 +
      ((9187182008542374187012362772901 : ℝ) / 829696655273437500000000) * (x - ((19 : ℝ) / 2))^15 * ((10 : ℝ) - x)^1 +
      ((434309895600952303993098653291 : ℝ) / 553131103515625000000000) * (x - ((19 : ℝ) / 2))^16 * ((10 : ℝ) - x)^0 := by
    unfold T
    ring
  rw [hid]
  positivity

private theorem T_interval_9 (x : ℝ)
    (hlo : (10 : ℝ) ≤ x) (hhi : x ≤ (12 : ℝ)) : 0 ≤ T x := by
  have hl : 0 ≤ x - (10 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (12 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : T x =
      ((434309895600952303993098653291 : ℝ) / 2375680000000000000000000000000000) * (x - (10 : ℝ))^0 * ((12 : ℝ) - x)^16 +
      ((3842114859486194932780596825829 : ℝ) / 890880000000000000000000000000000) * (x - (10 : ℝ))^1 * ((12 : ℝ) - x)^15 +
      ((1512162318705975889538572059157327 : ℝ) / 32071680000000000000000000000000000) * (x - (10 : ℝ))^2 * ((12 : ℝ) - x)^14 +
      ((5089591760948405222835577275020833 : ℝ) / 16035840000000000000000000000000000) * (x - (10 : ℝ))^3 * ((12 : ℝ) - x)^13 +
      ((47262445767114444916650389763480791 : ℝ) / 32071680000000000000000000000000000) * (x - (10 : ℝ))^4 * ((12 : ℝ) - x)^12 +
      ((10038625300598426050762852076809747 : ℝ) / 2004480000000000000000000000000000) * (x - (10 : ℝ))^5 * ((12 : ℝ) - x)^11 +
      ((45952373000029282724043042666976487 : ℝ) / 3563520000000000000000000000000000) * (x - (10 : ℝ))^6 * ((12 : ℝ) - x)^10 +
      ((137256706609123351073910954214587769 : ℝ) / 5345280000000000000000000000000000) * (x - (10 : ℝ))^7 * ((12 : ℝ) - x)^9 +
      ((106867895608089006143499369227168027 : ℝ) / 2672640000000000000000000000000000) * (x - (10 : ℝ))^8 * ((12 : ℝ) - x)^8 +
      ((130635253116396365691755596821142667 : ℝ) / 2672640000000000000000000000000000) * (x - (10 : ℝ))^9 * ((12 : ℝ) - x)^7 +
      ((99995842743056398087486765549079179 : ℝ) / 2138112000000000000000000000000000) * (x - (10 : ℝ))^10 * ((12 : ℝ) - x)^6 +
      ((111200536010301293791022348241979531 : ℝ) / 3207168000000000000000000000000000) * (x - (10 : ℝ))^11 * ((12 : ℝ) - x)^5 +
      ((626424612422640233634462794061755057 : ℝ) / 32071680000000000000000000000000000) * (x - (10 : ℝ))^12 * ((12 : ℝ) - x)^4 +
      ((1117660922507442843998049711712103 : ℝ) / 138240000000000000000000000000000) * (x - (10 : ℝ))^13 * ((12 : ℝ) - x)^3 +
      ((74399734699103433160594743622456621 : ℝ) / 32071680000000000000000000000000000) * (x - (10 : ℝ))^14 * ((12 : ℝ) - x)^2 +
      ((440811499459655299501079698660627 : ℝ) / 1069056000000000000000000000000000) * (x - (10 : ℝ))^15 * ((12 : ℝ) - x)^1 +
      ((9753393707653825065668031016063 : ℝ) / 285081600000000000000000000000000) * (x - (10 : ℝ))^16 * ((12 : ℝ) - x)^0 := by
    unfold T
    ring
  rw [hid]
  positivity

private theorem T_interval_10 (x : ℝ)
    (hlo : (12 : ℝ) ≤ x) (hhi : x ≤ (16 : ℝ)) : 0 ≤ T x := by
  have hl : 0 ≤ x - (12 : ℝ) := sub_nonneg.mpr hlo
  have hr : 0 ≤ (16 : ℝ) - x := sub_nonneg.mpr hhi
  have hid : T x =
      ((9753393707653825065668031016063 : ℝ) / 18683107737600000000000000000000000000) * (x - (12 : ℝ))^0 * ((16 : ℝ) - x)^16 +
      ((436993934229188956409043092785043 : ℝ) / 35030827008000000000000000000000000000) * (x - (12 : ℝ))^1 * ((16 : ℝ) - x)^15 +
      ((73111306433821042367032389139447021 : ℝ) / 525462405120000000000000000000000000000) * (x - (12 : ℝ))^2 * ((16 : ℝ) - x)^14 +
      ((101064371731613190375481925395033063 : ℝ) / 105092481024000000000000000000000000000) * (x - (12 : ℝ))^3 * ((16 : ℝ) - x)^13 +
      ((167086146543900033584430792939479057 : ℝ) / 36238786560000000000000000000000000000) * (x - (12 : ℝ))^4 * ((16 : ℝ) - x)^12 +
      ((8545058725389661176664284382866297757 : ℝ) / 525462405120000000000000000000000000000) * (x - (12 : ℝ))^5 * ((16 : ℝ) - x)^11 +
      ((7645837258894517954281301364087568453 : ℝ) / 175154135040000000000000000000000000000) * (x - (12 : ℝ))^6 * ((16 : ℝ) - x)^10 +
      ((15935485847065324569807995146969730681 : ℝ) / 175154135040000000000000000000000000000) * (x - (12 : ℝ))^7 * ((16 : ℝ) - x)^9 +
      ((20851945086405263649115229780984934907 : ℝ) / 140123308032000000000000000000000000000) * (x - (12 : ℝ))^8 * ((16 : ℝ) - x)^8 +
      ((1157697841129074026044304536904646937 : ℝ) / 6039797760000000000000000000000000000) * (x - (12 : ℝ))^9 * ((16 : ℝ) - x)^7 +
      ((11315077585305268312576195151483555419 : ℝ) / 58384711680000000000000000000000000000) * (x - (12 : ℝ))^10 * ((16 : ℝ) - x)^6 +
      ((15996337042391123338656611729906711261 : ℝ) / 105092481024000000000000000000000000000) * (x - (12 : ℝ))^11 * ((16 : ℝ) - x)^5 +
      ((95681907300445775548631558125781560933 : ℝ) / 1050924810240000000000000000000000000000) * (x - (12 : ℝ))^12 * ((16 : ℝ) - x)^4 +
      ((4214032943079206971690957497825132379 : ℝ) / 105092481024000000000000000000000000000) * (x - (12 : ℝ))^13 * ((16 : ℝ) - x)^3 +
      ((6444425118245683934411584583323084897 : ℝ) / 525462405120000000000000000000000000000) * (x - (12 : ℝ))^14 * ((16 : ℝ) - x)^2 +
      ((81538968061187220726139306881948079 : ℝ) / 35030827008000000000000000000000000000) * (x - (12 : ℝ))^15 * ((16 : ℝ) - x)^1 +
      ((3858561009428672891488297592815631 : ℝ) / 18683107737600000000000000000000000000) * (x - (12 : ℝ))^16 * ((16 : ℝ) - x)^0 := by
    unfold T
    ring
  rw [hid]
  positivity

private theorem T_tail (x : ℝ) (hx : (16 : ℝ) ≤ x) : 0 ≤ T x := by
  have hshift : 0 ≤ x - (16 : ℝ) := sub_nonneg.mpr hx
  have hid : T x =
    ((3858561009428672891488297592815631 : ℝ) / 4350000000000000000000000000) +
    ((34217862221672966018509620902520851 : ℝ) / 32625000000000000000000000000) * (x - (16 : ℝ))^1 +
    ((1120800711300330279803244910637521747 : ℝ) / 1957500000000000000000000000000) * (x - (16 : ℝ))^2 +
    ((62510339257302734190778142715645437 : ℝ) / 326250000000000000000000000000) * (x - (16 : ℝ))^3 +
    ((86133297684942801438387646850773381 : ℝ) / 1957500000000000000000000000000) * (x - (16 : ℝ))^4 +
    ((299968355065556678543198291819803 : ℝ) / 40781250000000000000000000000) * (x - (16 : ℝ))^5 +
    ((1812982984392060532606336837079467 : ℝ) / 1957500000000000000000000000000) * (x - (16 : ℝ))^6 +
    ((22409764684646367533824788547 : ℝ) / 250000000000000000000000000) * (x - (16 : ℝ))^7 +
    ((674215493190117716836565157 : ℝ) / 100000000000000000000000000) * (x - (16 : ℝ))^8 +
    ((12361638772840524876267203 : ℝ) / 31250000000000000000000000) * (x - (16 : ℝ))^9 +
    ((45129888293086032788608203 : ℝ) / 2500000000000000000000000000) * (x - (16 : ℝ))^10 +
    ((792873546570560448038161 : ℝ) / 1250000000000000000000000000) * (x - (16 : ℝ))^11 +
    ((42075945562116203375569 : ℝ) / 2500000000000000000000000000) * (x - (16 : ℝ))^12 +
    ((203839209981933025761 : ℝ) / 625000000000000000000000000) * (x - (16 : ℝ))^13 +
    ((10886926682801251283 : ℝ) / 2500000000000000000000000000) * (x - (16 : ℝ))^14 +
    ((44763189169456559 : ℝ) / 1250000000000000000000000000) * (x - (16 : ℝ))^15 +
    ((341703734117989 : ℝ) / 2500000000000000000000000000) * (x - (16 : ℝ))^16 := by
    unfold T
    ring
  rw [hid]
  positivity

private theorem T_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ T x := by
  by_cases h0 : x ≤ (4 : ℝ)
  · exact T_interval_0 x (by linarith) h0
  by_cases h1 : x ≤ (5 : ℝ)
  · exact T_interval_1 x (by linarith) h1
  by_cases h2 : x ≤ ((11 : ℝ) / 2)
  · exact T_interval_2 x (by linarith) h2
  by_cases h3 : x ≤ (6 : ℝ)
  · exact T_interval_3 x (by linarith) h3
  by_cases h4 : x ≤ (7 : ℝ)
  · exact T_interval_4 x (by linarith) h4
  by_cases h5 : x ≤ (8 : ℝ)
  · exact T_interval_5 x (by linarith) h5
  by_cases h6 : x ≤ (9 : ℝ)
  · exact T_interval_6 x (by linarith) h6
  by_cases h7 : x ≤ ((19 : ℝ) / 2)
  · exact T_interval_7 x (by linarith) h7
  by_cases h8 : x ≤ (10 : ℝ)
  · exact T_interval_8 x (by linarith) h8
  by_cases h9 : x ≤ (12 : ℝ)
  · exact T_interval_9 x (by linarith) h9
  by_cases h10 : x ≤ (16 : ℝ)
  · exact T_interval_10 x (by linarith) h10
  exact T_tail x (by linarith)

theorem P_nonneg (x : ℝ) : 0 ≤ P x := by
  have hfac : P x = (x^2 - 1)^2 * R (x^2) := by
    unfold P R
    ring
  rw [hfac]
  exact mul_nonneg (sq_nonneg _) (R_nonneg (x^2) (sq_nonneg x))

theorem P_affine_lower (x : ℝ) (hx : 0 ≤ x) : x - 9/4 ≤ P x := by
  have hfac : P x - x + 9/4 = (x - 3)^2 * T x := by
    unfold P T
    ring
  have hprod : 0 ≤ (x - 3)^2 * T x :=
    mul_nonneg (sq_nonneg _) (T_nonneg x hx)
  linarith

theorem P_neg (x : ℝ) : P (-x) = P x := by
  unfold P
  ring

/-- The degree-eighteen polynomial dominates the absolute-value hinge globally. -/
theorem majorant (x : ℝ) : max 0 (|x| - 9/4) ≤ P x := by
  apply max_le (P_nonneg x)
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    exact P_affine_lower x hx
  · rw [abs_of_neg (lt_of_not_ge hx)]
    have h := P_affine_lower (-x) (by linarith)
    rwa [P_neg] at h

end
end SharpEighth


/-! ## CertificateData -/
namespace SharpEighth

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pCoeffs : List ℚ := [(206520445606307043664847109/36250000000000000000000000000 : ℚ),(-1953972563767499921566123351/217500000000000000000000000000 : ℚ),(281404475232491589380339347/489375000000000000000000000000 : ℚ),(740901741568680334633155809/244687500000000000000000000000 : ℚ),(-324786196901061211549628347/978750000000000000000000000000 : ℚ),(796521088493109/50000000000000000000 : ℚ),(-41161541352553493/100000000000000000000000 : ℚ),(29617055737416117/5000000000000000000000000 : ℚ),(-5574570362723033/125000000000000000000000000 : ℚ),(341703734117989/2500000000000000000000000000 : ℚ)]
def pCoeff (j : ℕ) : ℚ := pCoeffs[j]?.getD 0

def momentPoly : ℕ → SymPoly
  | 0 => [([],(1 : ℚ))]
  | 1 => [([1],(1 : ℚ))]
  | 2 => [([2],(1 : ℚ)),([1,1],(3 : ℚ))]
  | 3 => [([3],(1 : ℚ)),([2,1],(15 : ℚ)),([1,1,1],(15 : ℚ))]
  | 4 => [([4],(1 : ℚ)),([3,1],(28 : ℚ)),([2,2],(35 : ℚ)),([2,1,1],(210 : ℚ)),([1,1,1,1],(105 : ℚ))]
  | 5 => [([5],(1 : ℚ)),([4,1],(45 : ℚ)),([3,2],(210 : ℚ)),([3,1,1],(630 : ℚ)),([2,2,1],(1575 : ℚ)),([2,1,1,1],(3150 : ℚ)),([1,1,1,1,1],(945 : ℚ))]
  | 6 => [([6],(1 : ℚ)),([5,1],(66 : ℚ)),([4,2],(495 : ℚ)),([4,1,1],(1485 : ℚ)),([3,3],(462 : ℚ)),([3,2,1],(13860 : ℚ)),([3,1,1,1],(13860 : ℚ)),([2,2,2],(5775 : ℚ)),([2,2,1,1],(51975 : ℚ)),([2,1,1,1,1],(51975 : ℚ)),([1,1,1,1,1,1],(10395 : ℚ))]
  | 7 => [([7],(1 : ℚ)),([6,1],(91 : ℚ)),([5,2],(1001 : ℚ)),([5,1,1],(3003 : ℚ)),([4,3],(3003 : ℚ)),([4,2,1],(45045 : ℚ)),([4,1,1,1],(45045 : ℚ)),([3,3,1],(42042 : ℚ)),([3,2,2],(105105 : ℚ)),([3,2,1,1],(630630 : ℚ)),([3,1,1,1,1],(315315 : ℚ)),([2,2,2,1],(525525 : ℚ)),([2,2,1,1,1],(1576575 : ℚ)),([2,1,1,1,1,1],(945945 : ℚ)),([1,1,1,1,1,1,1],(135135 : ℚ))]
  | 8 => [([8],(1 : ℚ)),([7,1],(120 : ℚ)),([6,2],(1820 : ℚ)),([6,1,1],(5460 : ℚ)),([5,3],(8008 : ℚ)),([5,2,1],(120120 : ℚ)),([5,1,1,1],(120120 : ℚ)),([4,4],(6435 : ℚ)),([4,3,1],(360360 : ℚ)),([4,2,2],(450450 : ℚ)),([4,2,1,1],(2702700 : ℚ)),([4,1,1,1,1],(1351350 : ℚ)),([3,3,2],(840840 : ℚ)),([3,3,1,1],(2522520 : ℚ)),([3,2,2,1],(12612600 : ℚ)),([3,2,1,1,1],(25225200 : ℚ)),([3,1,1,1,1,1],(7567560 : ℚ)),([2,2,2,2],(2627625 : ℚ)),([2,2,2,1,1],(31531500 : ℚ)),([2,2,1,1,1,1],(47297250 : ℚ)),([2,1,1,1,1,1,1],(18918900 : ℚ)),([1,1,1,1,1,1,1,1],(2027025 : ℚ))]
  | 9 => [([9],(1 : ℚ)),([8,1],(153 : ℚ)),([7,2],(3060 : ℚ)),([7,1,1],(9180 : ℚ)),([6,3],(18564 : ℚ)),([6,2,1],(278460 : ℚ)),([6,1,1,1],(278460 : ℚ)),([5,4],(43758 : ℚ)),([5,3,1],(1225224 : ℚ)),([5,2,2],(1531530 : ℚ)),([5,2,1,1],(9189180 : ℚ)),([5,1,1,1,1],(4594590 : ℚ)),([4,4,1],(984555 : ℚ)),([4,3,2],(9189180 : ℚ)),([4,3,1,1],(27567540 : ℚ)),([4,2,2,1],(68918850 : ℚ)),([4,2,1,1,1],(137837700 : ℚ)),([4,1,1,1,1,1],(41351310 : ℚ)),([3,3,3],(2858856 : ℚ)),([3,3,2,1],(128648520 : ℚ)),([3,3,1,1,1],(128648520 : ℚ)),([3,2,2,2],(107207100 : ℚ)),([3,2,2,1,1],(964863900 : ℚ)),([3,2,1,1,1,1],(964863900 : ℚ)),([3,1,1,1,1,1,1],(192972780 : ℚ)),([2,2,2,2,1],(402026625 : ℚ)),([2,2,2,1,1,1],(1608106500 : ℚ)),([2,2,1,1,1,1,1],(1447295850 : ℚ)),([2,1,1,1,1,1,1,1],(413513100 : ℚ)),([1,1,1,1,1,1,1,1,1],(34459425 : ℚ))]
  | _ => []

def sumPoly (ls : List SymPoly) : SymPoly := collectTerms ls.flatten

def linearOrbitPoly (p : Part) (a : List ℚ) : SymPoly :=
  (List.range p.length).map (fun i => (incPart p i 1, a[i]?.getD 0))
def quadraticOrbitPoly (p : Part) (a : List ℚ) : SymPoly :=
  (List.range p.length).flatMap (fun i => (List.range p.length).map (fun j =>
    (canon ((p.modify i (fun x => x+1)).modify j (fun x => x+1)),
     (a[i]?.getD 0)*(a[j]?.getD 0))))
def squarePoly (p : Part) (a : List ℚ) (b : ℚ) : SymPoly :=
  addPoly (quadraticOrbitPoly p a)
    (addPoly (scalePoly (2*b) (homogenize 1 (linearOrbitPoly p a)))
      (scalePoly (b*b) (homogenize 2 [(canon p,1)])))

inductive CertGen where
  | mono (p : Part)
  | sq (p : Part) (a : List ℚ) (b : ℚ)
  deriving DecidableEq

def genPoly : CertGen → SymPoly
  | .mono p => [(p,1)]
  | .sq p a b => squarePoly p a b

def certTerms : List (CertGen × ℚ) := [
  (.mono [3,1,1,1,1,1,1], (1664613736174404701898764587/6796875000000000000000000000 : ℚ)),
  (.mono [2,2,2,2,1], (108989344820371538388330031/453125000000000000000000000 : ℚ)),
  (.mono [2,2,2,1,1,1], (363684300416795776733564179/113281250000000000000000000 : ℚ)),
  (.mono [2,2,1,1,1,1,1], (2336944380198391076759655527/4531250000000000000000000000 : ℚ)),
  (.mono [2,1,1,1,1,1,1,1], (216789029015454276313036273/6796875000000000000000000000 : ℚ)),
  (.sq [7] [(3 : ℚ)] (-1 : ℚ), (493179443887342163427833603/13593750000000000000000000000 : ℚ)),
  (.sq [6,1] [(4 : ℚ),(-1 : ℚ)] (-1 : ℚ), (812765822952113500072745389/7646484375000000000000000000 : ℚ)),
  (.sq [5,2] [(0 : ℚ),(3 : ℚ)] (-1 : ℚ), (62167895823868919398383790542583/70837031250000000000000000000000 : ℚ)),
  (.sq [5,2] [(1 : ℚ),(2 : ℚ)] (-1 : ℚ), (163497426726949101247569983295373/23612343750000000000000000000000 : ℚ)),
  (.sq [5,2] [(3 : ℚ),(0 : ℚ)] (-1 : ℚ), (40898714423911742716816466080817/70837031250000000000000000000000 : ℚ)),
  (.sq [5,1,1] [(0 : ℚ),(1 : ℚ),(-4 : ℚ)] (1 : ℚ), (316314290160339665000599013407/244687500000000000000000000000 : ℚ)),
  (.sq [5,1,1] [(1 : ℚ),(-4 : ℚ),(0 : ℚ)] (1 : ℚ), (5616588740169136634279762243/30585937500000000000000000000 : ℚ)),
  (.sq [5,1,1] [(2 : ℚ),(-2 : ℚ),(3 : ℚ)] (-1 : ℚ), (114618313877765137564740921259/244687500000000000000000000000 : ℚ)),
  (.sq [4,3] [(1 : ℚ),(-1 : ℚ)] (0 : ℚ), (5339167732278402092228998206713/655898437500000000000000000000 : ℚ)),
  (.sq [4,2,1] [(1 : ℚ),(-4 : ℚ),(-3 : ℚ)] (2 : ℚ), (310739092555566277658560548518749/708370312500000000000000000000000 : ℚ)),
  (.sq [4,2,1] [(1 : ℚ),(-3 : ℚ),(-1 : ℚ)] (1 : ℚ), (392034570279110895520185390303/349812500000000000000000000000 : ℚ)),
  (.sq [4,2,1] [(1 : ℚ),(2 : ℚ),(0 : ℚ)] (-1 : ℚ), (122998561194378624518449413573949/141674062500000000000000000000000 : ℚ)),
  (.sq [4,2,1] [(3 : ℚ),(-1 : ℚ),(4 : ℚ)] (-2 : ℚ), (30884554274001200121651411444769/47224687500000000000000000000000 : ℚ)),
  (.sq [4,2,1] [(4 : ℚ),(-1 : ℚ),(3 : ℚ)] (-2 : ℚ), (15321637693779276596484703530539/29515429687500000000000000000000 : ℚ)),
  (.sq [3,3,1] [(0 : ℚ),(3 : ℚ),(0 : ℚ)] (-1 : ℚ), (1916317734043019380935103552589/983847656250000000000000000000 : ℚ)),
  (.sq [3,3,1] [(1 : ℚ),(-3 : ℚ),(-1 : ℚ)] (1 : ℚ), (2356243716118467132440203511597/1967695312500000000000000000000 : ℚ)),
  (.sq [3,2,2] [(1 : ℚ),(-3 : ℚ),(-1 : ℚ)] (1 : ℚ), (42477332960852370135610213284689/20988750000000000000000000000000 : ℚ)),
  (.sq [3,2,2] [(1 : ℚ),(1 : ℚ),(4 : ℚ)] (-2 : ℚ), (123346068448463558503725606137/67851562500000000000000000000 : ℚ)),
  (.sq [3,2,2] [(3 : ℚ),(-1 : ℚ),(1 : ℚ)] (-1 : ℚ), (34657463038753289354159290580269/62966250000000000000000000000000 : ℚ)),
  (.sq [3,2,1,1] [(0 : ℚ),(1 : ℚ),(-3 : ℚ),(0 : ℚ)] 0, (111868341854332796257367494399/13593750000000000000000000000 : ℚ)),
  (.sq [2,2,2,1] [(1 : ℚ),(0 : ℚ),(0 : ℚ),(-3 : ℚ)] 0, (129021577255464953947629819/45312500000000000000000000 : ℚ)),
  (.sq [2,1,1,1,1,1] [(1 : ℚ),(-4 : ℚ),(0 : ℚ),(0 : ℚ),(0 : ℚ),(0 : ℚ)] 0, (22348383362905355092020478147/67968750000000000000000000000 : ℚ)),
  (.sq [2,1,1,1,1,1] [(1 : ℚ),(-3 : ℚ),(0 : ℚ),(0 : ℚ),(0 : ℚ),(0 : ℚ)] 0, (20937950969712400953131202529/33984375000000000000000000000 : ℚ))]

def certificatePoly : SymPoly :=
  sumPoly (certTerms.map (fun (g,c) => scalePoly c (genPoly g)))
def gapPoly : SymPoly :=
  addPoly (scalePoly (3/16) (homogenize 9 [([],1)]))
    (sumPoly ((List.range 10).map (fun j =>
      scalePoly (-(pCoeff j)*3^j) (homogenize (9-j) (momentPoly j)))))

 theorem certificate_coefficient_identity :
    normalizePoly gapPoly = normalizePoly certificatePoly := by decide +kernel

 theorem certTerms_nonneg : ∀ t ∈ certTerms, 0 ≤ t.2 := by decide +kernel


end SharpEighth


/-! ## CertificateSemantics -/
namespace SharpEighth

set_option maxHeartbeats 0

theorem symEval_sumPoly (O : Part → ℝ) (ls : List SymPoly) :
    symEval O (sumPoly ls) = (ls.map (symEval O)).sum := by
  unfold sumPoly
  rw [symEval_collect]
  induction ls with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatten_cons, symEval_append, List.map_cons, List.sum_cons, ih]

theorem symEval_gen_nonneg (O : Part → ℝ)
    (hO : ∀ p, 0 ≤ O p)
    (hSq : ∀ p a b, 0 ≤ symEval O (squarePoly p a b)) (g : CertGen) :
    0 ≤ symEval O (genPoly g) := by
  cases g with
  | mono p => simpa [genPoly, symEval] using hO p
  | sq p a b => exact hSq p a b

theorem certificate_eval_nonneg (O : Part → ℝ)
    (hO : ∀ p, 0 ≤ O p)
    (hSq : ∀ p a b, 0 ≤ symEval O (squarePoly p a b)) :
    0 ≤ symEval O certificatePoly := by
  unfold certificatePoly
  rw [symEval_sumPoly]
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
  rw [symEval_scale]
  exact mul_nonneg (by exact_mod_cast certTerms_nonneg t ht)
    (symEval_gen_nonneg O hO hSq t.1)

theorem gap_eval_nonneg (O : Part → ℝ)
    (hO : ∀ p, 0 ≤ O p)
    (hSq : ∀ p a b, 0 ≤ symEval O (squarePoly p a b)) :
    0 ≤ symEval O gapPoly := by
  rw [symEval_of_normalize_eq O gapPoly certificatePoly certificate_coefficient_identity]
  exact certificate_eval_nonneg O hO hSq

theorem sum_map_neg_real {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map (fun a => -f a)).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem gap_eval_normalized (O : Part → ℝ)
    (hEmpty : O [] = 1)
    (hMul : ∀ p, (raisePart p |>.map O).sum = O p) :
    symEval O gapPoly = (3/16 : ℝ) -
      ((List.range 10).map (fun j =>
        (pCoeff j : ℝ) * 3^j * symEval O (momentPoly j))).sum := by
  have hHom (k : ℕ) (l : SymPoly) :
      symEval O (homogenize k l) = symEval O l := by
    simpa using symEval_homogenize O 1 (by intro p; simpa using hMul p) k l
  have hTerm (j : ℕ) :
      symEval O (scalePoly (-(pCoeff j)*3^j) (homogenize (9-j) (momentPoly j))) =
        -((pCoeff j : ℝ)*3^j*symEval O (momentPoly j)) := by
    rw [symEval_scale, hHom]
    push_cast
    ring
  unfold gapPoly
  rw [symEval_add, symEval_scale, hHom, symEval_sumPoly]
  simp only [List.map_map, Function.comp_def]
  simp_rw [hTerm]
  rw [sum_map_neg_real]
  norm_num [symEval, hEmpty]
  ring

theorem certificate_moment_bound (O : Part → ℝ)
    (hEmpty : O [] = 1)
    (hMul : ∀ p, (raisePart p |>.map O).sum = O p)
    (hO : ∀ p, 0 ≤ O p)
    (hSq : ∀ p a b, 0 ≤ symEval O (squarePoly p a b)) :
    ((List.range 10).map (fun j =>
      (pCoeff j : ℝ) * 3^j * symEval O (momentPoly j))).sum ≤ (3/16 : ℝ) := by
  have h := gap_eval_nonneg O hO hSq
  rw [gap_eval_normalized O hEmpty hMul] at h
  linarith

theorem P_eq_coeff_sum (x : ℝ) :
    P x = ((List.range 10).map (fun j => (pCoeff j : ℝ) * x^(2*j))).sum := by
  norm_num [P, pCoeff, pCoeffs, List.range_succ]
  ring


end SharpEighth


/-! ## MomentRecurrenceData -/
open scoped BigOperators

namespace SharpEighth

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The first key entry distinguishes the exponent of the newly added variable;
the remaining entries are the ordinary ordered-orbit partition. -/
def tagPoly (k : ℕ) (l : SymPoly) : SymPoly :=
  l.map (fun (p, c) => (k :: p, c))

def coordinateParts (p : Part) : List Part :=
  (0 :: p) :: (List.range p.length).map
    (fun i => p[i]?.getD 0 :: p.eraseIdx i)

def coordinatePoly (l : SymPoly) : SymPoly :=
  collectTerms (l.flatMap (fun (p, c) =>
    (coordinateParts p).map (fun q => (q, c))))

def momentRecurrencePoly (j : ℕ) : SymPoly :=
  sumPoly ((List.range (j + 1)).map (fun k =>
    scalePoly (((2 * j).choose (2 * k)) : ℚ) (tagPoly k (momentPoly (j - k)))))

/-- The ten finite moment tables satisfy the exact binomial recurrence.
This proof uses kernel reduction of rational arithmetic, not native execution. -/
theorem moment_coordinate_coefficient_identity (j : ℕ) (hj : j ≤ 9) :
    normalizePoly (coordinatePoly (momentPoly j)) =
      normalizePoly (momentRecurrencePoly j) := by
  interval_cases j <;> decide +kernel

def taggedEval (a : ℝ) (O : Part → ℝ) : Part → ℝ
  | [] => 0
  | k :: p => a ^ k * O p

theorem symEval_tagPoly (a : ℝ) (O : Part → ℝ) (k : ℕ) (l : SymPoly) :
    symEval (taggedEval a O) (tagPoly k l) = a ^ k * symEval O l := by
  induction l with
  | nil => simp [tagPoly, symEval]
  | cons t l ih =>
    rcases t with ⟨p, c⟩
    simp only [tagPoly, List.map_cons, symEval_cons, taggedEval] at ih ⊢
    rw [ih]
    ring

theorem symEval_coordinatePoly (a : ℝ) (O O' : Part → ℝ)
    (hrec : ∀ p, ((coordinateParts p).map (taggedEval a O)).sum = O' p)
    (l : SymPoly) :
    symEval (taggedEval a O) (coordinatePoly l) = symEval O' l := by
  unfold coordinatePoly
  rw [symEval_collect]
  induction l with
  | nil => rfl
  | cons t l ih =>
    rcases t with ⟨p, c⟩
    rw [List.flatMap_cons, symEval_append, symEval_constMap, hrec, ih]
    rfl

/-- Semantic recurrence for any family of orbit evaluations satisfying the
one-coordinate deletion identity. -/
theorem momentPoly_coordinate_recurrence (a : ℝ) (O O' : Part → ℝ)
    (hrec : ∀ p, ((coordinateParts p).map (taggedEval a O)).sum = O' p)
    (j : ℕ) (hj : j ≤ 9) :
    symEval O' (momentPoly j) =
      ((List.range (j + 1)).map (fun k =>
        (((2 * j).choose (2 * k) : ℕ) : ℝ) * a ^ k *
          symEval O (momentPoly (j - k)))).sum := by
  rw [← symEval_coordinatePoly a O O' hrec]
  rw [symEval_of_normalize_eq (taggedEval a O)
    (coordinatePoly (momentPoly j)) (momentRecurrencePoly j)
    (moment_coordinate_coefficient_identity j hj)]
  unfold momentRecurrencePoly
  rw [symEval_sumPoly, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply, symEval_scale, symEval_tagPoly, Rat.cast_natCast]
  ring


end SharpEighth


/-! ## OrbitCoordinates -/
open scoped BigOperators Classical
open Finset

namespace SharpEighth

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 10000

variable {ι : Type*} [Fintype ι]

theorem orbit_option (p : Part) (a : ℝ) (z : ι → ℝ) :
    orbit p (optionValue a z) = orbit p z +
      ∑ i : Fin p.length, a ^ p.get i * orbit (p.eraseIdx i.val) z := by
  classical
  change tupleOrbit p.get (optionValue a z) = _
  rw [tupleOrbit_option]
  congr 1
  apply sum_congr rfl
  intro i _
  congr 1
  exact (tupleOrbit_reindex (p.eraseIdx i.val).get
    (fun j : {j : Fin p.length // j ≠ i} => p.get j.val) z
    (eraseIndexEquiv p i) (fun k => (get_eraseIndexEquiv p i k).symm)).symm

theorem orbit_fin_cons {n : ℕ} (p : Part) (a : ℝ) (z : Fin n → ℝ) :
    orbit p (Fin.cons a z) = orbit p z +
      ∑ i : Fin p.length, a ^ p.get i * orbit (p.eraseIdx i.val) z := by
  calc
    orbit p (Fin.cons a z) = orbit p (optionValue a z) := by
      apply tupleOrbit_reindex_codomain p.get _ _ (finSuccEquiv n)
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [optionValue]
      · simp [optionValue]
    _ = _ := orbit_option p a z

theorem orbit_coordinateParts {n : ℕ} (p : Part) (a : ℝ) (z : Fin n → ℝ) :
    ((coordinateParts p).map (taggedEval a (fun q => orbit q z))).sum =
      orbit p (Fin.cons a z) := by
  rw [orbit_fin_cons]
  simp only [coordinateParts, List.map_cons, List.sum_cons, List.map_map,
    Function.comp_apply, taggedEval, pow_zero, one_mul]
  congr 1
  rw [← List.sum_toFinset _ List.nodup_range]
  have hrange : (List.range p.length).toFinset = Finset.range p.length := by
    ext i
    simp
  rw [hrange, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  simp [taggedEval]


end

end SharpEighth


/-! ## RademacherDefs -/
open scoped BigOperators

namespace SharpEighth

noncomputable section

/-- Uniform average on a finite set. -/
def avg {α : Type*} [Fintype α] (g : α → ℝ) : ℝ :=
  (∑ x, g x) / (Fintype.card α : ℝ)

/-- The Rademacher sign associated with a Boolean coordinate. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

/-- A real linear form on the Boolean cube. -/
def linearForm {n : ℕ} (c : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i, c i * sign (x i)

theorem avg_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    avg (fun x => f x + g x) = avg f + avg g := by
  simp only [avg, Finset.sum_add_distrib, add_div]

theorem avg_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    avg (fun x => f x - g x) = avg f - avg g := by
  simp only [avg, Finset.sum_sub_distrib, sub_div]

theorem avg_mul_left {α : Type*} [Fintype α] (a : ℝ) (f : α → ℝ) :
    avg (fun x => a * f x) = a * avg f := by
  simp only [avg, ← Finset.mul_sum]
  ring

theorem avg_mul_right {α : Type*} [Fintype α] (f : α → ℝ) (a : ℝ) :
    avg (fun x => f x * a) = avg f * a := by
  simp only [avg, ← Finset.sum_mul]
  ring

theorem avg_le_avg {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ x, f x ≤ g x) : avg f ≤ avg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (by positivity)

theorem avg_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (h : ∀ x, 0 ≤ f x) : 0 ≤ avg f := by
  exact div_nonneg (Finset.sum_nonneg fun x _ => h x) (by positivity)

theorem avg_const {α : Type*} [Fintype α] [Nonempty α] (a : ℝ) :
    avg (fun _ : α => a) = a := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  simp only [avg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem avg_equiv {α : Type*} [Fintype α] (e : Equiv.Perm α) (f : α → ℝ) :
    avg (fun x => f (e x)) = avg f := by
  unfold avg
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem avg_sum {α ι : Type*} [Fintype α] [Fintype ι] (f : ι → α → ℝ) :
    avg (fun x => ∑ i, f i x) = ∑ i, avg (f i) := by
  simp only [avg]
  rw [Finset.sum_comm, Finset.sum_div]

end
end SharpEighth


/-! ## RademacherMoments -/
open scoped BigOperators
open Finset

namespace SharpEighth

noncomputable section

private def cubeConsEquiv (n : ℕ) :
    (Bool × (Fin n → Bool)) ≃ (Fin (n + 1) → Bool) where
  toFun x := Fin.cons x.1 x.2
  invFun x := (x 0, fun i => x i.succ)
  left_inv x := by
    rcases x with ⟨b, x⟩
    rfl
  right_inv x := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem avg_cube_cons {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    avg f =
      (avg (fun x => f (Fin.cons true x)) +
        avg (fun x => f (Fin.cons false x))) / 2 := by
  have hsum : (∑ x, f x) =
      ∑ b : Bool, ∑ x : Fin n → Bool, f (Fin.cons b x) := by
    calc
      _ = ∑ bx : Bool × (Fin n → Bool), f (Fin.cons bx.1 bx.2) :=
        (Fintype.sum_equiv (cubeConsEquiv n) _ _ (fun _ => rfl)).symm
      _ = _ := Fintype.sum_prod_type _
  unfold avg
  rw [hsum, Fintype.sum_bool]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_succ,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  ring

theorem linearForm_cons {n : ℕ} (a : ℝ) (c : Fin n → ℝ)
    (b : Bool) (x : Fin n → Bool) :
    linearForm (Fin.cons a c) (Fin.cons b x) = a * sign b + linearForm c x := by
  simp [linearForm, Fin.sum_univ_succ]

private theorem sum_range_even_odd (f : ℕ → ℝ) (j : ℕ) :
    (∑ r ∈ range (2 * j + 1), f r) =
      (∑ k ∈ range (j + 1), f (2 * k)) +
        ∑ k ∈ range j, f (2 * k + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by omega]
    rw [sum_range_succ, sum_range_succ, ih]
    rw [sum_range_succ (fun k => f (2 * k)) (j + 1),
      sum_range_succ (fun k => f (2 * k + 1)) j]
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by omega]
    ring

/-- Averaging the two signs removes the odd binomial terms. -/
theorem even_binomial_average (a b : ℝ) (j : ℕ) :
    ((a + b) ^ (2 * j) + (-a + b) ^ (2 * j)) / 2 =
      ∑ k ∈ range (j + 1),
        ((2 * j).choose (2 * k) : ℝ) * a ^ (2 * k) * b ^ (2 * (j - k)) := by
  rw [add_pow, add_pow, ← sum_add_distrib,
    sum_range_even_odd]
  have hodd : (∑ k ∈ range j,
      (a ^ (2 * k + 1) * b ^ (2 * j - (2 * k + 1)) *
        ((2 * j).choose (2 * k + 1) : ℝ) +
      (-a) ^ (2 * k + 1) * b ^ (2 * j - (2 * k + 1)) *
        ((2 * j).choose (2 * k + 1) : ℝ))) = 0 := by
    apply sum_eq_zero
    intro k _
    simp [pow_succ, pow_mul]
  rw [hodd, add_zero, sum_div]
  apply sum_congr rfl
  intro k hk
  have he : 2 * j - 2 * k = 2 * (j - k) := by omega
  rw [he]
  simp only [pow_mul, neg_sq]
  ring

theorem avg_sum_finset {α ι : Type*} [Fintype α]
    (s : Finset ι) (f : ι → α → ℝ) :
    avg (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, avg (f i) := by
  unfold avg
  rw [sum_comm, sum_div]

theorem avg_div {α : Type*} [Fintype α] (f : α → ℝ) (a : ℝ) :
    avg (fun x => f x / a) = avg f / a := by
  unfold avg
  rw [← sum_div]
  ring

/-- The even moments of a Rademacher linear form obey the binomial recurrence
when one independent Boolean coordinate is adjoined. -/
theorem even_moment_cons {n : ℕ} (a : ℝ) (c : Fin n → ℝ) (j : ℕ) :
    avg (fun x => (linearForm (Fin.cons a c) x) ^ (2 * j)) =
      ∑ k ∈ range (j + 1),
        ((2 * j).choose (2 * k) : ℝ) * a ^ (2 * k) *
          avg (fun x => (linearForm c x) ^ (2 * (j - k))) := by
  rw [avg_cube_cons]
  simp only [linearForm_cons, sign, Bool.false_eq_true, ↓reduceIte, mul_one,
    mul_neg_one]
  calc
    _ = avg (fun x =>
        ((a + linearForm c x) ^ (2 * j) +
          (-a + linearForm c x) ^ (2 * j)) / 2) := by
      rw [avg_div, avg_add]
    _ = avg (fun x => ∑ k ∈ range (j + 1),
        ((2 * j).choose (2 * k) : ℝ) * a ^ (2 * k) *
          (linearForm c x) ^ (2 * (j - k))) := by
      congr 1
      funext x
      exact even_binomial_average _ _ _
    _ = _ := by
      rw [avg_sum_finset]
      apply sum_congr rfl
      intro k _
      exact avg_mul_left _ _


end
end SharpEighth


/-! ## MomentBase -/
open scoped BigOperators

namespace SharpEighth

noncomputable section

theorem orbit_fin_zero (p : Part) (z : Fin 0 → ℝ) :
    orbit p z = if p = [] then 1 else 0 := by
  cases p with
  | nil => simp [orbit_nil]
  | cons d p =>
    haveI : IsEmpty (Fin (d :: p).length ↪ Fin 0) :=
      ⟨fun e => Fin.elim0 (e ⟨0, by simp⟩)⟩
    simp [orbit]

theorem momentPoly_fin_zero (z : Fin 0 → ℝ) (j : ℕ) (hj : j ≤ 9) :
    symEval (fun p => orbit p z) (momentPoly j) = if j = 0 then 1 else 0 := by
  interval_cases j <;>
    norm_num [momentPoly, symEval, orbit_fin_zero, List.cons_ne_nil]

theorem even_moment_fin_zero (c : Fin 0 → ℝ) (j : ℕ) :
    avg (fun x => (linearForm c x) ^ (2 * j)) = if j = 0 then 1 else 0 := by
  cases j with
  | zero => simp [avg_const]
  | succ j => simp [linearForm, avg_const]

theorem momentPoly_matches_zero_dimension (c : Fin 0 → ℝ)
    (j : ℕ) (hj : j ≤ 9) :
    symEval (fun p => orbit p (fun i => (c i) ^ 2)) (momentPoly j) =
      avg (fun x => (linearForm c x) ^ (2 * j)) := by
  rw [momentPoly_fin_zero _ j hj, even_moment_fin_zero]


end
end SharpEighth


/-! ## OrbitSquares -/
open scoped BigOperators Classical
open Finset

namespace SharpEighth

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem orbit_add_get (p q : List ℕ) (z : ι → ℝ) (hlen : q.length = p.length)
    (d : Fin p.length → ℕ)
    (hget : ∀ k, q.get (Fin.cast hlen.symm k) = p.get k + d k) :
    orbit q z = ∑ e : Fin p.length ↪ ι,
      orbitTerm p z e * ∏ k, z (e k) ^ d k := by
  rw [orbit_eq_cast_sum q z hlen]
  apply sum_congr rfl
  intro e _
  simp_rw [hget, pow_add]
  rw [prod_mul_distrib]
  rfl

theorem orbit_modify_two (p : List ℕ) (z : ι → ℝ) (i j : Fin p.length) :
    orbit ((p.modify i.val (fun a => a + 1)).modify j.val (fun a => a + 1)) z =
      ∑ e : Fin p.length ↪ ι, orbitTerm p z e * z (e i) * z (e j) := by
  let d : Fin p.length → ℕ := fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)
  have hlen : ((p.modify i.val (fun a => a + 1)).modify j.val (fun a => a + 1)).length =
      p.length := by simp
  have hget (k : Fin p.length) :
      ((p.modify i.val (fun a => a + 1)).modify j.val (fun a => a + 1)).get
        (Fin.cast hlen.symm k) = p.get k + d k := by
    have hik : (i.val = k.val) ↔ k = i := by simp [Fin.ext_iff, eq_comm]
    have hjk : (j.val = k.val) ↔ k = j := by simp [Fin.ext_iff, eq_comm]
    simp only [d, List.get_eq_getElem, Fin.coe_cast, List.getElem_modify, hik, hjk]
    split_ifs <;> omega
  rw [orbit_add_get p _ z hlen d hget]
  apply sum_congr rfl
  intro e _
  dsimp [d]
  simp_rw [pow_add]
  rw [prod_mul_distrib]
  have hprod (i : Fin p.length) :
      (∏ k : Fin p.length, z (e k) ^ (if k = i then 1 else 0)) = z (e i) := by
    simp only [apply_ite, pow_one, pow_zero]
    exact Fintype.prod_ite_eq' _ _
  rw [hprod, hprod]
  ring

def weightedOrbitSquare (p : List ℕ) (z : ι → ℝ) (a : Fin p.length → ℝ) (b : ℝ) : ℝ :=
  ∑ e : Fin p.length ↪ ι,
    orbitTerm p z e * ((∑ k, a k * z (e k)) + b * (∑ j, z j)) ^ 2

theorem weightedOrbitSquare_nonneg (p : List ℕ) (z : ι → ℝ)
    (a : Fin p.length → ℝ) (b : ℝ) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ weightedOrbitSquare p z a b := by
  apply sum_nonneg
  intro e _
  apply mul_nonneg _ (sq_nonneg _)
  apply prod_nonneg
  intro k _
  exact pow_nonneg (hz _) _

end

end SharpEighth


/-! ## SquareSemantics -/
open scoped BigOperators Classical
open Finset

namespace SharpEighth

noncomputable section

set_option maxHeartbeats 0

variable {ι : Type*} [Fintype ι]

theorem list_range_sum_eq_fin (k : ℕ) (f : ℕ → ℝ) :
    ((List.range k).map f).sum = ∑ i : Fin k, f i.val := by
  rw [← List.sum_toFinset _ List.nodup_range]
  have hrange : (List.range k).toFinset = Finset.range k := by
    ext i
    simp
  rw [hrange]
  exact (Fin.sum_univ_eq_sum_range f k).symm

theorem symEval_flatMap {α : Type*} (O : Part → ℝ)
    (l : List α) (f : α → SymPoly) :
    symEval O (l.flatMap f) = (l.map (fun a => symEval O (f a))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, symEval_append, List.map_cons, List.sum_cons, ih]

theorem symEval_linearOrbitPoly (p : Part) (z : ι → ℝ) (a : List ℚ) :
    symEval (fun q => orbit q z) (linearOrbitPoly p a) =
      ∑ i : Fin p.length, (a[i.val]?.getD 0 : ℝ) *
        orbit (p.modify i.val (fun d => d+1)) z := by
  rw [symEval_eq_sum]
  simp only [linearOrbitPoly, List.map_map, Function.comp_def]
  rw [list_range_sum_eq_fin]
  apply sum_congr rfl
  intro i _
  simp only [incPart, orbit_canon]

theorem symEval_quadraticOrbitPoly (p : Part) (z : ι → ℝ) (a : List ℚ) :
    symEval (fun q => orbit q z) (quadraticOrbitPoly p a) =
      ∑ i : Fin p.length, ∑ j : Fin p.length,
        (a[i.val]?.getD 0 : ℝ) * (a[j.val]?.getD 0 : ℝ) *
        orbit ((p.modify i.val (fun d => d+1)).modify j.val (fun d => d+1)) z := by
  unfold quadraticOrbitPoly
  rw [symEval_flatMap, list_range_sum_eq_fin]
  apply sum_congr rfl
  intro i _
  rw [symEval_eq_sum]
  simp only [List.map_map, Function.comp_def]
  rw [list_range_sum_eq_fin]
  apply sum_congr rfl
  intro j _
  simp only [Rat.cast_mul, orbit_canon]

theorem weightedOrbitSquare_expansion (p : Part) (z : ι → ℝ)
    (a : Fin p.length → ℝ) (b : ℝ) :
    weightedOrbitSquare p z a b =
      (∑ i : Fin p.length, ∑ j : Fin p.length, a i * a j *
        orbit ((p.modify i.val (fun d => d+1)).modify j.val (fun d => d+1)) z) +
      2*b*(∑ u, z u) *
        (∑ i : Fin p.length, a i * orbit (p.modify i.val (fun d => d+1)) z) +
      b^2*(∑ u, z u)^2 * orbit p z := by
  have hQuad :
      (∑ i : Fin p.length, ∑ j : Fin p.length, a i * a j *
        orbit ((p.modify i.val (fun d => d+1)).modify j.val (fun d => d+1)) z) =
      ∑ e : Fin p.length ↪ ι, orbitTerm p z e * (∑ i, a i * z (e i))^2 := by
    simp_rw [orbit_modify_two, mul_sum]
    calc
      _ = ∑ i : Fin p.length, ∑ e : Fin p.length ↪ ι,
          ∑ j : Fin p.length, a i*a j*(orbitTerm p z e*z (e i)*z (e j)) := by
        apply sum_congr rfl
        intro i _
        rw [sum_comm]
      _ = ∑ e : Fin p.length ↪ ι, ∑ i : Fin p.length,
          ∑ j : Fin p.length, a i*a j*(orbitTerm p z e*z (e i)*z (e j)) := by
        rw [sum_comm]
      _ = _ := by
        apply sum_congr rfl
        intro e _
        simp only [pow_two, sum_mul, mul_sum]
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        ring
  have hLin :
      (∑ i : Fin p.length, a i * orbit (p.modify i.val (fun d => d+1)) z) =
      ∑ e : Fin p.length ↪ ι, orbitTerm p z e * (∑ i, a i * z (e i)) := by
    simp_rw [orbit_modify, pow_one, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    apply sum_congr rfl
    intro i _
    ring
  rw [hQuad, hLin]
  unfold weightedOrbitSquare orbit
  calc
    _ = ∑ e : Fin p.length ↪ ι,
        (orbitTerm p z e * (∑ i, a i * z (e i))^2 +
          (2*b*(∑ u, z u)) * (orbitTerm p z e * (∑ i, a i * z (e i))) +
          (b^2*(∑ u, z u)^2) * orbitTerm p z e) := by
      apply sum_congr rfl
      intro e _
      ring
    _ = _ := by
      rw [sum_add_distrib, sum_add_distrib]
      rw [← mul_sum, ← mul_sum]

theorem symEval_squarePoly (p : Part) (z : ι → ℝ) (a : List ℚ) (b : ℚ) :
    symEval (fun q => orbit q z) (squarePoly p a b) =
      weightedOrbitSquare p z (fun i => (a[i.val]?.getD 0 : ℝ)) (b : ℝ) := by
  unfold squarePoly
  rw [symEval_add, symEval_add, symEval_scale, symEval_scale]
  rw [symEval_homogenize _ (∑ i, z i) (fun p => orbit_raisePart p z),
    symEval_homogenize _ (∑ i, z i) (fun p => orbit_raisePart p z)]
  rw [symEval_quadraticOrbitPoly, symEval_linearOrbitPoly,
    weightedOrbitSquare_expansion]
  simp only [symEval, Rat.cast_one, mul_one, zero_add, add_zero, orbit_canon,
    Rat.cast_mul, Rat.cast_ofNat, pow_one]
  ring

theorem symEval_squarePoly_nonneg (p : Part) (z : ι → ℝ)
    (a : List ℚ) (b : ℚ) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ symEval (fun q => orbit q z) (squarePoly p a b) := by
  rw [symEval_squarePoly]
  exact weightedOrbitSquare_nonneg p z _ _ hz


end
end SharpEighth


/-! ## PolynomialExpectation -/
open scoped BigOperators

namespace SharpEighth

noncomputable section

set_option maxHeartbeats 0

theorem avg_list_sum {α β : Type*} [Fintype α] (l : List β) (f : β → α → ℝ) :
    avg (fun x => (l.map (fun b => f b x)).sum) =
      (l.map (fun b => avg (f b))).sum := by
  induction l with
  | nil => simp [avg]
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [avg_add, ih]

theorem sqrt_three_mul_even_pow (s : ℝ) (j : ℕ) :
    (Real.sqrt 3 * s)^(2*j) = 3^j * s^(2*j) := by
  rw [mul_pow, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

theorem avg_P_eq_moments {n : ℕ} (c : Fin n → ℝ) :
    avg (fun x => P (Real.sqrt 3 * linearForm c x)) =
      ((List.range 10).map (fun j =>
        (pCoeff j : ℝ) * 3^j *
          avg (fun x => (linearForm c x)^(2*j)))).sum := by
  simp_rw [P_eq_coeff_sum]
  rw [avg_list_sum]
  congr 1
  apply List.map_congr_left
  intro j hj
  simp_rw [sqrt_three_mul_even_pow, ← mul_assoc]
  exact avg_mul_left _ _

theorem normalized_P_bound_of_orbit_moments {n : ℕ} (c : Fin n → ℝ)
    (hnorm : (∑ i, (c i)^2) = 1)
    (hSq : ∀ p a b,
      0 ≤ symEval (fun p => orbit p (fun i => (c i)^2)) (squarePoly p a b))
    (hMom : ∀ j < 10,
      avg (fun x => (linearForm c x)^(2*j)) =
        symEval (fun p => orbit p (fun i => (c i)^2)) (momentPoly j)) :
    avg (fun x => P (Real.sqrt 3 * linearForm c x)) ≤ 3/16 := by
  rw [avg_P_eq_moments]
  have heq : ((List.range 10).map (fun j =>
      (pCoeff j : ℝ) * 3^j * avg (fun x => (linearForm c x)^(2*j)))).sum =
      ((List.range 10).map (fun j =>
      (pCoeff j : ℝ) * 3^j *
        symEval (fun p => orbit p (fun i => (c i)^2)) (momentPoly j))).sum := by
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [hMom j (List.mem_range.mp hj)]
  rw [heq]
  apply certificate_moment_bound
  · exact orbit_nil _
  · intro p
    rw [orbit_raisePart, hnorm, one_mul]
  · intro p
    exact orbit_nonneg p _ (fun i => sq_nonneg (c i))
  · exact hSq


end
end SharpEighth


/-! ## Fourier -/
open scoped BigOperators

namespace SharpEighth

noncomputable section

private theorem hinge_pair (t a : ℝ) (ha : 0 ≤ a) :
    max 0 (t - a) + max 0 (-t - a) = max 0 (|t| - a) := by
  by_cases ht : 0 ≤ t
  · have hz : max 0 (-t - a) = 0 := max_eq_left (by linarith)
    rw [abs_of_nonneg ht, hz, add_zero]
  · have hz : max 0 (t - a) = 0 := max_eq_left (by linarith)
    rw [abs_of_neg (lt_of_not_ge ht), hz, zero_add]

private theorem avg_hinge_pair {α : Type*} [Fintype α]
    (e : Equiv.Perm α) (t : α → ℝ) (ht : ∀ x, t (e x) = -t x)
    (a : ℝ) (ha : 0 ≤ a) :
    2 * avg (fun x => max 0 (t x - a)) = avg (fun x => max 0 (|t x| - a)) := by
  have hneg : avg (fun x => max 0 (-t x - a)) = avg (fun x => max 0 (t x - a)) := by
    calc
      _ = avg (fun x => max 0 (t (e x) - a)) := by
        congr 1
        funext x
        rw [ht]
      _ = _ := avg_equiv e (fun x => max 0 (t x - a))
  have hpair : avg (fun x => max 0 (t x - a) + max 0 (-t x - a)) =
      avg (fun x => max 0 (|t x| - a)) := by
    congr 1
    funext x
    exact hinge_pair (t x) a ha
  rw [avg_add, hneg] at hpair
  linarith

/-- Symmetry converts the even polynomial majorant into a sharp correlation bound. -/
theorem symmetric_indicator_correlation_bound {α : Type*} [Fintype α]
    (e : Equiv.Perm α) (t f : α → ℝ)
    (ht : ∀ x, t (e x) = -t x)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hmean : avg f = 1/8)
    (hmoment : avg (fun x => P (t x)) ≤ 3/16) :
    avg (fun x => f x * t x) ≤ 3/8 := by
  have hpoint : ∀ x, f x * t x ≤ (9/4) * f x + max 0 (t x - 9/4) := by
    intro x
    rcases hf x with hx | hx
    · rw [hx]
      simpa only [zero_mul, mul_zero, zero_add] using (le_max_left 0 (t x - 9/4))
    · rw [hx]
      have h := le_max_right 0 (t x - 9/4)
      simp only [one_mul, mul_one]
      linarith
  have hbound := avg_le_avg hpoint
  rw [avg_add, avg_mul_left, hmean] at hbound
  have hmajor := avg_le_avg (fun x => majorant (t x))
  have hpair := avg_hinge_pair e t ht (9/4) (by norm_num)
  linarith

/-- Complement all bits. -/
def flipCube (n : ℕ) : Equiv.Perm (Fin n → Bool) where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

theorem linearForm_flip {n : ℕ} (c : Fin n → ℝ) (x : Fin n → Bool) :
    linearForm c (flipCube n x) = -linearForm c x := by
  simp [linearForm, flipCube, Finset.sum_neg_distrib]

/-- First-level Fourier coefficient with respect to the uniform cube measure. -/
def firstCoeff {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) : ℝ :=
  avg (fun x => sign (x i) * f x)

/-- Total Fourier weight at level one. -/
def firstWeight {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ i, (firstCoeff f i)^2

theorem firstWeight_nonneg {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    0 ≤ firstWeight f := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (firstCoeff f i)

theorem avg_mul_linearForm {n : ℕ} (f : (Fin n → Bool) → ℝ) (c : Fin n → ℝ) :
    avg (fun x => f x * linearForm c x) = ∑ i, c i * firstCoeff f i := by
  simp only [linearForm, Finset.mul_sum]
  rw [avg_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    avg (fun x => f x * (c i * sign (x i))) =
        avg (fun x => c i * (sign (x i) * f x)) := by
      congr 1
      funext x
      ring
    _ = c i * firstCoeff f i := avg_mul_left _ _

/-- A normalized polynomial-moment estimate implies the sharp density-one-eighth
first-level Fourier bound in every dimension. -/
theorem sharp_eighth_of_moment_bound {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hmean : avg f = 1/8)
    (hmoment : ∀ c : Fin n → ℝ, (∑ i, (c i)^2) = 1 →
      avg (fun x => P (Real.sqrt 3 * linearForm c x)) ≤ 3/16) :
    firstWeight f ≤ 3/64 := by
  have hWnonneg := firstWeight_nonneg f
  by_cases hW : firstWeight f = 0
  · rw [hW]
    norm_num
  have hWpos : 0 < firstWeight f := lt_of_le_of_ne hWnonneg (Ne.symm hW)
  have hsqrt : 0 < Real.sqrt (firstWeight f) := Real.sqrt_pos.2 hWpos
  have hsqrt2 : (Real.sqrt (firstWeight f))^2 = firstWeight f :=
    Real.sq_sqrt hWnonneg
  let c : Fin n → ℝ := fun i => firstCoeff f i / Real.sqrt (firstWeight f)
  have hcnorm : (∑ i, (c i)^2) = 1 := by
    calc
      _ = (∑ i, (firstCoeff f i)^2) / (Real.sqrt (firstWeight f))^2 := by
        simp only [c, div_pow, ← Finset.sum_div]
      _ = firstWeight f / firstWeight f := by rw [hsqrt2]; rfl
      _ = 1 := div_self hW
  have hcprod : (∑ i, c i * firstCoeff f i) = Real.sqrt (firstWeight f) := by
    calc
      _ = (∑ i, (firstCoeff f i)^2) / Real.sqrt (firstWeight f) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [c]
        ring
      _ = firstWeight f / Real.sqrt (firstWeight f) := rfl
      _ = Real.sqrt (firstWeight f) := by
        apply (div_eq_iff (ne_of_gt hsqrt)).2
        nlinarith [hsqrt2]
  have hcor := symmetric_indicator_correlation_bound (flipCube n)
    (fun x => Real.sqrt 3 * linearForm c x) f
    (by intro x; dsimp only; rw [linearForm_flip]; ring) hf hmean (hmoment c hcnorm)
  have hmeanprod : avg (fun x => f x * (Real.sqrt 3 * linearForm c x)) =
      Real.sqrt 3 * Real.sqrt (firstWeight f) := by
    calc
      _ = avg (fun x => Real.sqrt 3 * (f x * linearForm c x)) := by
        congr 1
        funext x
        ring
      _ = Real.sqrt 3 * avg (fun x => f x * linearForm c x) := avg_mul_left _ _
      _ = _ := by rw [avg_mul_linearForm, hcprod]
  rw [hmeanprod] at hcor
  have hsqrt3 : (Real.sqrt (3 : ℝ))^2 = 3 := Real.sq_sqrt (by norm_num)
  have hprodnonneg : 0 ≤ Real.sqrt 3 * Real.sqrt (firstWeight f) := by positivity
  have hsq : (Real.sqrt 3 * Real.sqrt (firstWeight f))^2 ≤ (3/8 : ℝ)^2 := by
    nlinarith
  rw [mul_pow, hsqrt3, hsqrt2] at hsq
  nlinarith

end
end SharpEighth


/-! ## MomentInduction -/
open scoped BigOperators

namespace SharpEighth

noncomputable section

set_option maxHeartbeats 0

/-- The coordinate-deletion identity for ordered orbit sums. -/
def OrbitCoordinateRecurrence : Prop :=
  ∀ (n : ℕ) (p : Part) (a : ℝ) (z : Fin n → ℝ),
    ((coordinateParts p).map (taggedEval a (fun q => orbit q z))).sum =
      orbit p (Fin.cons a z)

theorem momentPoly_matches_dimension_of_coordinate
    (hrec : OrbitCoordinateRecurrence) :
    ∀ (n : ℕ) (c : Fin n → ℝ) (j : ℕ), j ≤ 9 →
      symEval (fun p => orbit p (fun i => (c i)^2)) (momentPoly j) =
        avg (fun x => (linearForm c x)^(2*j)) := by
  intro n
  induction n with
  | zero =>
    intro c j hj
    exact momentPoly_matches_zero_dimension c j hj
  | succ n ih =>
    intro c j hj
    let a : ℝ := c 0
    let d : Fin n → ℝ := fun i => c i.succ
    have hc : c = Fin.cons a d := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hc]
    have hz : (fun i => (Fin.cons a d i)^2) =
        Fin.cons (a^2) (fun i => (d i)^2) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hz]
    rw [momentPoly_coordinate_recurrence (a^2)
      (fun p => orbit p (fun i => (d i)^2))
      (fun p => orbit p (Fin.cons (a^2) (fun i => (d i)^2)))
      (fun p => hrec n p (a^2) (fun i => (d i)^2)) j hj]
    rw [even_moment_cons]
    rw [list_range_sum_eq_fin]
    rw [← Fin.sum_univ_eq_sum_range (fun k =>
      ((2*j).choose (2*k) : ℝ) * a^(2*k) *
        avg (fun x => (linearForm d x)^(2*(j-k)))) (j+1)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [ih d (j-k.val) (by omega)]
    rw [← pow_mul]

theorem normalized_P_bound_of_coordinate
    (hrec : OrbitCoordinateRecurrence) {n : ℕ} (c : Fin n → ℝ)
    (hnorm : (∑ i, (c i)^2) = 1) :
    avg (fun x => P (Real.sqrt 3 * linearForm c x)) ≤ 3/16 := by
  apply normalized_P_bound_of_orbit_moments c hnorm
  · intro p a b
    exact symEval_squarePoly_nonneg p (fun i => (c i)^2) a b (fun i => sq_nonneg (c i))
  · intro j hj
    exact (momentPoly_matches_dimension_of_coordinate hrec n c j (by omega)).symm

theorem sharp_eighth_of_coordinate
    (hrec : OrbitCoordinateRecurrence) {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hmean : avg f = 1/8) :
    firstWeight f ≤ 3/64 := by
  apply sharp_eighth_of_moment_bound f hf hmean
  intro c hc
  exact normalized_P_bound_of_coordinate hrec c hc


end
end SharpEighth


/-! ## Sharpness -/
open scoped BigOperators

namespace SharpEighth

noncomputable section

/-- A singleton in the three-dimensional Boolean cube. -/
def eighthSingleton (x : Fin 3 → Bool) : ℝ :=
  if x = (fun _ => true) then 1 else 0

theorem eighthSingleton_boolean (x : Fin 3 → Bool) :
    eighthSingleton x = 0 ∨ eighthSingleton x = 1 := by
  classical
  by_cases h : x = (fun _ => true) <;> simp [eighthSingleton, h]

theorem eighthSingleton_mean : avg eighthSingleton = 1/8 := by
  classical
  norm_num [avg, eighthSingleton, Fintype.card_fun]

theorem eighthSingleton_coeff (i : Fin 3) : firstCoeff eighthSingleton i = 1/8 := by
  classical
  norm_num [firstCoeff, avg, eighthSingleton, mul_ite, sign, Fintype.card_fun]

theorem eighthSingleton_weight : firstWeight eighthSingleton = 3/64 := by
  unfold firstWeight
  simp only [eighthSingleton_coeff]
  norm_num

theorem eighth_weight_attained :
    ∃ f : (Fin 3 → Bool) → ℝ,
      (∀ x, f x = 0 ∨ f x = 1) ∧ avg f = 1/8 ∧ firstWeight f = 3/64 := by
  exact ⟨eighthSingleton, eighthSingleton_boolean, eighthSingleton_mean,
    eighthSingleton_weight⟩

/-- Adjoin one Boolean coordinate that the function does not use. -/
def ignoreHead {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (x : Fin (n + 1) → Bool) : ℝ := f (fun i => x i.succ)

theorem ignoreHead_mean {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    avg (ignoreHead f) = avg f := by
  rw [avg_cube_cons]
  simp only [ignoreHead, Fin.cons_succ]
  ring

theorem ignoreHead_coeff_zero {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    firstCoeff (ignoreHead f) 0 = 0 := by
  unfold firstCoeff
  rw [avg_cube_cons]
  change (avg (fun x => (1 : ℝ) * f x) +
    avg (fun x => (-1 : ℝ) * f x)) / 2 = 0
  rw [avg_mul_left, avg_mul_left]
  ring

theorem ignoreHead_coeff_succ {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    firstCoeff (ignoreHead f) i.succ = firstCoeff f i := by
  unfold firstCoeff
  rw [avg_cube_cons]
  simp only [ignoreHead, Fin.cons_succ]
  ring

theorem ignoreHead_weight {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    firstWeight (ignoreHead f) = firstWeight f := by
  unfold firstWeight
  rw [Fin.sum_univ_succ]
  simp only [ignoreHead_coeff_zero, ignoreHead_coeff_succ, zero_pow (by decide : 2 ≠ 0),
    zero_add]

theorem eighth_weight_attained_add (k : ℕ) :
    ∃ f : (Fin (k + 3) → Bool) → ℝ,
      (∀ x, f x = 0 ∨ f x = 1) ∧ avg f = 1/8 ∧ firstWeight f = 3/64 := by
  induction k with
  | zero => exact eighth_weight_attained
  | succ k ih =>
    obtain ⟨f, hf, hm, hw⟩ := ih
    change ∃ f : (Fin ((k + 3) + 1) → Bool) → ℝ, _
    refine ⟨ignoreHead f, ?_, ?_, ?_⟩
    · intro x
      exact hf _
    · rw [ignoreHead_mean, hm]
    · rw [ignoreHead_weight, hw]

/-- The sharp value is attained in every Boolean-cube dimension at least three. -/
theorem eighth_weight_attained_in_dimension (n : ℕ) (hn : 3 ≤ n) :
    ∃ f : (Fin n → Bool) → ℝ,
      (∀ x, f x = 0 ∨ f x = 1) ∧ avg f = 1/8 ∧ firstWeight f = 3/64 := by
  have h := eighth_weight_attained_add (n - 3)
  have he : n - 3 + 3 = n := by omega
  rw [he] at h
  exact h

end
end SharpEighth


/-! ## AverageDistance -/
open scoped BigOperators
open Finset

namespace SharpEighth

noncomputable section

/-- Hamming distance, expressed as a real-valued count of differing coordinates. -/
def hammingDistance {n : ℕ} (x y : Fin n → Bool) : ℝ :=
  ∑ i, if x i = y i then 0 else 1

/-- The normalized double weighted cube average. For a nonempty Boolean
indicator this is the mean Hamming distance between two independent uniform
points of its support, with the diagonal pairs included. -/
def weightedHammingAverage {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  avg (fun x => avg (fun y => f x * f y * hammingDistance x y)) / (avg f) ^ 2

theorem hamming_coordinate_identity (b c : Bool) :
    (if b = c then (0 : ℝ) else 1) = (1 - sign b * sign c) / 2 := by
  cases b <;> cases c <;> norm_num [sign]

theorem weighted_coordinate_average {n : ℕ}
    (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    avg (fun x => avg (fun y =>
      f x * f y * (if x i = y i then (0 : ℝ) else 1))) =
        ((avg f) ^ 2 - (firstCoeff f i) ^ 2) / 2 := by
  have hinner (x : Fin n → Bool) :
      avg (fun y => f x * f y * (if x i = y i then (0 : ℝ) else 1)) =
        (f x * avg f - (sign (x i) * f x) * firstCoeff f i) / 2 := by
    calc
      _ = avg (fun y =>
          (f x * f y - (sign (x i) * f x) * (sign (y i) * f y)) / 2) := by
        congr 1
        funext y
        rw [hamming_coordinate_identity]
        ring
      _ = _ := by
        rw [avg_div, avg_sub, avg_mul_left, avg_mul_left]
        rfl
  simp_rw [hinner]
  rw [avg_div, avg_sub, avg_mul_right, avg_mul_right]
  change (avg f * avg f - firstCoeff f i * firstCoeff f i) / 2 = _
  ring

theorem weighted_hamming_numerator {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    avg (fun x => avg (fun y => f x * f y * hammingDistance x y)) =
      ((n : ℝ) * (avg f) ^ 2 - firstWeight f) / 2 := by
  calc
    _ = ∑ i : Fin n, avg (fun x => avg (fun y =>
        f x * f y * (if x i = y i then (0 : ℝ) else 1))) := by
      simp only [hammingDistance, mul_sum, avg_sum]
    _ = ∑ i : Fin n, ((avg f) ^ 2 - (firstCoeff f i) ^ 2) / 2 := by
      simp_rw [weighted_coordinate_average]
    _ = _ := by
      rw [← sum_div, sum_sub_distrib]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, firstWeight]

theorem weighted_hamming_identity {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hmean : avg f ≠ 0) :
    weightedHammingAverage f = (n : ℝ) / 2 - firstWeight f / (2 * (avg f) ^ 2) := by
  unfold weightedHammingAverage
  rw [weighted_hamming_numerator]
  field_simp
  ring

/-- The Ahlswede--Katona average-distance bound at density one eighth follows
from the sharp first-level Fourier-weight bound. -/
theorem average_distance_eighth_of_weight_bound {n : ℕ}
    (f : (Fin n → Bool) → ℝ) (hmean : avg f = 1 / 8)
    (hweight : firstWeight f ≤ 3 / 64) :
    ((n : ℝ) - 3) / 2 ≤ weightedHammingAverage f := by
  rw [weighted_hamming_identity f (by rw [hmean]; norm_num), hmean]
  norm_num
  linarith

theorem eighth_distance_attained_in_dimension (n : ℕ) (hn : 3 ≤ n) :
    ∃ f : (Fin n → Bool) → ℝ,
      (∀ x, f x = 0 ∨ f x = 1) ∧ avg f = 1 / 8 ∧
        weightedHammingAverage f = ((n : ℝ) - 3) / 2 := by
  obtain ⟨f, hf, hm, hw⟩ := eighth_weight_attained_in_dimension n hn
  refine ⟨f, hf, hm, ?_⟩
  rw [weighted_hamming_identity f (by rw [hm]; norm_num), hm, hw]
  ring


end
end SharpEighth


/-! ## HingeSharpness -/
open scoped BigOperators

namespace SharpEighth

noncomputable section

def threeEqualCoefficients (_ : Fin 3) : ℝ := 1 / Real.sqrt 3

theorem threeEqualCoefficients_normalized :
    (∑ i, (threeEqualCoefficients i) ^ 2) = 1 := by
  norm_num [threeEqualCoefficients, div_pow, Real.sq_sqrt]

theorem threeEqualCoefficients_scaled (x : Fin 3 → Bool) :
    Real.sqrt 3 * linearForm threeEqualCoefficients x = ∑ i, sign (x i) := by
  unfold linearForm threeEqualCoefficients
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  field_simp

/-- The sharp hinge estimate is attained by three equal Rademacher coefficients. -/
theorem threeEqualCoefficients_hinge :
    avg (fun x => max 0
      (|Real.sqrt 3 * linearForm threeEqualCoefficients x| - 9 / 4)) = 3 / 16 := by
  simp_rw [threeEqualCoefficients_scaled]
  simp_rw [avg_cube_cons]
  norm_num [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sign, avg_const]

theorem hinge_bound_attained :
    ∃ c : Fin 3 → ℝ, (∑ i, (c i) ^ 2) = 1 ∧
      avg (fun x => max 0 (|Real.sqrt 3 * linearForm c x| - 9 / 4)) = 3 / 16 := by
  exact ⟨threeEqualCoefficients, threeEqualCoefficients_normalized,
    threeEqualCoefficients_hinge⟩


end
end SharpEighth


/-! ## Result -/
open scoped BigOperators

namespace SharpEighth

noncomputable section

theorem orbit_coordinate_recurrence : OrbitCoordinateRecurrence := by
  intro n p a z
  exact orbit_coordinateParts p a z

/-- The exact polynomial certificate bounds every normalized finite Rademacher sum. -/
theorem normalized_rademacher_polynomial_bound {n : ℕ} (c : Fin n → ℝ)
    (hnorm : (∑ i, (c i)^2) = 1) :
    avg (fun x => P (Real.sqrt 3 * linearForm c x)) ≤ 3/16 := by
  exact normalized_P_bound_of_coordinate orbit_coordinate_recurrence c hnorm

/-- The resulting positive-part bound is dimension independent. -/
theorem sharp_rademacher_hinge {n : ℕ} (c : Fin n → ℝ)
    (hnorm : (∑ i, (c i)^2) = 1) :
    avg (fun x => max 0 (|Real.sqrt 3 * linearForm c x| - 9/4)) ≤ 3/16 := by
  exact (avg_le_avg (fun x => majorant (Real.sqrt 3 * linearForm c x))).trans
    (normalized_rademacher_polynomial_bound c hnorm)

/-- The sharp first-level Fourier bound for Boolean functions of mean one eighth. -/
theorem sharp_eighth_fourier_bound {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hmean : avg f = 1/8) :
    firstWeight f ≤ 3/64 := by
  exact sharp_eighth_of_coordinate orbit_coordinate_recurrence f hf hmean

/-- The Ahlswede--Katona average-distance bound at density one eighth. -/
theorem average_distance_eighth {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hmean : avg f = 1/8) :
    ((n : ℝ) - 3)/2 ≤ weightedHammingAverage f := by
  exact average_distance_eighth_of_weight_bound f hmean
    (sharp_eighth_fourier_bound f hf hmean)

def attainableEighthWeights (n : ℕ) : Set ℝ :=
  {w | ∃ f : (Fin n → Bool) → ℝ,
    (∀ x, f x = 0 ∨ f x = 1) ∧ avg f = 1/8 ∧ firstWeight f = w}

/-- In every dimension at least three, the exact maximum is three sixty-fourths. -/
theorem exact_eighth_fourier_optimum (n : ℕ) (hn : 3 ≤ n) :
    IsGreatest (attainableEighthWeights n) (3/64 : ℝ) := by
  constructor
  · exact eighth_weight_attained_in_dimension n hn
  · intro w hw
    obtain ⟨f, hf, hm, rfl⟩ := hw
    exact sharp_eighth_fourier_bound f hf hm

def attainableEighthDistances (n : ℕ) : Set ℝ :=
  {d | ∃ f : (Fin n → Bool) → ℝ,
    (∀ x, f x = 0 ∨ f x = 1) ∧ avg f = 1/8 ∧ weightedHammingAverage f = d}

/-- In every dimension at least three, the exact minimum average distance is
one half of the number of free coordinates in a codimension-three subcube. -/
theorem exact_eighth_distance_optimum (n : ℕ) (hn : 3 ≤ n) :
    IsLeast (attainableEighthDistances n) (((n : ℝ)-3)/2) := by
  constructor
  · exact eighth_distance_attained_in_dimension n hn
  · intro d hd
    obtain ⟨f, hf, hm, rfl⟩ := hd
    exact average_distance_eighth f hf hm

end
end SharpEighth
