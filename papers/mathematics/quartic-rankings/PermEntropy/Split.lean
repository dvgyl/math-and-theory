import PermEntropy.FiniteEntropy
import PermEntropy.Ranking

noncomputable section
namespace PermEntropy

theorem list_eq_of_word_filter_eq {V : Type*} (f : V → Bool)
    (l k : List V) (hw : l.map f = k.map f)
    (ht : l.filter f = k.filter f)
    (hf : l.filter (fun a => !(f a)) = k.filter (fun a => !(f a))) : l = k := by
  induction l generalizing k with
  | nil =>
    cases k with
    | nil => rfl
    | cons b k => simp at hw
  | cons a l ih =>
    cases k with
    | nil => simp at hw
    | cons b k =>
      have hw' := List.cons.inj hw
      by_cases ha : f a = true
      · have hb : f b = true := hw'.1 ▸ ha
        simp [ha, hb] at ht hf
        obtain ⟨hab, ht⟩ := ht
        subst b
        exact congrArg (List.cons a) (ih k hw'.2 ht hf)
      · have ha' : f a = false := Bool.eq_false_iff.mpr ha
        have hb : f b = false := hw'.1 ▸ ha'
        simp [ha', hb] at ht hf
        obtain ⟨hab, hf⟩ := hf
        subst b
        exact congrArg (List.cons a) (ih k hw'.2 ht hf)

namespace Ranking
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem binary_encoding_injective (s : Finset V) :
    Function.Injective (fun r : Ranking V =>
      ((r.restrict s, r.restrict sᶜ), r.membershipWord s)) := by
  intro r t h
  have hp := congrArg Prod.fst h
  have hl := congrArg Prod.fst hp
  have hr := congrArg Prod.snd hp
  have hw := congrArg Prod.snd h
  apply Ranking.ext
  apply list_eq_of_word_filter_eq (fun v => decide (v ∈ s))
  · simpa only [ofFn_membershipWord] using congrArg List.ofFn hw
  · simpa only [order_restrict, map_filterList] using
      congrArg (fun x : Ranking s => x.order.map Subtype.val) hl
  · have h' := congrArg (fun x : Ranking (↥(sᶜ : Finset V)) => x.order.map Subtype.val) hr
    simp only [order_restrict, map_filterList] at h'
    simpa only [Finset.mem_compl, decide_not] using h'

end Ranking

namespace FinDist
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem entropy_ranking_split (p : FinDist (Ranking V)) (s : Finset V) :
    p.entropy ≤ (p.map (fun r => r.restrict s)).entropy +
      (p.map (fun r => r.restrict sᶜ)).entropy +
      (p.map (fun r => r.membershipWord s)).entropy := by
  let f := fun r : Ranking V => (r.restrict s, r.restrict sᶜ)
  let g := fun r : Ranking V => r.membershipWord s
  have h := p.entropy_pair_le_add f g
  rw [p.entropy_map_injective _ (Ranking.binary_encoding_injective s)] at h
  exact h.trans (add_le_add_right (p.entropy_pair_le_add _ _) _)

end FinDist
end PermEntropy
