import BinaryObstruction
import BinarySubspacePrelude
import BinaryTilingDefs

set_option autoImplicit false
namespace BinaryFuglede

lemma difference_free_mem_allowed (v : V) (hv : v ≠ 0)
    (havoid : ¬ ∃ i j : Fin 64, point i + point j = v) : v ∈ Allowed := by
  obtain ⟨n, rfl⟩ := decodeFin_bijective.surjective v
  rcases code_difference_cover n with hn | ⟨a, ha⟩ | hd
  · exfalso
    apply hv
    rw [hn]
    exact decode_zero
  · exact ⟨a, by simp only [allowedShift, ha]⟩
  · exfalso
    apply havoid
    refine ⟨(differenceWitness n).1, (differenceWitness n).2, ?_⟩
    change decodeFin (pointCode (differenceWitness n).1) +
      decodeFin (pointCode (differenceWitness n).2) = decodeFin n
    rw [← decodeFin_xor, hd]

lemma permittedCode_of_decode_mem_allowed (n : Fin 512)
    (h : decodeFin n ∈ Allowed) : permittedCode n = true := by
  obtain ⟨a, ha⟩ := h
  have hc : allowedCode a = n := decodeFin_injective ha
  rw [← hc]
  exact allowedCode_permitted a

lemma no_allowed_cube (a b c : V) (ha : a ∈ Allowed) (hb : b ∈ Allowed)
    (hc : c ∈ Allowed) (hab : a + b ∈ Allowed) (hac : a + c ∈ Allowed)
    (hbc : b + c ∈ Allowed) (habc : a + b + c ∈ Allowed) : False := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨k, rfl⟩ := hc
  apply no_allowed_cube_codes i j k
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply permittedCode_of_decode_mem_allowed
    simpa only [decodeFin_xor, allowedShift] using hab
  · apply permittedCode_of_decode_mem_allowed
    simpa only [decodeFin_xor, allowedShift] using hac
  · apply permittedCode_of_decode_mem_allowed
    simpa only [decodeFin_xor, allowedShift] using hbc
  · apply permittedCode_of_decode_mem_allowed
    simpa only [decodeFin_xor, allowedShift] using habc

lemma no_three_dimensional_difference_free (H : Submodule (ZMod 2) V)
    (hfin : Module.finrank (ZMod 2) H = 3)
    (havoid : ∀ v ∈ H, v ≠ 0 → ¬ ∃ i j : Fin 64, point i + point j = v) : False := by
  obtain ⟨a, b, c, ha, hb, hc, ha0, hb0, hc0, hab0, hac0, hbc0, habc0⟩ :=
    finrank_three_has_cube H hfin
  have hallowed (v : V) (hmem : v ∈ H) (hzero : v ≠ 0) : v ∈ Allowed :=
    difference_free_mem_allowed v hzero (havoid v hmem hzero)
  exact no_allowed_cube a b c
    (hallowed a ha ha0) (hallowed b hb hb0) (hallowed c hc hc0)
    (hallowed (a + b) (H.add_mem ha hb) hab0)
    (hallowed (a + c) (H.add_mem ha hc) hac0)
    (hallowed (b + c) (H.add_mem hb hc) hbc0)
    (hallowed (a + b + c) (H.add_mem (H.add_mem ha hb) hc) habc0)

lemma subspace_difference_free_of_tiling (H : Submodule (ZMod 2) V)
    (ht : TilingPair Eset (H : Set V)) :
    ∀ v ∈ H, v ≠ 0 → ¬ ∃ i j : Fin 64, point i + point j = v := by
  intro v hv hv0 hex
  obtain ⟨i, j, hij⟩ := hex
  let p : Eset × (H : Set V) := (⟨point i, ⟨i, rfl⟩⟩, ⟨0, H.zero_mem⟩)
  let q : Eset × (H : Set V) := (⟨point j, ⟨j, rfl⟩⟩, ⟨v, hv⟩)
  have heq : (p.1 : V) + (p.2 : V) = (q.1 : V) + (q.2 : V) := by
    change point i + 0 = point j + v
    rw [← hij]
    simp only [add_zero]
    calc
      point i = point i + (point j + point j) := by rw [add_self, add_zero]
      _ = point j + (point i + point j) := by abel
  have hpq : p = q := ht.injective heq
  have hz : (0 : V) = v := congrArg (fun r : Eset × (H : Set V) => (r.2 : V)) hpq
  exact hv0 hz.symm

lemma no_three_dimensional_tiling (H : Submodule (ZMod 2) V)
    (hfin : Module.finrank (ZMod 2) H = 3) : ¬ TilingPair Eset (H : Set V) := by
  intro ht
  exact no_three_dimensional_difference_free H hfin (subspace_difference_free_of_tiling H ht)

end BinaryFuglede
