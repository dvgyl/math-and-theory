import BinaryNoLinear

set_option autoImplicit false
namespace BinaryFuglede

/-- Every genuine complement of the displayed 64-point tile has eight points. -/
lemma complement_card_eight (B : Set V) [Fintype Eset] [Fintype B]
    (hEcard : Fintype.card Eset = 64) (ht : TilingPair Eset B) :
    Fintype.card B = 8 := by
  have hc := Fintype.card_of_bijective ht
  simp only [Fintype.card_prod, hEcard, card_V] at hc
  omega

lemma add_nonzero_of_distinct (u v : V) (hne : u ≠ v) : u + v ≠ 0 := by
  intro h
  have heq := congrArg (fun x : V => x + v) h
  have huv : u = v := by simpa only [add_assoc, add_self, add_zero, zero_add] using heq
  exact hne huv

/-- Two distinct points of an actual tiling complement give a nonzero shift
outside the difference set of the tile. -/
lemma complement_difference_free (B : Set V) (ht : TilingPair Eset B)
    (u v : V) (hu : u ∈ B) (hv : v ∈ B) (hne : u ≠ v) :
    ¬ ∃ i j : Fin 64, point i + point j = u + v := by
  rintro ⟨i, j, hij⟩
  let p : Eset × B := (⟨point i, ⟨i, rfl⟩⟩, ⟨u, hu⟩)
  let q : Eset × B := (⟨point j, ⟨j, rfl⟩⟩, ⟨v, hv⟩)
  have heq : (p.1 : V) + (p.2 : V) = (q.1 : V) + (q.2 : V) := by
    change point i + u = point j + v
    calc
      point i + u = (point i + point j) + point j + u := by
        rw [add_assoc (point i) (point j) (point j), add_self, add_zero]
      _ = (u + v) + point j + u := by rw [hij]
      _ = point j + v + (u + u) := by abel
      _ = point j + v := by rw [add_self, add_zero]
  have hpq : p = q := ht.injective heq
  exact hne (congrArg (fun r : Eset × B => (r.2 : V)) hpq)

lemma complement_difference_allowed (B : Set V) (ht : TilingPair Eset B)
    (u v : V) (hu : u ∈ B) (hv : v ∈ B) (hne : u ≠ v) :
    u + v ∈ Allowed :=
  difference_free_mem_allowed (u + v) (add_nonzero_of_distinct u v hne)
    (complement_difference_free B ht u v hu hv hne)

/-- A finite set has a point outside any strictly smaller finite list. -/
lemma exists_mem_outside_finset (B : Set V) [Fintype B] (F : Finset V)
    (hcard : F.card < Fintype.card B) : ∃ x : V, x ∈ B ∧ x ∉ F := by
  classical
  by_contra! h
  have hsub : B.toFinset ⊆ F := by
    intro x hx
    exact h x (by simpa using hx)
  have hc := Finset.card_le_card hsub
  rw [Set.toFinset_card] at hc
  omega

/-- An eight-point complement cannot have a nonzero translation period.
The proof applies the verified forbidden-cube certificate to seven actual
differences of complement points, rather than to a relaxed representation. -/
theorem not_periodic_complement (B : Set V) [Fintype Eset] [Fintype B]
    (hEcard : Fintype.card Eset = 64) (ht : TilingPair Eset B) :
    ¬ Periodic B := by
  classical
  intro hper
  obtain ⟨p, hp, hperiod⟩ := hper
  have hcard := complement_card_eight B hEcard ht
  obtain ⟨u, hu, _⟩ := exists_mem_outside_finset B ∅ (by simp [hcard])
  have hup : u + p ∈ B := (hperiod u).mp hu
  have htwo : ({u, u + p} : Finset V).card < Fintype.card B := by
    have hc := List.toFinset_card_le (l := [u, u + p])
    simpa only [List.toFinset_cons, List.toFinset_nil, List.length_cons,
      List.length_nil, hcard] using (lt_of_le_of_lt hc (by norm_num : 2 < 8))
  obtain ⟨v, hv, hvout⟩ := exists_mem_outside_finset B {u, u + p} htwo
  have hvne : v ≠ u ∧ v ≠ u + p := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hvout
  have hvu : v ≠ u := hvne.1
  have hvup : v ≠ u + p := hvne.2
  have hvp : v + p ∈ B := (hperiod v).mp hv
  have hfour : ({u, u + p, v, v + p} : Finset V).card < Fintype.card B := by
    have hc := List.toFinset_card_le (l := [u, u + p, v, v + p])
    simpa only [List.toFinset_cons, List.toFinset_nil, List.length_cons,
      List.length_nil, hcard] using (lt_of_le_of_lt hc (by norm_num : 4 < 8))
  obtain ⟨w, hw, hwout⟩ :=
    exists_mem_outside_finset B {u, u + p, v, v + p} hfour
  have hwne : w ≠ u ∧ w ≠ u + p ∧ w ≠ v ∧ w ≠ v + p := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hwout
  have hupne : u ≠ u + p := by
    intro he
    have hp0 : (0 : V) = p := add_left_cancel (by simpa only [add_zero] using he)
    exact hp hp0.symm
  have hpA : p ∈ Allowed := by
    have hc := complement_difference_allowed B ht u (u + p) hu hup hupne
    simpa only [← add_assoc, add_self, zero_add] using hc
  have hbA := complement_difference_allowed B ht u v hu hv hvu.symm
  have hcA := complement_difference_allowed B ht u w hu hw hwne.1.symm
  have habA : p + (u + v) ∈ Allowed := by
    have hc := complement_difference_allowed B ht (u + p) v hup hv hvup.symm
    convert hc using 1
    abel
  have hacA : p + (u + w) ∈ Allowed := by
    have hc := complement_difference_allowed B ht (u + p) w hup hw hwne.2.1.symm
    convert hc using 1
    abel
  have hbcA : (u + v) + (u + w) ∈ Allowed := by
    have hc := complement_difference_allowed B ht v w hv hw hwne.2.2.1.symm
    have he : (u + v) + (u + w) = v + w := by
      calc
        _ = (v + w) + (u + u) := by abel
        _ = v + w := by rw [add_self, add_zero]
    rwa [he]
  have habcA : p + (u + v) + (u + w) ∈ Allowed := by
    have hc := complement_difference_allowed B ht (v + p) w hvp hw hwne.2.2.2.symm
    have he : p + (u + v) + (u + w) = (v + p) + w := by
      calc
        _ = ((v + p) + w) + (u + u) := by abel
        _ = (v + p) + w := by rw [add_self, add_zero]
    rwa [he]
  exact no_allowed_cube p (u + v) (u + w) hpA hbA hcA habA hacA hbcA habcA

end BinaryFuglede
