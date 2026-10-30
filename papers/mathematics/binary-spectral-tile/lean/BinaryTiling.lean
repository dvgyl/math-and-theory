import BinaryTilingCodes

set_option autoImplicit false
namespace BinaryFuglede

lemma sum_point_tile_bijective :
    Function.Bijective (fun p : Fin 64 × Fin 8 => point p.1 + tileShift p.2) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro v
    obtain ⟨k, rfl⟩ := decodeFin_bijective.2 v
    obtain ⟨i, j, h⟩ := code_tiling k
    refine ⟨(i,j), ?_⟩
    change decodeFin (pointCode i) + decodeFin (tileCode j) = decodeFin k
    rw [← decodeFin_xor, h]
  · simp [Fintype.card_prod, card_V]

lemma point_injective : Function.Injective point := by
  intro i j h
  have hp : (fun p : Fin 64 × Fin 8 => point p.1 + tileShift p.2) (i,0) =
      (fun p : Fin 64 × Fin 8 => point p.1 + tileShift p.2) (j,0) := by simpa using congrArg (· + tileShift 0) h
  exact congrArg Prod.fst (sum_point_tile_bijective.1 hp)

lemma tileShift_injective : Function.Injective tileShift := by
  intro i j h
  have hp : (fun p : Fin 64 × Fin 8 => point p.1 + tileShift p.2) (0,i) =
      (fun p : Fin 64 × Fin 8 => point p.1 + tileShift p.2) (0,j) := by simpa using congrArg (point 0 + ·) h
  exact congrArg Prod.snd (sum_point_tile_bijective.1 hp)

noncomputable def pointEquiv : Fin 64 ≃ Eset :=
  Equiv.ofBijective (fun i => ⟨point i, ⟨i,rfl⟩⟩)
    ⟨fun _ _ h => point_injective (congrArg Subtype.val h),
      fun x => by obtain ⟨i, hi⟩ := x.property; exact ⟨i, Subtype.ext hi⟩⟩

noncomputable def tileEquiv : Fin 8 ≃ Tset :=
  Equiv.ofBijective (fun i => ⟨tileShift i, ⟨i,rfl⟩⟩)
    ⟨fun _ _ h => tileShift_injective (congrArg Subtype.val h),
      fun x => by obtain ⟨i, hi⟩ := x.property; exact ⟨i, Subtype.ext hi⟩⟩

lemma card_Eset [Fintype Eset] : Fintype.card Eset = 64 := by
  rw [← Fintype.card_congr pointEquiv]
  rfl

lemma card_Tset [Fintype Tset] : Fintype.card Tset = 8 := by
  rw [← Fintype.card_congr tileEquiv]
  rfl

lemma explicit_tiling : TilingPair Eset Tset := by
  constructor
  · intro p q h
    obtain ⟨i,hi⟩ := p.1.property
    obtain ⟨j,hj⟩ := p.2.property
    obtain ⟨k,hk⟩ := q.1.property
    obtain ⟨l,hl⟩ := q.2.property
    have hc : point i + tileShift j = point k + tileShift l := by simpa [hi,hj,hk,hl] using h
    have he : (i,j) = (k,l) := sum_point_tile_bijective.1 hc
    apply Prod.ext
    · apply Subtype.ext
      simpa [hi,hk] using congrArg (fun z : Fin 64 × Fin 8 => point z.1) he
    · apply Subtype.ext
      simpa [hj,hl] using congrArg (fun z : Fin 64 × Fin 8 => tileShift z.2) he
  · intro v
    obtain ⟨⟨i,j⟩, h⟩ := sum_point_tile_bijective.2 v
    exact ⟨(⟨point i,⟨i,rfl⟩⟩,⟨tileShift j,⟨j,rfl⟩⟩), h⟩

end BinaryFuglede
