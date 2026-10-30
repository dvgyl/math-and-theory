import InfoE3.Defs

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace InfoE3

/-- A literal CI row for distinct singletons i,j outside the conditioning set K. -/
def ciQuad (i j : Fin 5) (K : Mask 5) : Nat × Nat × Nat × Nat :=
  (K.val + 2 ^ i.val, K.val + 2 ^ j.val, K.val,
    K.val + 2 ^ i.val + 2 ^ j.val)

/-- Explicit left inverse of the finite eighty-row catalog. -/
def ciLookup (q : Nat × Nat × Nat × Nat) : Fin 80 :=
  let key := q.1 * 32768 + q.2.1 * 1024 + q.2.2.1 * 32 + q.2.2.2
  ⟨(((if key < 380027 then (if key < 206926 then (if key < 108619 then (if key < 73738 then (if key < 40969 then (if key < 36869 then 0 else 8) else (if key < 49169 then 16 else (if key < 69638 then 24 else 32))) else (if key < 103463 then (if key < 81938 then 40 else 48) else (if key < 104519 then 33 else (if key < 107563 then 9 else 41)))) else (if key < 170119 then (if key < 116819 then (if key < 115763 then 17 else 49) else (if key < 139276 then 25 else (if key < 147476 then 56 else 64))) else (if key < 176269 then (if key < 173101 then 1 else 57) else (if key < 181301 then 18 else (if key < 184469 then 65 else 26))))) else (if key < 278552 then (if key < 242863 then (if key < 215126 then (if key < 209038 then 58 else 42) else (if key < 217238 then 66 else (if key < 240751 then 50 else 60))) else (if key < 248951 then (if key < 243919 then 44 else 20) else (if key < 251063 then 68 else (if key < 252119 then 52 else 28)))) else (if key < 340238 then (if key < 307469 then (if key < 305419 then 72 else 2) else (if key < 312377 then 10 else (if key < 319769 then 73 else 27))) else (if key < 352538 then (if key < 346202 then 34 else 74) else (if key < 374063 then 51 else (if key < 375119 then 36 else 12)))))) else (if key < 614938 then (if key < 485726 then (if key < 440719 then (if key < 387419 then (if key < 386363 then 76 else 53) else (if key < 413852 then 29 else (if key < 418076 then 75 else 67))) else (if key < 451901 then (if key < 447677 then 4 else 77) else (if key < 455069 then 69 else (if key < 481502 then 30 else 78)))) else (if key < 522719 then (if key < 515327 then (if key < 487838 then 70 else 54) else (if key < 519551 then 79 else (if key < 521663 then 71 else 55))) else (if key < 578069 then (if key < 576019 then 31 else 3) else (if key < 582169 then 11 else (if key < 610838 then 19 else 35))))) else (if key < 750238 then (if key < 680476 then (if key < 645719 then (if key < 644663 then 43 else 37) else (if key < 648763 then 13 else (if key < 649819 then 45 else 21))) else (if key < 714301 then (if key < 711319 then 59 else 5) else (if key < 717469 then 61 else (if key < 748126 then 22 else 62)))) else (if key < 848669 then (if key < 784063 then (if key < 781951 then 46 else 63) else (if key < 785119 then 47 else (if key < 846619 then 23 else 6))) else (if key < 915263 then (if key < 881438 then 14 else 38) else (if key < 916319 then 39 else (if key < 981919 then 15 else 7)))))))) : Nat) % 80, Nat.mod_lt _ (by decide)⟩

/-- The catalog contains each valid elementary CI exactly once. -/
theorem ci_catalog_complete :
    ∀ i j : Fin 5, ∀ K : Mask 5,
      i < j → K.val.testBit i.val = false → K.val.testBit j.val = false →
      ∃! k : Fin 80, ciRows[k.val]! = ciQuad i j K := by
  have hleft : ∀ k : Fin 80, ciLookup ciRows[k.val]! = k := by decide +kernel
  have hright : ∀ i j : Fin 5, ∀ K : Mask 5,
      i < j → K.val.testBit i.val = false → K.val.testBit j.val = false →
      ciRows[(ciLookup (ciQuad i j K)).val]! = ciQuad i j K := by decide +kernel
  intro i j K hij hi hj
  refine ⟨ciLookup (ciQuad i j K), hright i j K hij hi hj, ?_⟩
  intro k hk
  have hx := congrArg ciLookup hk
  rw [hleft] at hx
  exact hx

/-- There are no invalid or extraneous rows in the catalog. -/
theorem ci_catalog_valid :
    ∀ k : Fin 80, ∃ i j : Fin 5, ∃ K : Mask 5,
      i < j ∧ K.val.testBit i.val = false ∧ K.val.testBit j.val = false ∧
      ciRows[k.val]! = ciQuad i j K := by
  intro k
  fin_cases k
  · exact ⟨0, 1, 0, by decide +kernel⟩
  · exact ⟨0, 1, 4, by decide +kernel⟩
  · exact ⟨0, 1, 8, by decide +kernel⟩
  · exact ⟨0, 1, 16, by decide +kernel⟩
  · exact ⟨0, 1, 12, by decide +kernel⟩
  · exact ⟨0, 1, 20, by decide +kernel⟩
  · exact ⟨0, 1, 24, by decide +kernel⟩
  · exact ⟨0, 1, 28, by decide +kernel⟩
  · exact ⟨0, 2, 0, by decide +kernel⟩
  · exact ⟨0, 2, 2, by decide +kernel⟩
  · exact ⟨0, 2, 8, by decide +kernel⟩
  · exact ⟨0, 2, 16, by decide +kernel⟩
  · exact ⟨0, 2, 10, by decide +kernel⟩
  · exact ⟨0, 2, 18, by decide +kernel⟩
  · exact ⟨0, 2, 24, by decide +kernel⟩
  · exact ⟨0, 2, 26, by decide +kernel⟩
  · exact ⟨0, 3, 0, by decide +kernel⟩
  · exact ⟨0, 3, 2, by decide +kernel⟩
  · exact ⟨0, 3, 4, by decide +kernel⟩
  · exact ⟨0, 3, 16, by decide +kernel⟩
  · exact ⟨0, 3, 6, by decide +kernel⟩
  · exact ⟨0, 3, 18, by decide +kernel⟩
  · exact ⟨0, 3, 20, by decide +kernel⟩
  · exact ⟨0, 3, 22, by decide +kernel⟩
  · exact ⟨0, 4, 0, by decide +kernel⟩
  · exact ⟨0, 4, 2, by decide +kernel⟩
  · exact ⟨0, 4, 4, by decide +kernel⟩
  · exact ⟨0, 4, 8, by decide +kernel⟩
  · exact ⟨0, 4, 6, by decide +kernel⟩
  · exact ⟨0, 4, 10, by decide +kernel⟩
  · exact ⟨0, 4, 12, by decide +kernel⟩
  · exact ⟨0, 4, 14, by decide +kernel⟩
  · exact ⟨1, 2, 0, by decide +kernel⟩
  · exact ⟨1, 2, 1, by decide +kernel⟩
  · exact ⟨1, 2, 8, by decide +kernel⟩
  · exact ⟨1, 2, 16, by decide +kernel⟩
  · exact ⟨1, 2, 9, by decide +kernel⟩
  · exact ⟨1, 2, 17, by decide +kernel⟩
  · exact ⟨1, 2, 24, by decide +kernel⟩
  · exact ⟨1, 2, 25, by decide +kernel⟩
  · exact ⟨1, 3, 0, by decide +kernel⟩
  · exact ⟨1, 3, 1, by decide +kernel⟩
  · exact ⟨1, 3, 4, by decide +kernel⟩
  · exact ⟨1, 3, 16, by decide +kernel⟩
  · exact ⟨1, 3, 5, by decide +kernel⟩
  · exact ⟨1, 3, 17, by decide +kernel⟩
  · exact ⟨1, 3, 20, by decide +kernel⟩
  · exact ⟨1, 3, 21, by decide +kernel⟩
  · exact ⟨1, 4, 0, by decide +kernel⟩
  · exact ⟨1, 4, 1, by decide +kernel⟩
  · exact ⟨1, 4, 4, by decide +kernel⟩
  · exact ⟨1, 4, 8, by decide +kernel⟩
  · exact ⟨1, 4, 5, by decide +kernel⟩
  · exact ⟨1, 4, 9, by decide +kernel⟩
  · exact ⟨1, 4, 12, by decide +kernel⟩
  · exact ⟨1, 4, 13, by decide +kernel⟩
  · exact ⟨2, 3, 0, by decide +kernel⟩
  · exact ⟨2, 3, 1, by decide +kernel⟩
  · exact ⟨2, 3, 2, by decide +kernel⟩
  · exact ⟨2, 3, 16, by decide +kernel⟩
  · exact ⟨2, 3, 3, by decide +kernel⟩
  · exact ⟨2, 3, 17, by decide +kernel⟩
  · exact ⟨2, 3, 18, by decide +kernel⟩
  · exact ⟨2, 3, 19, by decide +kernel⟩
  · exact ⟨2, 4, 0, by decide +kernel⟩
  · exact ⟨2, 4, 1, by decide +kernel⟩
  · exact ⟨2, 4, 2, by decide +kernel⟩
  · exact ⟨2, 4, 8, by decide +kernel⟩
  · exact ⟨2, 4, 3, by decide +kernel⟩
  · exact ⟨2, 4, 9, by decide +kernel⟩
  · exact ⟨2, 4, 10, by decide +kernel⟩
  · exact ⟨2, 4, 11, by decide +kernel⟩
  · exact ⟨3, 4, 0, by decide +kernel⟩
  · exact ⟨3, 4, 1, by decide +kernel⟩
  · exact ⟨3, 4, 2, by decide +kernel⟩
  · exact ⟨3, 4, 4, by decide +kernel⟩
  · exact ⟨3, 4, 3, by decide +kernel⟩
  · exact ⟨3, 4, 5, by decide +kernel⟩
  · exact ⟨3, 4, 6, by decide +kernel⟩
  · exact ⟨3, 4, 7, by decide +kernel⟩

theorem exactly_twenty_six_zeros :
    ((List.finRange 80).filter fun k => zeroCI k).length = 26 := by decide +kernel

theorem target_not_zero : zeroCI 47 = false := by decide +kernel

/-- Both copy maps are embeddings of the complete five-element Boolean algebra. -/
theorem orig_injective : ∀ L : Mask 5, Function.Injective (origMask L) := by
  decide +kernel

theorem copy_injective : ∀ L : Mask 5, Function.Injective (copyMask L) := by
  decide +kernel

theorem orig_preserves_inter : ∀ L S T : Mask 5,
    origMask L (S &&& T) = origMask L S &&& origMask L T := by decide +kernel

theorem orig_preserves_union : ∀ L S T : Mask 5,
    origMask L (S ||| T) = origMask L S ||| origMask L T := by decide +kernel

theorem copy_preserves_inter : ∀ L S T : Mask 5,
    copyMask L (S &&& T) = copyMask L S &&& copyMask L T := by decide +kernel

theorem copy_preserves_union : ∀ L S T : Mask 5,
    copyMask L (S ||| T) = copyMask L S ||| copyMask L T := by decide +kernel

theorem copy_fixes_overlap : ∀ L S : Mask 5, S &&& L = S →
    copyMask L S = origMask L S := by decide +kernel

theorem copies_intersection : ∀ L : Mask 5,
    origMask L 31 &&& copyMask L 31 = origMask L L := by decide +kernel

theorem copies_union : ∀ L : Mask 5,
    origMask L 31 ||| copyMask L 31 = fullMask (groundSize L) := by decide +kernel

theorem empty_embeddings : ∀ L : Mask 5,
    origMask L 0 = 0 ∧ copyMask L 0 = 0 := by decide +kernel

theorem ground_size_range : ∀ L : Mask 5, 5 ≤ groundSize L ∧ groundSize L ≤ 10 := by
  decide +kernel

#print axioms ci_catalog_complete
#print axioms ci_catalog_valid
#print axioms copy_preserves_inter
#print axioms copies_union

end InfoE3
