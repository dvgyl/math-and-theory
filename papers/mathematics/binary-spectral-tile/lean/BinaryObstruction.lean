import BinaryData

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BinaryFuglede

def permittedCode (n : Fin 512) : Bool :=
  ([1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 31, 32, 33, 34, 36, 40, 47, 48, 55, 59, 61, 62, 63] : List ℕ).contains n.val

lemma allowedCode_permitted : ∀ a : Fin 28, permittedCode (allowedCode a) = true := by
  decide +kernel

def differenceWitness : Fin 512 → Fin 64 × Fin 64 :=
  ![(63, 63), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (39, 38), (0, 0), (0, 0), (0, 0), (63, 62), (0, 0), (31, 30), (23, 22), (55, 54), (0, 0), (0, 0), (0, 0), (55, 53), (0, 0), (47, 45), (31, 29), (63, 61), (0, 0), (23, 20), (39, 37), (31, 28), (63, 60), (39, 36), (47, 44), (0, 0), (0, 0), (0, 0), (0, 0), (23, 19), (0, 0), (7, 3), (63, 59), (47, 43), (0, 0), (55, 50), (31, 26), (39, 35), (47, 42), (63, 58), (7, 2), (0, 0), (0, 0), (63, 57), (47, 41), (7, 1), (23, 17), (55, 49), (39, 32), (0, 0), (7, 0), (47, 40), (63, 56), (0, 0), (31, 24), (0, 0), (0, 0), (0, 0), (63, 55), (26, 18), (27, 19), (46, 38), (62, 54), (30, 22), (31, 23), (45, 36), (47, 38), (29, 20), (28, 21), (62, 55), (44, 36), (25, 16), (24, 17), (63, 54), (29, 23), (44, 39), (47, 36), (63, 53), (25, 19), (47, 37), (44, 38), (62, 52), (62, 53), (46, 36), (45, 39), (27, 16), (63, 52), (45, 38), (46, 37), (31, 20), (44, 33), (27, 23), (62, 50), (47, 34), (47, 35), (31, 19), (63, 51), (44, 32), (46, 34), (63, 50), (29, 16), (45, 33), (45, 32), (62, 51), (25, 20), (46, 35), (28, 18), (62, 48), (46, 32), (29, 19), (24, 22), (63, 49), (45, 34), (25, 23), (27, 20), (47, 32), (63, 48), (26, 21), (31, 16), (44, 34), (62, 49), (30, 17), (57, 41), (61, 45), (59, 43), (63, 47), (54, 38), (53, 37), (51, 34), (48, 33), (63, 46), (59, 42), (61, 44), (57, 40), (55, 39), (52, 36), (50, 35), (49, 32), (52, 39), (55, 36), (49, 35), (50, 32), (61, 47), (57, 43), (63, 45), (59, 41), (53, 38), (54, 37), (48, 34), (51, 33), (59, 40), (63, 44), (57, 42), (61, 46), (55, 34), (52, 33), (50, 38), (49, 37), (63, 43), (59, 47), (61, 41), (57, 45), (54, 35), (53, 32), (51, 39), (48, 36), (57, 44), (61, 40), (59, 46), (63, 42), (59, 45), (63, 41), (57, 47), (61, 43), (53, 35), (54, 32), (48, 39), (51, 36), (61, 42), (57, 46), (63, 40), (59, 44), (52, 34), (55, 33), (49, 38), (50, 37), (62, 38), (61, 37), (51, 43), (55, 47), (49, 41), (53, 45), (61, 36), (62, 39), (55, 46), (51, 42), (60, 37), (63, 38), (63, 39), (60, 36), (53, 44), (49, 40), (60, 39), (63, 36), (54, 44), (50, 40), (52, 46), (48, 42), (63, 37), (60, 38), (50, 41), (54, 45), (62, 36), (61, 39), (61, 38), (62, 37), (48, 43), (52, 47), (63, 34), (60, 33), (53, 41), (49, 45), (55, 43), (51, 47), (60, 32), (63, 35), (49, 44), (53, 40), (61, 33), (62, 34), (62, 35), (61, 32), (51, 46), (55, 42), (61, 35), (62, 32), (48, 46), (52, 42), (50, 44), (54, 40), (62, 33), (61, 34), (52, 43), (48, 47), (63, 32), (60, 35), (60, 34), (63, 33), (54, 41), (50, 45), (62, 30), (60, 28), (38, 6), (46, 14), (53, 21), (52, 20), (63, 31), (61, 29), (47, 14), (38, 7), (61, 28), (63, 30), (60, 29), (62, 31), (55, 22), (54, 23), (63, 29), (61, 31), (52, 22), (53, 23), (38, 4), (47, 13), (62, 28), (60, 30), (54, 21), (55, 20), (60, 31), (62, 29), (61, 30), (63, 28), (46, 13), (38, 5), (61, 25), (63, 27), (54, 18), (55, 19), (47, 11), (35, 7), (60, 24), (62, 26), (52, 17), (53, 16), (62, 27), (60, 25), (63, 26), (61, 24), (35, 6), (46, 11), (60, 26), (62, 24), (46, 8), (35, 5), (55, 17), (54, 16), (61, 27), (63, 25), (35, 4), (47, 8), (63, 24), (61, 26), (62, 25), (60, 27), (53, 18), (52, 19), (63, 23), (52, 28), (49, 25), (53, 29), (54, 30), (62, 22), (55, 31), (51, 27), (50, 27), (54, 31), (51, 26), (62, 23), (52, 29), (48, 25), (63, 22), (49, 24), (55, 29), (51, 25), (62, 20), (50, 24), (49, 27), (53, 31), (48, 26), (63, 21), (53, 30), (63, 20), (52, 31), (48, 27), (62, 21), (55, 28), (50, 25), (54, 29), (51, 31), (55, 27), (50, 30), (63, 19), (53, 25), (49, 29), (62, 18), (48, 28), (62, 19), (53, 24), (48, 29), (52, 25), (55, 26), (63, 18), (54, 27), (50, 31), (52, 26), (62, 16), (53, 27), (49, 31), (63, 17), (54, 24), (51, 29), (55, 25), (54, 25), (50, 29), (63, 16), (51, 28), (48, 31), (52, 27), (49, 30), (62, 17), (62, 14), (61, 13), (55, 7), (52, 4), (49, 1), (50, 2), (61, 12), (62, 15), (52, 5), (55, 6), (60, 13), (63, 14), (63, 15), (60, 12), (50, 3), (49, 0), (60, 15), (63, 12), (49, 3), (50, 0), (55, 5), (52, 6), (63, 13), (60, 14), (50, 1), (49, 2), (62, 12), (61, 15), (61, 14), (62, 13), (52, 7), (55, 4), (63, 10), (60, 9), (53, 1), (54, 2), (51, 7), (48, 4), (60, 8), (63, 11), (54, 3), (53, 0), (61, 9), (62, 10), (62, 11), (61, 8), (48, 5), (51, 6), (61, 11), (62, 8), (51, 5), (48, 6), (53, 3), (54, 0), (62, 9), (61, 10), (48, 7), (51, 4), (63, 8), (60, 11), (60, 10), (63, 9), (54, 1), (53, 2), (57, 1), (59, 3), (63, 7), (61, 5), (54, 14), (53, 13), (51, 10), (48, 9), (61, 4), (63, 6), (59, 2), (57, 0), (55, 15), (52, 12), (50, 11), (49, 8), (52, 15), (55, 12), (49, 11), (50, 8), (63, 5), (61, 7), (57, 3), (59, 1), (53, 14), (54, 13), (48, 10), (51, 9), (59, 0), (57, 2), (61, 6), (63, 4), (55, 10), (52, 9), (50, 14), (49, 13), (59, 7), (57, 5), (61, 1), (63, 3), (54, 11), (53, 8), (51, 15), (48, 12), (63, 2), (61, 0), (57, 4), (59, 6), (61, 3), (63, 1), (59, 5), (57, 7), (53, 11), (54, 8), (48, 15), (51, 12), (57, 6), (59, 4), (63, 0), (61, 2), (52, 10), (55, 9), (49, 14), (50, 13)]

def DifferenceCovered (n : Fin 512) : Prop :=
    n = 0 ∨ (∃ a : Fin 28, allowedCode a = n) ∨
    xorFin (pointCode (differenceWitness n).1) (pointCode (differenceWitness n).2) = n

instance instDecidableDifferenceCovered (n : Fin 512) : Decidable (DifferenceCovered n) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def blockCode (k : Fin 32) (j : Fin 16) : Fin 512 :=
  ⟨16 * k.val + j.val, by omega⟩

private lemma difference_chunk_0 : ∀ j : Fin 16, DifferenceCovered (blockCode 0 j) := by
  decide +kernel

private lemma difference_chunk_1 : ∀ j : Fin 16, DifferenceCovered (blockCode 1 j) := by
  decide +kernel

private lemma difference_chunk_2 : ∀ j : Fin 16, DifferenceCovered (blockCode 2 j) := by
  decide +kernel

private lemma difference_chunk_3 : ∀ j : Fin 16, DifferenceCovered (blockCode 3 j) := by
  decide +kernel

private lemma difference_chunk_4 : ∀ j : Fin 16, DifferenceCovered (blockCode 4 j) := by
  decide +kernel

private lemma difference_chunk_5 : ∀ j : Fin 16, DifferenceCovered (blockCode 5 j) := by
  decide +kernel

private lemma difference_chunk_6 : ∀ j : Fin 16, DifferenceCovered (blockCode 6 j) := by
  decide +kernel

private lemma difference_chunk_7 : ∀ j : Fin 16, DifferenceCovered (blockCode 7 j) := by
  decide +kernel

private lemma difference_chunk_8 : ∀ j : Fin 16, DifferenceCovered (blockCode 8 j) := by
  decide +kernel

private lemma difference_chunk_9 : ∀ j : Fin 16, DifferenceCovered (blockCode 9 j) := by
  decide +kernel

private lemma difference_chunk_10 : ∀ j : Fin 16, DifferenceCovered (blockCode 10 j) := by
  decide +kernel

private lemma difference_chunk_11 : ∀ j : Fin 16, DifferenceCovered (blockCode 11 j) := by
  decide +kernel

private lemma difference_chunk_12 : ∀ j : Fin 16, DifferenceCovered (blockCode 12 j) := by
  decide +kernel

private lemma difference_chunk_13 : ∀ j : Fin 16, DifferenceCovered (blockCode 13 j) := by
  decide +kernel

private lemma difference_chunk_14 : ∀ j : Fin 16, DifferenceCovered (blockCode 14 j) := by
  decide +kernel

private lemma difference_chunk_15 : ∀ j : Fin 16, DifferenceCovered (blockCode 15 j) := by
  decide +kernel

private lemma difference_chunk_16 : ∀ j : Fin 16, DifferenceCovered (blockCode 16 j) := by
  decide +kernel

private lemma difference_chunk_17 : ∀ j : Fin 16, DifferenceCovered (blockCode 17 j) := by
  decide +kernel

private lemma difference_chunk_18 : ∀ j : Fin 16, DifferenceCovered (blockCode 18 j) := by
  decide +kernel

private lemma difference_chunk_19 : ∀ j : Fin 16, DifferenceCovered (blockCode 19 j) := by
  decide +kernel

private lemma difference_chunk_20 : ∀ j : Fin 16, DifferenceCovered (blockCode 20 j) := by
  decide +kernel

private lemma difference_chunk_21 : ∀ j : Fin 16, DifferenceCovered (blockCode 21 j) := by
  decide +kernel

private lemma difference_chunk_22 : ∀ j : Fin 16, DifferenceCovered (blockCode 22 j) := by
  decide +kernel

private lemma difference_chunk_23 : ∀ j : Fin 16, DifferenceCovered (blockCode 23 j) := by
  decide +kernel

private lemma difference_chunk_24 : ∀ j : Fin 16, DifferenceCovered (blockCode 24 j) := by
  decide +kernel

private lemma difference_chunk_25 : ∀ j : Fin 16, DifferenceCovered (blockCode 25 j) := by
  decide +kernel

private lemma difference_chunk_26 : ∀ j : Fin 16, DifferenceCovered (blockCode 26 j) := by
  decide +kernel

private lemma difference_chunk_27 : ∀ j : Fin 16, DifferenceCovered (blockCode 27 j) := by
  decide +kernel

private lemma difference_chunk_28 : ∀ j : Fin 16, DifferenceCovered (blockCode 28 j) := by
  decide +kernel

private lemma difference_chunk_29 : ∀ j : Fin 16, DifferenceCovered (blockCode 29 j) := by
  decide +kernel

private lemma difference_chunk_30 : ∀ j : Fin 16, DifferenceCovered (blockCode 30 j) := by
  decide +kernel

private lemma difference_chunk_31 : ∀ j : Fin 16, DifferenceCovered (blockCode 31 j) := by
  decide +kernel

lemma code_difference_cover (n : Fin 512) : DifferenceCovered n := by
  let k : Fin 32 := ⟨n.val / 16, by omega⟩
  let j : Fin 16 := ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩
  have hn : blockCode k j = n := by
    apply Fin.ext
    simp only [blockCode, k, j]
    omega
  rw [← hn]
  generalize k = k'
  fin_cases k'
  · exact difference_chunk_0 j
  · exact difference_chunk_1 j
  · exact difference_chunk_2 j
  · exact difference_chunk_3 j
  · exact difference_chunk_4 j
  · exact difference_chunk_5 j
  · exact difference_chunk_6 j
  · exact difference_chunk_7 j
  · exact difference_chunk_8 j
  · exact difference_chunk_9 j
  · exact difference_chunk_10 j
  · exact difference_chunk_11 j
  · exact difference_chunk_12 j
  · exact difference_chunk_13 j
  · exact difference_chunk_14 j
  · exact difference_chunk_15 j
  · exact difference_chunk_16 j
  · exact difference_chunk_17 j
  · exact difference_chunk_18 j
  · exact difference_chunk_19 j
  · exact difference_chunk_20 j
  · exact difference_chunk_21 j
  · exact difference_chunk_22 j
  · exact difference_chunk_23 j
  · exact difference_chunk_24 j
  · exact difference_chunk_25 j
  · exact difference_chunk_26 j
  · exact difference_chunk_27 j
  · exact difference_chunk_28 j
  · exact difference_chunk_29 j
  · exact difference_chunk_30 j
  · exact difference_chunk_31 j

def CubeAllowed (a b c : Fin 28) : Prop :=
    permittedCode (xorFin (allowedCode a) (allowedCode b)) = true ∧
    permittedCode (xorFin (allowedCode a) (allowedCode c)) = true ∧
    permittedCode (xorFin (allowedCode b) (allowedCode c)) = true ∧
    permittedCode (xorFin (xorFin (allowedCode a) (allowedCode b)) (allowedCode c)) = true

instance instDecidableCubeAllowed (a b c : Fin 28) : Decidable (CubeAllowed a b c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

private lemma cube_chunk_0 : ∀ b c : Fin 28, ¬ CubeAllowed 0 b c := by
  decide +kernel

private lemma cube_chunk_1 : ∀ b c : Fin 28, ¬ CubeAllowed 1 b c := by
  decide +kernel

private lemma cube_chunk_2 : ∀ b c : Fin 28, ¬ CubeAllowed 2 b c := by
  decide +kernel

private lemma cube_chunk_3 : ∀ b c : Fin 28, ¬ CubeAllowed 3 b c := by
  decide +kernel

private lemma cube_chunk_4 : ∀ b c : Fin 28, ¬ CubeAllowed 4 b c := by
  decide +kernel

private lemma cube_chunk_5 : ∀ b c : Fin 28, ¬ CubeAllowed 5 b c := by
  decide +kernel

private lemma cube_chunk_6 : ∀ b c : Fin 28, ¬ CubeAllowed 6 b c := by
  decide +kernel

private lemma cube_chunk_7 : ∀ b c : Fin 28, ¬ CubeAllowed 7 b c := by
  decide +kernel

private lemma cube_chunk_8 : ∀ b c : Fin 28, ¬ CubeAllowed 8 b c := by
  decide +kernel

private lemma cube_chunk_9 : ∀ b c : Fin 28, ¬ CubeAllowed 9 b c := by
  decide +kernel

private lemma cube_chunk_10 : ∀ b c : Fin 28, ¬ CubeAllowed 10 b c := by
  decide +kernel

private lemma cube_chunk_11 : ∀ b c : Fin 28, ¬ CubeAllowed 11 b c := by
  decide +kernel

private lemma cube_chunk_12 : ∀ b c : Fin 28, ¬ CubeAllowed 12 b c := by
  decide +kernel

private lemma cube_chunk_13 : ∀ b c : Fin 28, ¬ CubeAllowed 13 b c := by
  decide +kernel

private lemma cube_chunk_14 : ∀ b c : Fin 28, ¬ CubeAllowed 14 b c := by
  decide +kernel

private lemma cube_chunk_15 : ∀ b c : Fin 28, ¬ CubeAllowed 15 b c := by
  decide +kernel

private lemma cube_chunk_16 : ∀ b c : Fin 28, ¬ CubeAllowed 16 b c := by
  decide +kernel

private lemma cube_chunk_17 : ∀ b c : Fin 28, ¬ CubeAllowed 17 b c := by
  decide +kernel

private lemma cube_chunk_18 : ∀ b c : Fin 28, ¬ CubeAllowed 18 b c := by
  decide +kernel

private lemma cube_chunk_19 : ∀ b c : Fin 28, ¬ CubeAllowed 19 b c := by
  decide +kernel

private lemma cube_chunk_20 : ∀ b c : Fin 28, ¬ CubeAllowed 20 b c := by
  decide +kernel

private lemma cube_chunk_21 : ∀ b c : Fin 28, ¬ CubeAllowed 21 b c := by
  decide +kernel

private lemma cube_chunk_22 : ∀ b c : Fin 28, ¬ CubeAllowed 22 b c := by
  decide +kernel

private lemma cube_chunk_23 : ∀ b c : Fin 28, ¬ CubeAllowed 23 b c := by
  decide +kernel

private lemma cube_chunk_24 : ∀ b c : Fin 28, ¬ CubeAllowed 24 b c := by
  decide +kernel

private lemma cube_chunk_25 : ∀ b c : Fin 28, ¬ CubeAllowed 25 b c := by
  decide +kernel

private lemma cube_chunk_26 : ∀ b c : Fin 28, ¬ CubeAllowed 26 b c := by
  decide +kernel

private lemma cube_chunk_27 : ∀ b c : Fin 28, ¬ CubeAllowed 27 b c := by
  decide +kernel

lemma no_allowed_cube_codes (a b c : Fin 28) : ¬ CubeAllowed a b c := by
  fin_cases a
  · exact cube_chunk_0 b c
  · exact cube_chunk_1 b c
  · exact cube_chunk_2 b c
  · exact cube_chunk_3 b c
  · exact cube_chunk_4 b c
  · exact cube_chunk_5 b c
  · exact cube_chunk_6 b c
  · exact cube_chunk_7 b c
  · exact cube_chunk_8 b c
  · exact cube_chunk_9 b c
  · exact cube_chunk_10 b c
  · exact cube_chunk_11 b c
  · exact cube_chunk_12 b c
  · exact cube_chunk_13 b c
  · exact cube_chunk_14 b c
  · exact cube_chunk_15 b c
  · exact cube_chunk_16 b c
  · exact cube_chunk_17 b c
  · exact cube_chunk_18 b c
  · exact cube_chunk_19 b c
  · exact cube_chunk_20 b c
  · exact cube_chunk_21 b c
  · exact cube_chunk_22 b c
  · exact cube_chunk_23 b c
  · exact cube_chunk_24 b c
  · exact cube_chunk_25 b c
  · exact cube_chunk_26 b c
  · exact cube_chunk_27 b c

end BinaryFuglede
