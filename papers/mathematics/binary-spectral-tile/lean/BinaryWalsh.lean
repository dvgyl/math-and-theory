import BinaryCharacters

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open scoped BigOperators
namespace BinaryFuglede

def SpectralDifference (k : Fin 512) : Prop :=
  k ≠ 0 ∧ ([0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 31,
    32, 33, 34, 36, 40, 47, 48, 55, 59, 61, 62, 63] : List ℕ).contains (k.val % 64) = true

instance instDecidableSpectralDifference (k : Fin 512) : Decidable (SpectralDifference k) :=
  inferInstanceAs (Decidable (_ ∧ _))

def walshInt (k : Fin 512) : ℤ := ∑ j : Fin 64, intCharacter (decodeFin k) (point j)

def walshBlockCode (k : Fin 32) (j : Fin 16) : Fin 512 := ⟨16*k.val + j.val, by omega⟩

private lemma walsh_chunk_0 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 0 j) → walshInt (walshBlockCode 0 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_1 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 1 j) → walshInt (walshBlockCode 1 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_2 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 2 j) → walshInt (walshBlockCode 2 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_3 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 3 j) → walshInt (walshBlockCode 3 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_4 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 4 j) → walshInt (walshBlockCode 4 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_5 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 5 j) → walshInt (walshBlockCode 5 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_6 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 6 j) → walshInt (walshBlockCode 6 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_7 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 7 j) → walshInt (walshBlockCode 7 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_8 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 8 j) → walshInt (walshBlockCode 8 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_9 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 9 j) → walshInt (walshBlockCode 9 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_10 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 10 j) → walshInt (walshBlockCode 10 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_11 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 11 j) → walshInt (walshBlockCode 11 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_12 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 12 j) → walshInt (walshBlockCode 12 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_13 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 13 j) → walshInt (walshBlockCode 13 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_14 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 14 j) → walshInt (walshBlockCode 14 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_15 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 15 j) → walshInt (walshBlockCode 15 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_16 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 16 j) → walshInt (walshBlockCode 16 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_17 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 17 j) → walshInt (walshBlockCode 17 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_18 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 18 j) → walshInt (walshBlockCode 18 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_19 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 19 j) → walshInt (walshBlockCode 19 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_20 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 20 j) → walshInt (walshBlockCode 20 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_21 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 21 j) → walshInt (walshBlockCode 21 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_22 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 22 j) → walshInt (walshBlockCode 22 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_23 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 23 j) → walshInt (walshBlockCode 23 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_24 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 24 j) → walshInt (walshBlockCode 24 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_25 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 25 j) → walshInt (walshBlockCode 25 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_26 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 26 j) → walshInt (walshBlockCode 26 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_27 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 27 j) → walshInt (walshBlockCode 27 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_28 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 28 j) → walshInt (walshBlockCode 28 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_29 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 29 j) → walshInt (walshBlockCode 29 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_30 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 30 j) → walshInt (walshBlockCode 30 j) = 0 := by
  decide +kernel

private lemma walsh_chunk_31 : ∀ j : Fin 16, SpectralDifference (walshBlockCode 31 j) → walshInt (walshBlockCode 31 j) = 0 := by
  decide +kernel

lemma walshInt_zero (k : Fin 512) (hk : SpectralDifference k) : walshInt k = 0 := by
  have hall (a : Fin 32) (b : Fin 16) : SpectralDifference (walshBlockCode a b) → walshInt (walshBlockCode a b) = 0 := by
    fin_cases a
    · exact walsh_chunk_0 b
    · exact walsh_chunk_1 b
    · exact walsh_chunk_2 b
    · exact walsh_chunk_3 b
    · exact walsh_chunk_4 b
    · exact walsh_chunk_5 b
    · exact walsh_chunk_6 b
    · exact walsh_chunk_7 b
    · exact walsh_chunk_8 b
    · exact walsh_chunk_9 b
    · exact walsh_chunk_10 b
    · exact walsh_chunk_11 b
    · exact walsh_chunk_12 b
    · exact walsh_chunk_13 b
    · exact walsh_chunk_14 b
    · exact walsh_chunk_15 b
    · exact walsh_chunk_16 b
    · exact walsh_chunk_17 b
    · exact walsh_chunk_18 b
    · exact walsh_chunk_19 b
    · exact walsh_chunk_20 b
    · exact walsh_chunk_21 b
    · exact walsh_chunk_22 b
    · exact walsh_chunk_23 b
    · exact walsh_chunk_24 b
    · exact walsh_chunk_25 b
    · exact walsh_chunk_26 b
    · exact walsh_chunk_27 b
    · exact walsh_chunk_28 b
    · exact walsh_chunk_29 b
    · exact walsh_chunk_30 b
    · exact walsh_chunk_31 b
  let a : Fin 32 := ⟨k.val / 16, by omega⟩
  let b : Fin 16 := ⟨k.val % 16, Nat.mod_lt _ (by decide)⟩
  have he : walshBlockCode a b = k := by
    apply Fin.ext
    dsimp [walshBlockCode,a,b]
    omega
  simpa only [he] using hall a b (he.symm ▸ hk)

private lemma frequency_row_0 : ∀ j : Fin 64, (0 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 0) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_1 : ∀ j : Fin 64, (1 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 1) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_2 : ∀ j : Fin 64, (2 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 2) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_3 : ∀ j : Fin 64, (3 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 3) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_4 : ∀ j : Fin 64, (4 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 4) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_5 : ∀ j : Fin 64, (5 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 5) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_6 : ∀ j : Fin 64, (6 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 6) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_7 : ∀ j : Fin 64, (7 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 7) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_8 : ∀ j : Fin 64, (8 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 8) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_9 : ∀ j : Fin 64, (9 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 9) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_10 : ∀ j : Fin 64, (10 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 10) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_11 : ∀ j : Fin 64, (11 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 11) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_12 : ∀ j : Fin 64, (12 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 12) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_13 : ∀ j : Fin 64, (13 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 13) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_14 : ∀ j : Fin 64, (14 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 14) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_15 : ∀ j : Fin 64, (15 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 15) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_16 : ∀ j : Fin 64, (16 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 16) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_17 : ∀ j : Fin 64, (17 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 17) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_18 : ∀ j : Fin 64, (18 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 18) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_19 : ∀ j : Fin 64, (19 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 19) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_20 : ∀ j : Fin 64, (20 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 20) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_21 : ∀ j : Fin 64, (21 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 21) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_22 : ∀ j : Fin 64, (22 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 22) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_23 : ∀ j : Fin 64, (23 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 23) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_24 : ∀ j : Fin 64, (24 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 24) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_25 : ∀ j : Fin 64, (25 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 25) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_26 : ∀ j : Fin 64, (26 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 26) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_27 : ∀ j : Fin 64, (27 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 27) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_28 : ∀ j : Fin 64, (28 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 28) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_29 : ∀ j : Fin 64, (29 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 29) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_30 : ∀ j : Fin 64, (30 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 30) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_31 : ∀ j : Fin 64, (31 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 31) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_32 : ∀ j : Fin 64, (32 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 32) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_33 : ∀ j : Fin 64, (33 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 33) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_34 : ∀ j : Fin 64, (34 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 34) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_35 : ∀ j : Fin 64, (35 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 35) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_36 : ∀ j : Fin 64, (36 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 36) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_37 : ∀ j : Fin 64, (37 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 37) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_38 : ∀ j : Fin 64, (38 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 38) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_39 : ∀ j : Fin 64, (39 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 39) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_40 : ∀ j : Fin 64, (40 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 40) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_41 : ∀ j : Fin 64, (41 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 41) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_42 : ∀ j : Fin 64, (42 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 42) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_43 : ∀ j : Fin 64, (43 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 43) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_44 : ∀ j : Fin 64, (44 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 44) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_45 : ∀ j : Fin 64, (45 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 45) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_46 : ∀ j : Fin 64, (46 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 46) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_47 : ∀ j : Fin 64, (47 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 47) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_48 : ∀ j : Fin 64, (48 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 48) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_49 : ∀ j : Fin 64, (49 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 49) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_50 : ∀ j : Fin 64, (50 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 50) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_51 : ∀ j : Fin 64, (51 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 51) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_52 : ∀ j : Fin 64, (52 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 52) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_53 : ∀ j : Fin 64, (53 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 53) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_54 : ∀ j : Fin 64, (54 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 54) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_55 : ∀ j : Fin 64, (55 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 55) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_56 : ∀ j : Fin 64, (56 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 56) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_57 : ∀ j : Fin 64, (57 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 57) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_58 : ∀ j : Fin 64, (58 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 58) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_59 : ∀ j : Fin 64, (59 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 59) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_60 : ∀ j : Fin 64, (60 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 60) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_61 : ∀ j : Fin 64, (61 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 61) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_62 : ∀ j : Fin 64, (62 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 62) (freqCode j)) := by
  decide +kernel

private lemma frequency_row_63 : ∀ j : Fin 64, (63 : Fin 64) ≠ j → SpectralDifference (xorFin (freqCode 63) (freqCode j)) := by
  decide +kernel

lemma frequency_difference (i j : Fin 64) (hij : i ≠ j) : SpectralDifference (xorFin (freqCode i) (freqCode j)) := by
  fin_cases i
  · exact frequency_row_0 j hij
  · exact frequency_row_1 j hij
  · exact frequency_row_2 j hij
  · exact frequency_row_3 j hij
  · exact frequency_row_4 j hij
  · exact frequency_row_5 j hij
  · exact frequency_row_6 j hij
  · exact frequency_row_7 j hij
  · exact frequency_row_8 j hij
  · exact frequency_row_9 j hij
  · exact frequency_row_10 j hij
  · exact frequency_row_11 j hij
  · exact frequency_row_12 j hij
  · exact frequency_row_13 j hij
  · exact frequency_row_14 j hij
  · exact frequency_row_15 j hij
  · exact frequency_row_16 j hij
  · exact frequency_row_17 j hij
  · exact frequency_row_18 j hij
  · exact frequency_row_19 j hij
  · exact frequency_row_20 j hij
  · exact frequency_row_21 j hij
  · exact frequency_row_22 j hij
  · exact frequency_row_23 j hij
  · exact frequency_row_24 j hij
  · exact frequency_row_25 j hij
  · exact frequency_row_26 j hij
  · exact frequency_row_27 j hij
  · exact frequency_row_28 j hij
  · exact frequency_row_29 j hij
  · exact frequency_row_30 j hij
  · exact frequency_row_31 j hij
  · exact frequency_row_32 j hij
  · exact frequency_row_33 j hij
  · exact frequency_row_34 j hij
  · exact frequency_row_35 j hij
  · exact frequency_row_36 j hij
  · exact frequency_row_37 j hij
  · exact frequency_row_38 j hij
  · exact frequency_row_39 j hij
  · exact frequency_row_40 j hij
  · exact frequency_row_41 j hij
  · exact frequency_row_42 j hij
  · exact frequency_row_43 j hij
  · exact frequency_row_44 j hij
  · exact frequency_row_45 j hij
  · exact frequency_row_46 j hij
  · exact frequency_row_47 j hij
  · exact frequency_row_48 j hij
  · exact frequency_row_49 j hij
  · exact frequency_row_50 j hij
  · exact frequency_row_51 j hij
  · exact frequency_row_52 j hij
  · exact frequency_row_53 j hij
  · exact frequency_row_54 j hij
  · exact frequency_row_55 j hij
  · exact frequency_row_56 j hij
  · exact frequency_row_57 j hij
  · exact frequency_row_58 j hij
  · exact frequency_row_59 j hij
  · exact frequency_row_60 j hij
  · exact frequency_row_61 j hij
  · exact frequency_row_62 j hij
  · exact frequency_row_63 j hij

lemma int_character_orthogonality (i j : Fin 64) (hij : i ≠ j) :
    (∑ k : Fin 64, intCharacter (freq i) (point k) * intCharacter (freq j) (point k)) = 0 := by
  simp_rw [← intCharacter_add_left]
  change (∑ k : Fin 64, intCharacter (decodeFin (freqCode i) + decodeFin (freqCode j)) (point k)) = 0
  rw [← decodeFin_xor]
  exact walshInt_zero _ (frequency_difference i j hij)

end BinaryFuglede
