import BinaryData
import BinaryTilingDefs

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BinaryFuglede

lemma point_zero : point 0 = 0 := by
  change decode 0 = 0
  exact decode_zero

private theorem nonperiod_code_1 : ∀ k : Fin 64, xorFin (pointCode 8) (pointCode 1) ≠ pointCode k := by decide
private theorem nonperiod_code_2 : ∀ k : Fin 64, xorFin (pointCode 8) (pointCode 2) ≠ pointCode k := by decide
private theorem nonperiod_code_3 : ∀ k : Fin 64, xorFin (pointCode 16) (pointCode 3) ≠ pointCode k := by decide
private theorem nonperiod_code_4 : ∀ k : Fin 64, xorFin (pointCode 8) (pointCode 4) ≠ pointCode k := by decide
private theorem nonperiod_code_5 : ∀ k : Fin 64, xorFin (pointCode 8) (pointCode 5) ≠ pointCode k := by decide
private theorem nonperiod_code_6 : ∀ k : Fin 64, xorFin (pointCode 8) (pointCode 6) ≠ pointCode k := by decide
private theorem nonperiod_code_7 : ∀ k : Fin 64, xorFin (pointCode 8) (pointCode 7) ≠ pointCode k := by decide
private theorem nonperiod_code_8 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 8) ≠ pointCode k := by decide
private theorem nonperiod_code_9 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 9) ≠ pointCode k := by decide
private theorem nonperiod_code_10 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 10) ≠ pointCode k := by decide
private theorem nonperiod_code_11 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 11) ≠ pointCode k := by decide
private theorem nonperiod_code_12 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 12) ≠ pointCode k := by decide
private theorem nonperiod_code_13 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 13) ≠ pointCode k := by decide
private theorem nonperiod_code_14 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 14) ≠ pointCode k := by decide
private theorem nonperiod_code_15 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 15) ≠ pointCode k := by decide
private theorem nonperiod_code_16 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 16) ≠ pointCode k := by decide
private theorem nonperiod_code_17 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 17) ≠ pointCode k := by decide
private theorem nonperiod_code_18 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 18) ≠ pointCode k := by decide
private theorem nonperiod_code_19 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 19) ≠ pointCode k := by decide
private theorem nonperiod_code_20 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 20) ≠ pointCode k := by decide
private theorem nonperiod_code_21 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 21) ≠ pointCode k := by decide
private theorem nonperiod_code_22 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 22) ≠ pointCode k := by decide
private theorem nonperiod_code_23 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 23) ≠ pointCode k := by decide
private theorem nonperiod_code_24 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 24) ≠ pointCode k := by decide
private theorem nonperiod_code_25 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 25) ≠ pointCode k := by decide
private theorem nonperiod_code_26 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 26) ≠ pointCode k := by decide
private theorem nonperiod_code_27 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 27) ≠ pointCode k := by decide
private theorem nonperiod_code_28 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 28) ≠ pointCode k := by decide
private theorem nonperiod_code_29 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 29) ≠ pointCode k := by decide
private theorem nonperiod_code_30 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 30) ≠ pointCode k := by decide
private theorem nonperiod_code_31 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 31) ≠ pointCode k := by decide
private theorem nonperiod_code_32 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 32) ≠ pointCode k := by decide
private theorem nonperiod_code_33 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 33) ≠ pointCode k := by decide
private theorem nonperiod_code_34 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 34) ≠ pointCode k := by decide
private theorem nonperiod_code_35 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 35) ≠ pointCode k := by decide
private theorem nonperiod_code_36 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 36) ≠ pointCode k := by decide
private theorem nonperiod_code_37 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 37) ≠ pointCode k := by decide
private theorem nonperiod_code_38 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 38) ≠ pointCode k := by decide
private theorem nonperiod_code_39 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 39) ≠ pointCode k := by decide
private theorem nonperiod_code_40 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 40) ≠ pointCode k := by decide
private theorem nonperiod_code_41 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 41) ≠ pointCode k := by decide
private theorem nonperiod_code_42 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 42) ≠ pointCode k := by decide
private theorem nonperiod_code_43 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 43) ≠ pointCode k := by decide
private theorem nonperiod_code_44 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 44) ≠ pointCode k := by decide
private theorem nonperiod_code_45 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 45) ≠ pointCode k := by decide
private theorem nonperiod_code_46 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 46) ≠ pointCode k := by decide
private theorem nonperiod_code_47 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 47) ≠ pointCode k := by decide
private theorem nonperiod_code_48 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 48) ≠ pointCode k := by decide
private theorem nonperiod_code_49 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 49) ≠ pointCode k := by decide
private theorem nonperiod_code_50 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 50) ≠ pointCode k := by decide
private theorem nonperiod_code_51 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 51) ≠ pointCode k := by decide
private theorem nonperiod_code_52 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 52) ≠ pointCode k := by decide
private theorem nonperiod_code_53 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 53) ≠ pointCode k := by decide
private theorem nonperiod_code_54 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 54) ≠ pointCode k := by decide
private theorem nonperiod_code_55 : ∀ k : Fin 64, xorFin (pointCode 1) (pointCode 55) ≠ pointCode k := by decide
private theorem nonperiod_code_56 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 56) ≠ pointCode k := by decide
private theorem nonperiod_code_57 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 57) ≠ pointCode k := by decide
private theorem nonperiod_code_58 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 58) ≠ pointCode k := by decide
private theorem nonperiod_code_59 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 59) ≠ pointCode k := by decide
private theorem nonperiod_code_60 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 60) ≠ pointCode k := by decide
private theorem nonperiod_code_61 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 61) ≠ pointCode k := by decide
private theorem nonperiod_code_62 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 62) ≠ pointCode k := by decide
private theorem nonperiod_code_63 : ∀ k : Fin 64, xorFin (pointCode 2) (pointCode 63) ≠ pointCode k := by decide

lemma code_nonperiodic (i : Fin 64) (hi : i ≠ 0) :
    ∃ j : Fin 64, ∀ k : Fin 64, xorFin (pointCode j) (pointCode i) ≠ pointCode k := by
  fin_cases i
  · exact (hi rfl).elim
  · exact ⟨8, nonperiod_code_1⟩
  · exact ⟨8, nonperiod_code_2⟩
  · exact ⟨16, nonperiod_code_3⟩
  · exact ⟨8, nonperiod_code_4⟩
  · exact ⟨8, nonperiod_code_5⟩
  · exact ⟨8, nonperiod_code_6⟩
  · exact ⟨8, nonperiod_code_7⟩
  · exact ⟨1, nonperiod_code_8⟩
  · exact ⟨1, nonperiod_code_9⟩
  · exact ⟨1, nonperiod_code_10⟩
  · exact ⟨1, nonperiod_code_11⟩
  · exact ⟨1, nonperiod_code_12⟩
  · exact ⟨1, nonperiod_code_13⟩
  · exact ⟨1, nonperiod_code_14⟩
  · exact ⟨1, nonperiod_code_15⟩
  · exact ⟨1, nonperiod_code_16⟩
  · exact ⟨1, nonperiod_code_17⟩
  · exact ⟨1, nonperiod_code_18⟩
  · exact ⟨1, nonperiod_code_19⟩
  · exact ⟨1, nonperiod_code_20⟩
  · exact ⟨1, nonperiod_code_21⟩
  · exact ⟨1, nonperiod_code_22⟩
  · exact ⟨1, nonperiod_code_23⟩
  · exact ⟨1, nonperiod_code_24⟩
  · exact ⟨1, nonperiod_code_25⟩
  · exact ⟨1, nonperiod_code_26⟩
  · exact ⟨1, nonperiod_code_27⟩
  · exact ⟨1, nonperiod_code_28⟩
  · exact ⟨1, nonperiod_code_29⟩
  · exact ⟨1, nonperiod_code_30⟩
  · exact ⟨1, nonperiod_code_31⟩
  · exact ⟨1, nonperiod_code_32⟩
  · exact ⟨1, nonperiod_code_33⟩
  · exact ⟨1, nonperiod_code_34⟩
  · exact ⟨1, nonperiod_code_35⟩
  · exact ⟨1, nonperiod_code_36⟩
  · exact ⟨1, nonperiod_code_37⟩
  · exact ⟨1, nonperiod_code_38⟩
  · exact ⟨1, nonperiod_code_39⟩
  · exact ⟨2, nonperiod_code_40⟩
  · exact ⟨2, nonperiod_code_41⟩
  · exact ⟨2, nonperiod_code_42⟩
  · exact ⟨2, nonperiod_code_43⟩
  · exact ⟨2, nonperiod_code_44⟩
  · exact ⟨2, nonperiod_code_45⟩
  · exact ⟨2, nonperiod_code_46⟩
  · exact ⟨2, nonperiod_code_47⟩
  · exact ⟨1, nonperiod_code_48⟩
  · exact ⟨1, nonperiod_code_49⟩
  · exact ⟨1, nonperiod_code_50⟩
  · exact ⟨1, nonperiod_code_51⟩
  · exact ⟨1, nonperiod_code_52⟩
  · exact ⟨1, nonperiod_code_53⟩
  · exact ⟨1, nonperiod_code_54⟩
  · exact ⟨1, nonperiod_code_55⟩
  · exact ⟨2, nonperiod_code_56⟩
  · exact ⟨2, nonperiod_code_57⟩
  · exact ⟨2, nonperiod_code_58⟩
  · exact ⟨2, nonperiod_code_59⟩
  · exact ⟨2, nonperiod_code_60⟩
  · exact ⟨2, nonperiod_code_61⟩
  · exact ⟨2, nonperiod_code_62⟩
  · exact ⟨2, nonperiod_code_63⟩

lemma Eset_not_periodic : ¬ Periodic Eset := by
  rintro ⟨p,hp,hperiod⟩
  have h0 : (0 : V) ∈ Eset := ⟨0,point_zero⟩
  have hpin : p ∈ Eset := by simpa using (hperiod 0).mp h0
  obtain ⟨i,hi⟩ := hpin
  have hi0 : i ≠ 0 := by
    intro h
    apply hp
    rw [← hi,h,point_zero]
  obtain ⟨j,hj⟩ := code_nonperiodic i hi0
  have hplus : point j + p ∈ Eset := (hperiod (point j)).mp ⟨j,rfl⟩
  obtain ⟨k,hk⟩ := hplus
  apply hj k
  apply decodeFin_injective
  rw [decodeFin_xor]
  change point j + point i = point k
  rw [hi,← hk]

end BinaryFuglede
