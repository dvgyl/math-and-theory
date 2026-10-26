module
public import MathAndTheory.Mathematics.DomiRank.Logs

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

@[expose] public section

namespace MathAndTheory.DomiRank

theorem log_left_0_interval :
    ((-35645977 : ℝ) / 20000000) ≤ Real.log ((89889445253 : ℝ) / 534258269542) ∧
    Real.log ((89889445253 : ℝ) / 534258269542) ≤ ((-44557471 : ℝ) / 25000000) := by
  have h := log_interval_of_ratio (x := ((359557781012 : ℝ) / 267129134771)) (t := ((92428646241 : ℝ) / 626686915783))
    (by norm_num) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  have htwo := log_two_interval
  have heq : Real.log ((89889445253 : ℝ) / 534258269542) = Real.log ((359557781012 : ℝ) / 267129134771) - 3 * Real.log 2 := by
    rw [show ((89889445253 : ℝ) / 534258269542) = ((359557781012 : ℝ) / 267129134771) / (2 : ℝ) ^ 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith

theorem log_left_1_interval :
    ((-178436459 : ℝ) / 100000000) ≤ Real.log ((89703948253 : ℝ) / 534258269542) ∧
    Real.log ((89703948253 : ℝ) / 534258269542) ≤ ((-89218229 : ℝ) / 50000000) := by
  have h := log_interval_of_ratio (x := ((358815793012 : ℝ) / 267129134771)) (t := ((91686658241 : ℝ) / 625944927783))
    (by norm_num) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  have htwo := log_two_interval
  have heq : Real.log ((89703948253 : ℝ) / 534258269542) = Real.log ((358815793012 : ℝ) / 267129134771) - 3 * Real.log 2 := by
    rw [show ((89703948253 : ℝ) / 534258269542) = ((358815793012 : ℝ) / 267129134771) / (2 : ℝ) ^ 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith

theorem log_left_2_interval :
    ((-290218503 : ℝ) / 100000000) ≤ Real.log ((29332448253 : ℝ) / 534258269542) ∧
    Real.log ((29332448253 : ℝ) / 534258269542) ≤ ((-290218501 : ℝ) / 100000000) := by
  have h := log_interval_of_ratio (x := ((469319172048 : ℝ) / 267129134771)) (t := ((202190037277 : ℝ) / 736448306819))
    (by norm_num) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  have htwo := log_two_interval
  have heq : Real.log ((29332448253 : ℝ) / 534258269542) = Real.log ((469319172048 : ℝ) / 267129134771) - 5 * Real.log 2 := by
    rw [show ((29332448253 : ℝ) / 534258269542) = ((469319172048 : ℝ) / 267129134771) / (2 : ℝ) ^ 5 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith

theorem log_left_3_interval :
    ((-89817941 : ℝ) / 50000000) ≤ Real.log ((88634445253 : ℝ) / 534258269542) ∧
    Real.log ((88634445253 : ℝ) / 534258269542) ≤ ((-179635881 : ℝ) / 100000000) := by
  have h := log_interval_of_ratio (x := ((354537781012 : ℝ) / 267129134771)) (t := ((87408646241 : ℝ) / 621666915783))
    (by norm_num) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  have htwo := log_two_interval
  have heq : Real.log ((88634445253 : ℝ) / 534258269542) = Real.log ((354537781012 : ℝ) / 267129134771) - 3 * Real.log 2 := by
    rw [show ((88634445253 : ℝ) / 534258269542) = ((354537781012 : ℝ) / 267129134771) / (2 : ℝ) ^ 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith

theorem log_left_4_interval :
    ((-87704177 : ℝ) / 10000000) ≤ Real.log ((82948253 : ℝ) / 534258269542) ∧
    Real.log ((82948253 : ℝ) / 534258269542) ≤ ((-877041769 : ℝ) / 100000000) := by
  have h := log_interval_of_ratio (x := ((339756044288 : ℝ) / 267129134771)) (t := ((72626909517 : ℝ) / 606885179059))
    (by norm_num) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  have htwo := log_two_interval
  have heq : Real.log ((82948253 : ℝ) / 534258269542) = Real.log ((339756044288 : ℝ) / 267129134771) - 13 * Real.log 2 := by
    rw [show ((82948253 : ℝ) / 534258269542) = ((339756044288 : ℝ) / 267129134771) / (2 : ℝ) ^ 13 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith

noncomputable def leftEntropyNats : ℝ :=
  -(1 * ((89889445253 : ℝ) / 534258269542) * Real.log ((89889445253 : ℝ) / 534258269542) +
      2 * ((89703948253 : ℝ) / 534258269542) * Real.log ((89703948253 : ℝ) / 534258269542) +
      6 * ((29332448253 : ℝ) / 534258269542) * Real.log ((29332448253 : ℝ) / 534258269542) +
      1 * ((88634445253 : ℝ) / 534258269542) * Real.log ((88634445253 : ℝ) / 534258269542) +
      4 * ((82948253 : ℝ) / 534258269542) * Real.log ((82948253 : ℝ) / 534258269542))

theorem log_right_0_interval :
    ((-88603529 : ℝ) / 50000000) ≤ Real.log ((168020629 : ℝ) / 988469056) ∧
    Real.log ((168020629 : ℝ) / 988469056) ≤ ((-177207057 : ℝ) / 100000000) := by
  have h := log_interval_of_ratio (x := ((168020629 : ℝ) / 123558632)) (t := ((44461997 : ℝ) / 291579261))
    (by norm_num) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  have htwo := log_two_interval
  have heq : Real.log ((168020629 : ℝ) / 988469056) = Real.log ((168020629 : ℝ) / 123558632) - 3 * Real.log 2 := by
    rw [show ((168020629 : ℝ) / 988469056) = ((168020629 : ℝ) / 123558632) / (2 : ℝ) ^ 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith

theorem log_right_1_interval :
    ((-35526911 : ℝ) / 20000000) ≤ Real.log ((167303879 : ℝ) / 988469056) ∧
    Real.log ((167303879 : ℝ) / 988469056) ≤ ((-88817277 : ℝ) / 50000000) := by
  have h := log_interval_of_ratio (x := ((167303879 : ℝ) / 123558632)) (t := ((43745247 : ℝ) / 290862511))
    (by norm_num) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  have htwo := log_two_interval
  have heq : Real.log ((167303879 : ℝ) / 988469056) = Real.log ((167303879 : ℝ) / 123558632) - 3 * Real.log 2 := by
    rw [show ((167303879 : ℝ) / 988469056) = ((167303879 : ℝ) / 123558632) / (2 : ℝ) ^ 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith

theorem log_right_2_interval :
    ((-72883081 : ℝ) / 25000000) ≤ Real.log ((107123383 : ℝ) / 1976938112) ∧
    Real.log ((107123383 : ℝ) / 1976938112) ≤ ((-291532323 : ℝ) / 100000000) := by
  have h := log_interval_of_ratio (x := ((107123383 : ℝ) / 61779316)) (t := ((45344067 : ℝ) / 168902699))
    (by norm_num) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  have htwo := log_two_interval
  have heq : Real.log ((107123383 : ℝ) / 1976938112) = Real.log ((107123383 : ℝ) / 61779316) - 5 * Real.log 2 := by
    rw [show ((107123383 : ℝ) / 1976938112) = ((107123383 : ℝ) / 61779316) / (2 : ℝ) ^ 5 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith

theorem log_right_3_interval :
    ((-180180147 : ℝ) / 100000000) ≤ Real.log ((81549377 : ℝ) / 494234528) ∧
    Real.log ((81549377 : ℝ) / 494234528) ≤ ((-90090073 : ℝ) / 50000000) := by
  have h := log_interval_of_ratio (x := ((81549377 : ℝ) / 61779316)) (t := ((19770061 : ℝ) / 143328693))
    (by norm_num) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  have htwo := log_two_interval
  have heq : Real.log ((81549377 : ℝ) / 494234528) = Real.log ((81549377 : ℝ) / 61779316) - 3 * Real.log 2 := by
    rw [show ((81549377 : ℝ) / 494234528) = ((81549377 : ℝ) / 61779316) / (2 : ℝ) ^ 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith

theorem log_right_4_interval :
    ((-398317637 : ℝ) / 50000000) ≤ Real.log ((685883 : ℝ) / 1976938112) ∧
    Real.log ((685883 : ℝ) / 1976938112) ≤ ((-796635273 : ℝ) / 100000000) := by
  have h := log_interval_of_ratio (x := ((21948256 : ℝ) / 15444829)) (t := ((6503427 : ℝ) / 37393085))
    (by norm_num) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  have htwo := log_two_interval
  have heq : Real.log ((685883 : ℝ) / 1976938112) = Real.log ((21948256 : ℝ) / 15444829) - 12 * Real.log 2 := by
    rw [show ((685883 : ℝ) / 1976938112) = ((21948256 : ℝ) / 15444829) / (2 : ℝ) ^ 12 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith

noncomputable def rightEntropyNats : ℝ :=
  -(1 * ((168020629 : ℝ) / 988469056) * Real.log ((168020629 : ℝ) / 988469056) +
      2 * ((167303879 : ℝ) / 988469056) * Real.log ((167303879 : ℝ) / 988469056) +
      6 * ((107123383 : ℝ) / 1976938112) * Real.log ((107123383 : ℝ) / 1976938112) +
      1 * ((81549377 : ℝ) / 494234528) * Real.log ((81549377 : ℝ) / 494234528) +
      4 * ((685883 : ℝ) / 1976938112) * Real.log ((685883 : ℝ) / 1976938112))

theorem leftEntropyNats_upper : leftEntropyNats < (2158577 : ℝ) / 1000000 := by
  have h0 := log_left_0_interval.1
  have h1 := log_left_1_interval.1
  have h2 := log_left_2_interval.1
  have h3 := log_left_3_interval.1
  have h4 := log_left_4_interval.1
  unfold leftEntropyNats
  linarith

theorem rightEntropyNats_lower : (2158712 : ℝ) / 1000000 < rightEntropyNats := by
  have h0 := log_right_0_interval.2
  have h1 := log_right_1_interval.2
  have h2 := log_right_2_interval.2
  have h3 := log_right_3_interval.2
  have h4 := log_right_4_interval.2
  unfold rightEntropyNats
  linarith

theorem entropyNats_certificate : leftEntropyNats + (1 : ℝ) / 10000 < rightEntropyNats := by
  have hl := leftEntropyNats_upper
  have hr := rightEntropyNats_lower
  linarith

end MathAndTheory.DomiRank
