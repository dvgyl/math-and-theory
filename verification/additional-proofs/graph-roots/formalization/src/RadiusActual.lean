import RadiusLog

noncomputable section
namespace SquareFlowerCompletion.Radius

theorem bracket_root_radius_bound (n : ℕ) (z : ℂ) (hn : 0 < n)
    (hroot : bracket n z = 0) (hr : 4 ≤ ‖z‖) (hL : 1 ≤ Real.log (4*(n : ℝ))) :
    Real.log (4*(n : ℝ))-Real.log (Real.log (4*(n : ℝ))) ≤
      4*(n : ℝ)/(‖z‖-3)^2 :=
  lower_of_power n hn ‖z‖ hr (bracket_root_norm_bound n z hroot hr) hL

theorem actual_graph_root_radius_bound (n : ℕ) (z : ℂ) (hn : 0 < n)
    (hroot : (Counting.complexDominationPolynomial n).eval z = 0)
    (hr : 4 ≤ ‖z‖) (hL : 1 ≤ Real.log (4*(n : ℝ))) :
    Real.log (4*(n : ℝ))-Real.log (Real.log (4*(n : ℝ))) ≤
      4*(n : ℝ)/(‖z‖-3)^2 := by
  have hz : z ≠ 0 := by
    intro hz
    norm_num [hz] at hr
  have hb : bracket n z = 0 := by
    have h := (Counting.eval_eq_zero_iff_bracket hz).mp hroot
    simpa [bracket,A,B] using h
  exact bracket_root_radius_bound n z hn hb hr hL

#print axioms bracket_root_radius_bound
#print axioms actual_graph_root_radius_bound
end SquareFlowerCompletion.Radius
