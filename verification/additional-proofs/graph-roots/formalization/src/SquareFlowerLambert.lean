import LambertSequence

noncomputable section
open Filter Topology
namespace SquareFlowerCompletion
namespace Lambert

def logScale (n : ℕ) : ℝ := Real.log (4 * (n : ℝ))
def initialCoordinate (lam : ℂ) : ℂ := -Complex.exp (-lam / 2)

theorem logScale_tendsto_atTop : Tendsto logScale atTop atTop := by
  apply Real.tendsto_log_atTop.comp
  exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4)

theorem exists_square_flower_lambert : ∃ lam : ℕ → ℂ,
    Tendsto (fun n => lam n - center (logScale n)) atTop (𝓝 0) ∧
    ∀ᶠ n in atTop, lam n ∈ Complex.slitPlane ∧
      lam n + Complex.log (lam n) = (logScale n : ℂ) + (Real.pi : ℂ) * Complex.I ∧
      lam n * Complex.exp (lam n) = -(4 * (n : ℂ)) := by
  obtain ⟨lam, hlim, heq⟩ := exists_lambert_sequence logScale logScale_tendsto_atTop
  refine ⟨lam, hlim, ?_⟩
  filter_upwards [heq, eventually_ge_atTop 1] with n hn hpos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hpos)
  have hexp : Complex.exp (logScale n : ℂ) = 4 * (n : ℂ) := by
    rw [logScale, ← Complex.ofReal_exp, Real.exp_log (by positivity : 0 < 4 * (n : ℝ))]
    push_cast
    rfl
  exact ⟨hn.1, hn.2.1, hexp ▸ hn.2.2⟩

theorem initialCoordinate_ne_zero (lam : ℂ) : initialCoordinate lam ≠ 0 := by
  simp [initialCoordinate, Complex.exp_ne_zero]

theorem initialCoordinate_square_exp (lam : ℂ) :
    initialCoordinate lam ^ 2 = Complex.exp (-lam) := by
  dsimp [initialCoordinate]
  rw [neg_sq, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem initialCoordinate_half_exp (lam : ℂ) :
    initialCoordinate lam * Complex.exp (lam / 2) = -1 := by
  dsimp [initialCoordinate]
  rw [neg_mul, ← Complex.exp_add]
  have h : -lam / 2 + lam / 2 = 0 := by ring
  rw [h, Complex.exp_zero]

theorem initialCoordinate_square {n : ℕ} (hn : 0 < n) {lam : ℂ}
    (he : lam * Complex.exp lam = -(4 * (n : ℂ))) :
    initialCoordinate lam ^ 2 = -lam / (4 * (n : ℂ)) := by
  have hn0 : 4 * (n : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast hn.ne')
  have he0 : Complex.exp lam ≠ 0 := Complex.exp_ne_zero lam
  rw [initialCoordinate_square_exp, Complex.exp_neg]
  apply (eq_div_iff hn0).2
  calc
    (Complex.exp lam)⁻¹ * (4 * (n : ℂ)) =
        (Complex.exp lam)⁻¹ * (-(lam * Complex.exp lam)) := by rw [he]; ring
    _ = -lam := by field_simp

theorem initialCoordinate_norm_square {n : ℕ} (hn : 0 < n) {lam : ℂ}
    (he : lam * Complex.exp lam = -(4 * (n : ℂ))) :
    ‖initialCoordinate lam‖ ^ 2 = ‖lam‖ / (4 * (n : ℝ)) := by
  have h := congrArg norm (initialCoordinate_square hn he)
  norm_num [norm_pow, norm_div, norm_mul] at h
  exact h

theorem initialCoordinate_model_zero {n : ℕ} (hn : 0 < n) {lam : ℂ}
    (he : lam * Complex.exp lam = -(4 * (n : ℂ))) :
    initialCoordinate lam * Complex.exp (-2 * (n : ℂ) * initialCoordinate lam ^ 2) = -1 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h : -2 * (n : ℂ) * initialCoordinate lam ^ 2 = lam / 2 := by
    rw [initialCoordinate_square hn he]
    field_simp
    ring
  rw [h]
  exact initialCoordinate_half_exp lam

#print axioms exists_square_flower_lambert
#print axioms initialCoordinate_square
#print axioms initialCoordinate_norm_square
#print axioms initialCoordinate_model_zero
end Lambert
end SquareFlowerCompletion
