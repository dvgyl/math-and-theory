import PowerFamily
import Normalization

open scoped BigOperators Matrix ComplexOrder

namespace PPTCone

/-- The normalized density operator for n+1 actual qutrit Tiles copies. -/
noncomputable def tilesDensity (n : ℕ) :
    Matrix (PowerIndex n × PowerIndex n) (PowerIndex n × PowerIndex n) ℂ :=
  ((4 : ℂ)^(n+1))⁻¹ • tilesPower n

theorem tilesDensity_zero : tilesDensity 0 = (4 : ℂ)⁻¹ • tilesProjector := by
  simp only [tilesDensity, tilesPower, Nat.zero_add, pow_one]

/-- The normalization agrees exactly with taking tensor products of the
single-copy density state, with the specified local-system regrouping. -/
theorem tilesDensity_succ (n : ℕ) :
    tilesDensity (n+1) = tensorProduct (tilesDensity 0) (tilesDensity n) := by
  ext p q
  simp only [tilesDensity, tilesPower, tensorProduct, Matrix.smul_apply,
    smul_eq_mul, Nat.zero_add, pow_one, pow_succ, mul_inv_rev]
  ring

/-- The scalar acting on each pure vector in the normalization. -/
noncomputable def tilesAmplitude (n : ℕ) : ℂ := ((2 : ℂ)^(n+1))⁻¹

theorem tilesAmplitude_nonzero (n : ℕ) : tilesAmplitude n ≠ 0 := by
  exact inv_ne_zero (pow_ne_zero _ (by norm_num))

theorem tilesAmplitude_normsq (n : ℕ) :
    tilesAmplitude n * star (tilesAmplitude n) = ((4 : ℂ)^(n+1))⁻¹ := by
  simp only [tilesAmplitude, star_inv₀, star_pow, star_ofNat]
  rw [← mul_inv_rev, ← mul_pow]
  norm_num

theorem tilesPower_trace (n : ℕ) : Matrix.trace (tilesPower n) = (4 : ℂ)^(n+1) := by
  induction n with
  | zero => simpa only [Nat.zero_add, pow_one] using tilesProjector_trace
  | succ n ih =>
    change Matrix.trace (tensorProduct tilesProjector (tilesPower n)) = _
    rw [tensorProduct_trace, tilesProjector_trace, ih, pow_succ]
    exact mul_comm _ _

theorem tilesDensity_trace (n : ℕ) : Matrix.trace (tilesDensity n) = 1 := by
  simp only [tilesDensity, Matrix.trace_smul, smul_eq_mul, tilesPower_trace]
  exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))

theorem tilesDensity_posSemidef (n : ℕ) : (tilesDensity n).PosSemidef := by
  rw [tilesDensity, ← tilesAmplitude_normsq]
  exact projector_smul_normsq_posSemidef (tilesPower n)
    (tilesPower_hermitian n) (tilesPower_idempotent n) (tilesAmplitude n)

theorem tilesDensity_partialTranspose (n : ℕ) :
    partialTranspose (tilesDensity n) = tilesDensity n := by
  simp only [tilesDensity, partialTranspose_smul, tilesPower_partialTranspose]

theorem tilesDensity_nonzero (n : ℕ) : tilesDensity n ≠ 0 := by
  intro h
  have ht := tilesDensity_trace n
  rw [h, Matrix.trace_zero] at ht
  norm_num at ht

/-- Exact Schmidt number of the normalized density operator, using the
unrestricted finite pure-state decomposition definition. -/
theorem tilesDensity_schmidtNumber_exact (n k : ℕ) :
    PureCone (HasSR k) (tilesDensity n) ↔ 2^(n+1) ≤ k := by
  rw [tilesDensity, ← tilesAmplitude_normsq,
    PureCone.smul_normsq_iff _ _ (tilesAmplitude_nonzero n)]
  exact tilesPower_schmidtNumber_exact n k

theorem tilesDensity_not_transposeConeSum (n : ℕ) :
    ¬ TransposeConeSum (HasSR (2^(n+1)-1)) (tilesDensity n) := by
  rw [tilesDensity, ← tilesAmplitude_normsq,
    TransposeConeSum.smul_normsq_iff _ _ (tilesAmplitude_nonzero n)]
  exact tilesPower_not_transposeConeSum n

/-- The central statement for trace-one states, with no assumed positivity,
normalization, Schmidt-rank, or tensor-support facts left as hypotheses. -/
theorem normalized_sharp_tiles_power_family (n : ℕ) :
    Matrix.trace (tilesDensity n) = 1 ∧
      (tilesDensity n).PosSemidef ∧
      (partialTranspose (tilesDensity n)).PosSemidef ∧
      (∀ k, PureCone (HasSR k) (tilesDensity n) ↔ 2^(n+1) ≤ k) ∧
      ¬ TransposeConeSum (HasSR (2^(n+1)-1)) (tilesDensity n) := by
  exact ⟨tilesDensity_trace n, tilesDensity_posSemidef n,
    (tilesDensity_partialTranspose n).symm ▸ tilesDensity_posSemidef n,
    tilesDensity_schmidtNumber_exact n, tilesDensity_not_transposeConeSum n⟩

#print axioms normalized_sharp_tiles_power_family
#print axioms tilesDensity_schmidtNumber_exact
#print axioms tilesDensity_succ

end PPTCone
