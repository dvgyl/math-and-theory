module
public import GeneralContraction


@[expose] public section

/-! Exact rectangular trace identities for lifted finite-dimensional dual witnesses. -/
open Matrix
open scoped BigOperators ComplexOrder
open CMICounterexample ConditionalHockey

namespace TightFramePairing
noncomputable section

variable {S F : Type} [Fintype S] [DecidableEq S] [Fintype F] [DecidableEq F]

omit [DecidableEq S] [DecidableEq F] in
theorem trace_sandwich_pairing [DecidableEq S] [DecidableEq F] (K : Matrix S F ℂ) (D : Matrix F F ℂ)
    (M : Matrix S S ℂ) :
    (K*D*Kᴴ*M).trace = (D*(Kᴴ*M*K)).trace := by
  calc
    _ = ((K*D)*(Kᴴ*M)).trace := by simp only [Matrix.mul_assoc]
    _ = ((Kᴴ*M)*(K*D)).trace := Matrix.trace_mul_comm _ _
    _ = ((Kᴴ*M*K)*D).trace := by simp only [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm _ _

omit [DecidableEq S] [DecidableEq F] in
theorem compress_base [DecidableEq S] [DecidableEq F] (T : Matrix S S ℂ) (K : Matrix S F ℂ)
    (G J : Matrix F F ℂ) (hTK : T*K=K*J) (hGram : Kᴴ*K=G) :
    Kᴴ*T*K=G*J := by
  calc
    _ = Kᴴ*(T*K) := Matrix.mul_assoc _ _ _
    _ = Kᴴ*(K*J) := by rw [hTK]
    _ = (Kᴴ*K)*J := (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [hGram]

omit [DecidableEq S] [DecidableEq F] in
theorem compress_sandwich [DecidableEq S] [DecidableEq F] (K : Matrix S F ℂ) (G L : Matrix F F ℂ)
    (hGram : Kᴴ*K=G) : Kᴴ*(K*L*Kᴴ)*K=G*L*G := by
  calc
    _ = (Kᴴ*K)*L*(Kᴴ*K) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hGram]

theorem compress_output (T : Matrix S S ℂ) (K : Matrix S F ℂ)
    (G J L : Matrix F F ℂ) (b s : ℝ)
    (hTK : T*K=K*J) (hGram : Kᴴ*K=G) :
    Kᴴ*(b • T-s • (K*L*Kᴴ))*K = b • (G*J)-s • (G*L*G) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul, compress_base T K G J hTK hGram,
    compress_sandwich K G L hGram]

theorem trace_base_sandwich (T : Matrix S S ℂ) (K : Matrix S F ℂ)
    (G J L : Matrix F F ℂ) (hTK : T*K=K*J) (hGram : Kᴴ*K=G) :
    (T*(K*L*Kᴴ)).trace = (L*G*J).trace := by
  calc
    _ = (K*L*Kᴴ*T).trace := Matrix.trace_mul_comm _ _
    _ = (L*(Kᴴ*T*K)).trace := trace_sandwich_pairing K L T
    _ = (L*(G*J)).trace := by rw [compress_base T K G J hTK hGram]
    _ = _ := by rw [Matrix.mul_assoc]

theorem lifted_input_pairing (T : Matrix S S ℂ) (K : Matrix S F ℂ)
    (G J D L : Matrix F F ℂ) (hTK : T*K=K*J) (hGram : Kᴴ*K=G) :
    ((T+K*D*Kᴴ)*(K*L*Kᴴ)).trace.re =
      (L*G*J).trace.re+(D*G*L*G).trace.re := by
  rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re,
    trace_base_sandwich T K G J L hTK hGram]
  have heq : (K*D*Kᴴ*(K*L*Kᴴ)).trace = (D*G*L*G).trace := by
    rw [trace_sandwich_pairing K D (K*L*Kᴴ), compress_sandwich K G L hGram]
    simp only [Matrix.mul_assoc]
  rw [heq]

theorem lifted_output_pairing (T : Matrix S S ℂ) (K : Matrix S F ℂ)
    (G J D L : Matrix F F ℂ) (b s : ℝ)
    (hTK : T*K=K*J) (hGram : Kᴴ*K=G) :
    ((T+K*D*Kᴴ)*(b • T-s • (K*L*Kᴴ))).trace.re =
      b*(T*T).trace.re+
        (D*(b • (G*J)-s • (G*L*G))).trace.re-
        s*(L*G*J).trace.re := by
  rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  have hbase : (T*(b • T-s • (K*L*Kᴴ))).trace.re =
      b*(T*T).trace.re-s*(L*G*J).trace.re := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_smul, Complex.sub_re,
      trace_base_sandwich T K G J L hTK hGram]
    simp only [Complex.smul_re, smul_eq_mul]
  have hcorr : (K*D*Kᴴ*(b • T-s • (K*L*Kᴴ))).trace =
      (D*(b • (G*J)-s • (G*L*G))).trace := by
    rw [trace_sandwich_pairing K D _, compress_output T K G J L b s hTK hGram]
  rw [hbase, hcorr]
  ring

end
end TightFramePairing
