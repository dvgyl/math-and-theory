import GapAlgebra

open scoped BigOperators

namespace ADMMNearSharpCertificate

open ADMMBarrier ADMMNearSharp

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

noncomputable def rawGap (X Z Zprev Vprev : Matrix ν κ ℝ)
    (lamF lamG : Matrix ν ν ℝ) (τ : ℝ) : Matrix κ κ ℝ :=
  qsum X (Zprev - τ • Vprev - X) lamF +
  qsum Z (X + τ • Vprev - Z) lamG

theorem rawGap_affine (X Z Zprev Vprev : Matrix ν κ ℝ)
    (lamF lamG : Matrix ν ν ℝ) (a b s : ℝ) :
    rawGap X Z Zprev Vprev lamF lamG ((1-s)*a+s*b) =
      (1-s) • rawGap X Z Zprev Vprev lamF lamG a +
      s • rawGap X Z Zprev Vprev lamF lamG b := by
  simp only [rawGap, qsum_sub_normals, qsum_add_normals, qsum_smul_normals]
  module

theorem affine_psd {P0 P1 C : Matrix ι ι ℝ}
    (h0 : (P0-C).PosSemidef) (h1 : (P1-C).PosSemidef)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ((1-s) • P0 + s • P1 - C).PosSemidef := by
  have h := (psd_smul h0 (by linarith : 0 ≤ 1-s)).add (psd_smul h1 hs0)
  have he : (1-s) • (P0-C) + s • (P1-C) = (1-s) • P0 + s • P1-C := by
    module
  rwa [he] at h

theorem affine_identity (S0 S1 D : Matrix ι κ ℝ) (diss : Matrix κ κ ℝ)
    (X Z Zprev Vprev : Matrix ν κ ℝ) (lamF lamG : Matrix ν ν ℝ)
    (P0 P1 T0 T1 : Matrix ι ι ℝ) (a b s : ℝ)
    (h0 : S0.transpose * P0 * S0 - S1.transpose * P0 * S1 - diss -
      rawGap X Z Zprev Vprev lamF lamG a = D.transpose * T0 * D)
    (h1 : S0.transpose * P1 * S0 - S1.transpose * P1 * S1 - diss -
      rawGap X Z Zprev Vprev lamF lamG b = D.transpose * T1 * D) :
    S0.transpose * ((1-s) • P0 + s • P1) * S0 -
      S1.transpose * ((1-s) • P0 + s • P1) * S1 - diss -
      rawGap X Z Zprev Vprev lamF lamG ((1-s)*a+s*b) =
      D.transpose * ((1-s) • T0 + s • T1) * D := by
  rw [rawGap_affine]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have h := congrArg (fun M => (1-s) • M) h0
  have h' := congrArg (fun M => s • M) h1
  calc
    _ = (1-s) • (S0.transpose * P0 * S0 - S1.transpose * P0 * S1 - diss -
          rawGap X Z Zprev Vprev lamF lamG a) +
        s • (S0.transpose * P1 * S0 - S1.transpose * P1 * S1 - diss -
          rawGap X Z Zprev Vprev lamF lamG b) := by module
    _ = _ := by rw [h0, h1]

end ADMMNearSharpCertificate
