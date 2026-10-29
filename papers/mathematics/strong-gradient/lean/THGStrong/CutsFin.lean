import THGStrong.Cuts
import Lean.Elab.Tactic.Omega

noncomputable section
open scoped BigOperators
open Finset

namespace THGStrong

lemma cutPrefix_add_after {ι : Type*} [Fintype ι] [LinearOrder ι]
    (u : ι → ℝ) (i : ι) : cutPrefix u i + cutAfter u i = ∑ k, u k := by
  unfold cutPrefix cutAfter
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  by_cases hki : k ≤ i
  · simp [hki, not_lt_of_ge hki]
  · simp [hki, lt_of_not_ge hki]

lemma cutBefore_fin (F : ℕ → ℝ) (N : ℕ) (i : Fin (N+1)) :
    cutBefore (fun k : Fin (N+1) => F k) i = ∑ k ∈ range i.val, F k := by
  unfold cutBefore
  change (∑ k : Fin (N+1), if k.val < i.val then F k.val else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < i.val then F k else 0) (N+1)]
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range]
  have hi := i.isLt
  omega

lemma cutPrefix_fin (F : ℕ → ℝ) (N : ℕ) (i : Fin (N+1)) :
    cutPrefix (fun k : Fin (N+1) => F k) i = ∑ k ∈ range (i.val+1), F k := by
  unfold cutPrefix
  change (∑ k : Fin (N+1), if k.val ≤ i.val then F k.val else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ i.val then F k else 0) (N+1)]
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range]
  have hi := i.isLt
  omega

lemma cutPrefix_forward_difference (F : ℕ → ℝ) (N : ℕ) (i : Fin (N+1)) :
    cutPrefix (fun k : Fin (N+1) => F (k.val+1)-F k.val) i = F (i.val+1)-F 0 := by
  rw [cutPrefix_fin (fun k => F (k+1)-F k) N i, sum_range_sub]

lemma cutBefore_forward_difference (F : ℕ → ℝ) (N : ℕ) (i : Fin (N+1)) :
    cutBefore (fun k : Fin (N+1) => F (k.val+1)-F k.val) i = F i.val-F 0 := by
  rw [cutBefore_fin (fun k => F (k+1)-F k) N i, sum_range_sub]

lemma cutAfter_backward_difference (F : ℕ → ℝ) (N : ℕ) (i : Fin (N+1)) :
    cutAfter (fun k : Fin (N+1) => F k.val-F (k.val+1)) i = F (i.val+1)-F (N+1) := by
  have ht := cutPrefix_add_after (fun k : Fin (N+1) => F k.val-F (k.val+1)) i
  rw [cutPrefix_fin (fun k => F k-F (k+1)) N i, sum_range_sub',
    Fin.sum_univ_eq_sum_range (fun k => F k-F (k+1)) (N+1), sum_range_sub'] at ht
  linarith

lemma mixed_coefficient_algebra (U Up B Bp V Vn D Dn μ h a : ℝ)
    (ha : a = 1-μ*h)
    (hforward : a*B-Bp = (h-1)*U+Up)
    (htail : V-a*Vn = D+(h-1)*Dn) :
    (U-Up)*(V-Vn)+(B-Bp)*(D-Dn) +
      h*((B-Bp)*Dn+μ*(U-Up)*Vn-U*(V-Vn)-μ*B*(D-Dn)) -
      μ*h^2*(U*Vn+B*Dn) = 0 := by
  have hi :
      (U-Up)*(V-Vn)+(B-Bp)*(D-Dn) +
        h*((B-Bp)*Dn+μ*(U-Up)*Vn-U*(V-Vn)-μ*B*(D-Dn)) -
        μ*h^2*(U*Vn+B*Dn) =
      (a*B-Bp-(h-1)*U-Up)*(V-a*Vn) -
        (a*B-Bp)*(V-a*Vn-D-(h-1)*Dn) := by
    rw [ha]
    ring
  rw [hi]
  have hf : a*B-Bp-(h-1)*U-Up = 0 := by linarith
  have ht : V-a*Vn-D-(h-1)*Dn = 0 := by linarith
  rw [hf, ht]
  ring

lemma diagonal_coefficient_algebra (U Up B Bp V Vn D Dn μ h a : ℝ)
    (ha : a = 1-μ*h)
    (hforward : a*B-Bp = (h-1)*U+Up)
    (htail : V-a*Vn = D+(h-1)*Dn) :
    (2*h*((B-Bp)*Dn+μ*(U-Up)*Vn)-μ*h^2*(U*Vn+B*Dn) -
      ((U-Up)*Vn+(D-Dn)*Bp+(V-Vn)*Up+(B-Bp)*Dn)) +
      (h-1)*((U-Up)*Vn+(D-Dn)*Bp-(V-Vn)*Up-(B-Bp)*Dn) =
    2*((h-1)^2*U*Dn-Up*D) +
      (h-2)*(((U-Up)*Vn+(D-Dn)*Bp-(V-Vn)*Up-(B-Bp)*Dn) +
        (a-1)*(U*Vn-B*Dn)) := by
  have hBp : Bp = a*B-(h-1)*U-Up := by linarith
  have hV : V = a*Vn+D+(h-1)*Dn := by linarith
  rw [hBp, hV, ha]
  ring

lemma diagonal_coefficient_zero (U Up B Bp V Vn D Dn μ h a : ℝ)
    (ha : a = 1-μ*h)
    (hforward : a*B-Bp = (h-1)*U+Up)
    (htail : V-a*Vn = D+(h-1)*Dn)
    (hwronskian : 2*((h-1)^2*U*Dn-Up*D) = 1-(h-1)^2)
    (hprogress : a*(U*Vn-B*Dn)-(Up*V-Bp*D) = h) :
    (2*h*((B-Bp)*Dn+μ*(U-Up)*Vn)-μ*h^2*(U*Vn+B*Dn) -
      ((U-Up)*Vn+(D-Dn)*Bp+(V-Vn)*Up+(B-Bp)*Dn)) =
      -(h-1)*((U-Up)*Vn+(D-Dn)*Bp-(V-Vn)*Up-(B-Bp)*Dn) := by
  have hid := diagonal_coefficient_algebra U Up B Bp V Vn D Dn μ h a ha hforward htail
  have hdiv : ((U-Up)*Vn+(D-Dn)*Bp-(V-Vn)*Up-(B-Bp)*Dn) +
      (a-1)*(U*Vn-B*Dn) = h := by
    nlinarith only [hprogress]
  rw [hwronskian, hdiv] at hid
  nlinarith only [hid]


lemma diagonal_coefficient_zero_weighted (U Up B Bp V Vn D Dn μ h a : ℝ)
    (ha : a = 1-μ*h)
    (hforward : a*B-Bp = (h-1)*U+Up)
    (htail : Up*(V-a*Vn-D-(h-1)*Dn) = 0)
    (hwronskian : 2*((h-1)^2*U*Dn-Up*D) = 1-(h-1)^2)
    (hprogress : a*(U*Vn-B*Dn)-(Up*V-Bp*D) = h) :
    (2*h*((B-Bp)*Dn+μ*(U-Up)*Vn)-μ*h^2*(U*Vn+B*Dn) -
      ((U-Up)*Vn+(D-Dn)*Bp+(V-Vn)*Up+(B-Bp)*Dn)) =
      -(h-1)*((U-Up)*Vn+(D-Dn)*Bp-(V-Vn)*Up-(B-Bp)*Dn) := by
  by_cases hUp : Up = 0
  · have hp : a*(U*Vn-B*Dn)-(0*(a*Vn+D+(h-1)*Dn)-Bp*D) = h := by
      simpa only [hUp, zero_mul] using hprogress
    have hf : a*B-Bp = (h-1)*U+0 := by simpa only [hUp] using hforward
    have hw : 2*((h-1)^2*U*Dn-0*D) = 1-(h-1)^2 := by
      simpa only [hUp] using hwronskian
    have hz := diagonal_coefficient_zero U 0 B Bp (a*Vn+D+(h-1)*Dn)
      Vn D Dn μ h a ha hf (by ring) hw hp
    simpa only [hUp, zero_mul, mul_zero, sub_zero] using hz
  · have ht : V-a*Vn-D-(h-1)*Dn = 0 := (mul_eq_zero.mp htail).resolve_left hUp
    exact diagonal_coefficient_zero U Up B Bp V Vn D Dn μ h a ha hforward
      (by linarith) hwronskian hprogress

#print axioms cutAfter_backward_difference
#print axioms mixed_coefficient_algebra
#print axioms diagonal_coefficient_zero

end THGStrong
