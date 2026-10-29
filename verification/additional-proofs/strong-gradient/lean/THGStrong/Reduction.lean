import THGStrong.CertificateAPI
import THGStrong.Scaling
import THGStrong.Balance

noncomputable section
open scoped BigOperators InnerProductSpace

namespace THGStrong
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma terminal_bounds_of_interpolation {μ f : ℝ} {x g : E}
    (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hfrom : 0 ≤ Q μ 0 x 0 g 0 f)
    (hto : 0 ≤ Q μ x 0 g 0 f 0) :
    sq g ≤ sq x ∧ sq g ≤ 2*f := by
  have hfrom0 := parameter_change_nonneg μ 0 0 f 0 x 0 g hμ1 hμ0 hfrom
  have hto0 := parameter_change_nonneg μ 0 f 0 x 0 g 0 hμ1 hμ0 hto
  have hd := sq_nonneg (x-g)
  simp only [Q, sq, zero_mul, sub_zero, smul_zero, zero_smul,
    inner_zero_left, inner_zero_right, zero_sub, inner_neg_left,
    inner_neg_right, inner_sub_left, inner_sub_right] at hfrom0 hto0 hd
  rw [real_inner_comm g x] at hd
  unfold sq
  constructor <;> nlinarith

lemma progress_invPower_identity {μ h a : ℝ} (ha : a ≠ 0)
    (hparam : a = 1-μ*h) (N : ℕ) :
    invPower a N = 1+μ*progressSum h a N := by
  have hi := invPower_sub_one ha N
  unfold progressSum
  rw [hparam] at hi ⊢
  nlinarith only [hi]

lemma terminal_joint_to_gradient {μ S A R f : ℝ} {x g : E}
    (hμ : μ < 1) (hS : 0 ≤ S) (hA : 0 ≤ A) (hparam : A = 1+μ*S)
    (hx : sq g ≤ sq x) (hf : sq g ≤ 2*f)
    (hjoint : A*sq x+2*(1-μ)*S*f+S*(S+1)*sq g ≤ R) :
    (1+S)^2 * sq g ≤ R := by
  have hx' := mul_le_mul_of_nonneg_left hx hA
  have hf' := mul_le_mul_of_nonneg_left hf
    (mul_nonneg (sub_nonneg.mpr (le_of_lt hμ)) hS)
  have hc : (1+S)^2 = A+(1-μ)*S+S*(S+1) := by rw [hparam]; ring
  rw [hc, add_mul, add_mul]
  nlinarith only [hx', hf', hjoint]

lemma balanced_joint_of_certificate (cert : BalancedHistoryBound E)
    (N : ℕ) (h a μ : ℝ) (x g : ℕ → E) (f : ℕ → ℝ)
    (hN : 0 < N) (hh : 1 < h) (hh2 : h < 2) (hra : h-1 < a)
    (hparam : a = 1-μ*h) (hbal : invPower (h-1) N = 1+progressSum h a N)
    (hstep : ∀ i < N, x (i+1) = x i-h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ Q μ (x i) (x j) (g i) (g j) (f i) (f j))
    (hstar : ∀ i < N, 0 ≤ Q μ 0 (x i) 0 (g i) 0 (f i)) :
    invPower a N * sq (x N)+2*(1-μ)*progressSum h a N*f N+
      progressSum h a N*(progressSum h a N+1)*sq (g N) ≤ sq (x 0) := by
  have hb := cert N h a μ x g f hN hh hh2 hra hparam hbal hstep hQ
  have hs : 0 ≤ ∑ i ∈ Finset.range N,
      h*(a⁻¹)^(i+1)*Q μ 0 (x i) 0 (g i) 0 (f i) := by
    apply Finset.sum_nonneg
    intro i hi
    have ha : 0 < a := by linarith
    exact mul_nonneg (by positivity) (hstar i (Finset.mem_range.mp hi))
  linarith

lemma lower_branch_joint (cert : BalancedHistoryBound E)
    (N : ℕ) (h μ : ℝ) (x g : ℕ → E) (f : ℕ → ℝ)
    (hN : 0 < N) (hh : 0 < h) (hh2 : h < 2)
    (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (ha : 0 < 1-μ*h)
    (hbranch : 1 < h → (h-1)^N*(1+progressSum h (1-μ*h) N) ≤ 1)
    (hstep : ∀ i < N, x (i+1) = x i-h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ Q μ (x i) (x j) (g i) (g j) (f i) (f j))
    (hstar : ∀ i < N, 0 ≤ Q μ 0 (x i) 0 (g i) 0 (f i)) :
    invPower (1-μ*h) N * sq (x N)+
      2*(1-μ)*progressSum h (1-μ*h) N*f N+
      progressSum h (1-μ*h) N*(progressSum h (1-μ*h) N+1)*sq (g N)
      ≤ sq (x 0) := by
  let a := 1-μ*h
  let S := progressSum h a N
  obtain ⟨H, hH1, hhH, hHa, hbalance⟩ := balance_exists_lower hh ha hN hbranch
  change 0 < a at ha
  change H < 1+a at hHa
  change invPower (H-1) N = 1+progressSum H a N at hbalance
  have hH0 : 0 < H := by linarith
  have ha1 : a ≤ 1 := by dsimp [a]; nlinarith
  have hH2 : H < 2 := by change H < 1+a at hHa; linarith
  let s := h/H
  obtain ⟨hs0, hs1, _, hsmu, hparam, _⟩ :=
    scaling_parameters hh hH1 hhH hμ0 hμ1
  change 0 < s at hs0
  change s ≤ 1 at hs1
  have h1s : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have hHs : H*s = h := by dsimp [s]; field_simp
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hscaledStep (i : ℕ) (hi : i < N) :
      x (i+1) = x i-H • (s • g i) := by
    rw [smul_smul, hHs]
    exact hstep i hi
  have hscaledQ (i : ℕ) (hi : i ≤ N) (j : ℕ) (hj : j ≤ N) :
      0 ≤ Q (s*μ) (x i) (x j) (s • g i) (s • g j) (s*f i) (s*f j) :=
    scale_interpolation_nonneg μ s (f i) (f j) (x i) (x j) (g i) (g j)
      hμ1 (le_of_lt hs0) hs1 (hQ i hi j hj)
  have hb := cert N H a (s*μ) x (fun i => s • g i) (fun i => s*f i)
    hN hH1 hH2 (by linarith) (Eq.symm hparam) hbalance hscaledStep hscaledQ
  have hSscale : progressSum H a N = S/s :=
    scaled_progressSum (ne_of_gt hh) (ne_of_gt hH0)
  have hpot (i : ℕ) (hi : i < N) :
      sq (g N)-2*μ*f N ≤ sq (g i)-2*μ*f i := by
    apply potential_monotone μ h x g f N hh hμ1 (le_of_lt ha) (le_of_lt hh2)
      hstep
    · intro j hj
      exact hQ j (le_of_lt hj) (j+1) (Nat.succ_le_of_lt hj)
    · intro j hj
      exact hQ (j+1) (Nat.succ_le_of_lt hj) j (le_of_lt hj)
    · exact le_of_lt hi
  have hstarpoint (i : ℕ) (hi : i ∈ Finset.range N) :
      (1-s)*h*(a⁻¹)^(i+1)*(sq (g N)-2*μ*f N) ≤
        H*(a⁻¹)^(i+1)*Q (s*μ) 0 (x i) 0 (s • g i) 0 (s*f i) := by
    have hc : 0 ≤ (1-s)*h*(a⁻¹)^(i+1) := by positivity
    have hq := mul_nonneg (show 0 ≤ h*(a⁻¹)^(i+1) by positivity)
      (hstar i (Finset.mem_range.mp hi))
    have hp := mul_le_mul_of_nonneg_left (hpot i (Finset.mem_range.mp hi)) hc
    rw [scale_star_identity]
    have he : H*(a⁻¹)^(i+1)*(s*Q μ 0 (x i) 0 (g i) 0 (f i)+
        s*(1-s)*(sq (g i)-2*μ*f i)) =
        h*(a⁻¹)^(i+1)*Q μ 0 (x i) 0 (g i) 0 (f i)+
        (1-s)*h*(a⁻¹)^(i+1)*(sq (g i)-2*μ*f i) := by
      calc
        _ = (H*s)*(a⁻¹)^(i+1)*Q μ 0 (x i) 0 (g i) 0 (f i)+
          (1-s)*(H*s)*(a⁻¹)^(i+1)*(sq (g i)-2*μ*f i) := by ring
        _ = _ := by rw [hHs]
    rw [he]
    linarith
  have hstars := Finset.sum_le_sum hstarpoint
  have hsum : (∑ i ∈ Finset.range N,
      (1-s)*h*(a⁻¹)^(i+1)*(sq (g N)-2*μ*f N)) =
      (1-s)*S*(sq (g N)-2*μ*f N) := by
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    dsimp [S, progressSum, geomSum]
    ring
  rw [hsum] at hstars
  have hgsq : sq (s • g N) = s^2*sq (g N) := by
    simp only [sq, real_inner_smul_left, real_inner_smul_right]
    ring
  simp only [hSscale, hgsq] at hb
  have he : invPower a N*sq (x N)+2*(1-s*μ)*(S/s)*(s*f N)+
      (S/s)*(S/s+1)*(s^2*sq (g N))+
      (1-s)*S*(sq (g N)-2*μ*f N) =
      invPower a N*sq (x N)+2*(1-μ)*S*f N+S*(S+1)*sq (g N) := by
    field_simp [hsne]
    ring
  change invPower a N*sq (x N)+2*(1-μ)*S*f N+S*(S+1)*sq (g N) ≤ _
  rw [← he]
  exact le_trans (add_le_add_left hstars _) hb

lemma upper_balanced_parameter {h μ : ℝ} {N : ℕ}
    (hh : 1 < h) (hh2 : h < 2) (hN : 0 < N)
    (hbranch : 0 < 1-μ*h → invPower (h-1) N ≤ 1+progressSum h (1-μ*h) N) :
    ∃ b : ℝ, 1-μ*h ≤ b ∧ h-1 < b ∧
      invPower (h-1) N = 1+progressSum h b N := by
  by_cases ha : 0 < 1-μ*h
  · exact balance_exists_upper hh hh2 ha hN (by linarith [hbranch ha])
  · have hr : 0 < h-1 := by linarith
    have hG : 0 < geomSum (h-1) N := geomSum_pos hr hN
    have hleft : invPower (h-1) N-1 ≤ progressSum h (h-1) N := by
      rw [invPower_sub_one (ne_of_gt hr)]
      unfold progressSum
      nlinarith
    obtain ⟨b, hb, hrb, hbal⟩ := balance_exists_upper hh hh2 hr hN hleft
    exact ⟨b, by linarith, hrb, hbal⟩

lemma upper_branch_gradient (cert : BalancedHistoryBound E)
    (N : ℕ) (h μ : ℝ) (x g : ℕ → E) (f : ℕ → ℝ)
    (hN : 0 < N) (hh : 1 < h) (hh2 : h < 2) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hbranch : 0 < 1-μ*h → invPower (h-1) N ≤ 1+progressSum h (1-μ*h) N)
    (hstep : ∀ i < N, x (i+1) = x i-h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ Q μ (x i) (x j) (g i) (g j) (f i) (f j))
    (hstar : ∀ i ≤ N, 0 ≤ Q μ 0 (x i) 0 (g i) 0 (f i))
    (hto : 0 ≤ Q μ (x N) 0 (g N) 0 (f N) 0) :
    (invPower (h-1) N)^2*sq (g N) ≤ sq (x 0) := by
  obtain ⟨b, hb, hrb, hbal⟩ := upper_balanced_parameter hh hh2 hN hbranch
  obtain ⟨hνμ, hν1, hparam⟩ := weaker_curvature_parameters (by linarith) hμ1 hb
  let ν := (1-b)/h
  have hb0 : 0 < b := by linarith
  have hQν (i : ℕ) (hi : i ≤ N) (j : ℕ) (hj : j ≤ N) :
      0 ≤ Q ν (x i) (x j) (g i) (g j) (f i) (f j) :=
    parameter_change_nonneg μ ν (f i) (f j) (x i) (x j) (g i) (g j)
      hμ1 hνμ (hQ i hi j hj)
  have hstarν (i : ℕ) (hi : i < N) : 0 ≤ Q ν 0 (x i) 0 (g i) 0 (f i) :=
    parameter_change_nonneg μ ν 0 (f i) 0 (x i) 0 (g i)
      hμ1 hνμ (hstar i (le_of_lt hi))
  have hj := balanced_joint_of_certificate cert N h b ν x g f hN hh hh2 hrb
    hparam.symm hbal hstep hQν hstarν
  obtain ⟨hx, hf⟩ := terminal_bounds_of_interpolation hμ0 hμ1 (hstar N le_rfl) hto
  have hs : 0 ≤ progressSum h b N :=
    le_of_lt (progressSum_pos (by linarith) hb0 hN)
  have hA : 0 ≤ invPower b N := le_of_lt (invPower_pos hb0 N)
  have hAi := progress_invPower_identity (ne_of_gt hb0) hparam.symm N
  have hg := terminal_joint_to_gradient hν1 hs hA hAi hx hf hj
  rwa [← hbal] at hg

/-- The conjectured norm rate, written without a negative power at a zero base. -/
def gradientRate (μ h : ℝ) (N : ℕ) : ℝ :=
  max (if μ = 0 then (1+(N:ℝ)*h)⁻¹ else
    μ*(1-μ*h)^N/(1-(1-μ)*(1-μ*h)^N)) (|1-h|^N)

lemma oscillation_le_gradientRate (μ h : ℝ) (N : ℕ) :
    |1-h|^N ≤ gradientRate μ h N := le_max_right _ _

lemma gradientRate_nonneg (μ h : ℝ) (N : ℕ) :
    0 ≤ gradientRate μ h N :=
  le_trans (pow_nonneg (abs_nonneg _) _) (oscillation_le_gradientRate μ h N)

lemma progress_rate_formula {μ h : ℝ} (hμ0 : 0 ≤ μ) (hh : 0 < h)
    (ha : 0 < 1-μ*h) (N : ℕ) :
    (1+progressSum h (1-μ*h) N)⁻¹ =
      if μ = 0 then (1+(N:ℝ)*h)⁻¹ else
        μ*(1-μ*h)^N/(1-(1-μ)*(1-μ*h)^N) := by
  by_cases hμ : μ = 0
  · simp [hμ, progressSum, geomSum, mul_comm]
  · rw [if_neg hμ]
    have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμ)
    let a := 1-μ*h
    let S := progressSum h a N
    have hS : 0 ≤ S := by
      dsimp [S, progressSum, geomSum]
      positivity
    have hi := progress_invPower_identity (ne_of_gt ha) (rfl : a = 1-μ*h) N
    change invPower a N = 1+μ*S at hi
    have hpow : a^N*invPower a N = 1 := by
      rw [invPower, ← mul_pow, mul_inv_cancel₀ (ne_of_gt ha), one_pow]
    have hid : 1-(1-μ)*a^N = μ*a^N*(1+S) := by
      have hi' := congrArg (fun z : ℝ => a^N*z) hi
      change a^N*invPower a N = a^N*(1+μ*S) at hi'
      rw [hpow] at hi'
      nlinarith only [hi']
    have hpa : 0 < a^N := pow_pos ha N
    change (1+S)⁻¹ = μ*a^N/(1-(1-μ)*a^N)
    rw [hid]
    field_simp [ne_of_gt hμpos, ne_of_gt hpa, show 1+S ≠ 0 by linarith]

lemma weighted_sq_to_norm {c : ℝ} {x g : E} (hc : 0 < c)
    (hb : c^2*sq g ≤ sq x) : ‖g‖ ≤ c⁻¹*‖x‖ := by
  have hs : c*‖g‖ ≤ ‖x‖ := by
    have hcn : 0 ≤ c*‖g‖ := mul_nonneg (le_of_lt hc) (norm_nonneg _)
    simp only [sq, real_inner_self_eq_norm_sq] at hb
    nlinarith [norm_nonneg x]
  have hm := mul_le_mul_of_nonneg_left hs (le_of_lt (inv_pos.mpr hc))
  simpa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc)] using hm

lemma interpolated_gradient_rate (cert : BalancedHistoryBound E)
    (N : ℕ) (h μ : ℝ) (x g : ℕ → E) (f : ℕ → ℝ)
    (hN : 0 < N) (hh : 0 < h) (hh2 : h < 2) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hstep : ∀ i < N, x (i+1) = x i-h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ Q μ (x i) (x j) (g i) (g j) (f i) (f j))
    (hstar : ∀ i ≤ N, 0 ≤ Q μ 0 (x i) 0 (g i) 0 (f i))
    (hto : 0 ≤ Q μ (x N) 0 (g N) 0 (f N) 0) :
    ‖g N‖ ≤ gradientRate μ h N*‖x 0‖ := by
  by_cases hlow : 0 < 1-μ*h ∧
      (1 < h → (h-1)^N*(1+progressSum h (1-μ*h) N) ≤ 1)
  · obtain ⟨ha, hbranch⟩ := hlow
    have hj := lower_branch_joint cert N h μ x g f hN hh hh2 hμ0 hμ1 ha hbranch
      hstep hQ (fun i hi => hstar i (le_of_lt hi))
    obtain ⟨hx, hf⟩ := terminal_bounds_of_interpolation hμ0 hμ1 (hstar N le_rfl) hto
    have hS := le_of_lt (progressSum_pos hh ha hN)
    have hA := le_of_lt (invPower_pos ha N)
    have hAi := progress_invPower_identity (ne_of_gt ha) rfl N
    have hg := terminal_joint_to_gradient hμ1 hS hA hAi hx hf hj
    have hn := weighted_sq_to_norm (show 0 < 1+progressSum h (1-μ*h) N by linarith) hg
    apply le_trans hn
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [progress_rate_formula hμ0 hh ha N]
    exact le_max_left _ _
  · have hh1 : 1 < h := by
      by_contra hn
      have hh1 : h ≤ 1 := le_of_not_gt hn
      have ha : 0 < 1-μ*h := by
        have hm := mul_le_mul_of_nonneg_left hh1 hμ0
        nlinarith
      exact hlow ⟨ha, fun ht => False.elim (not_lt_of_ge hh1 ht)⟩
    have hbranch : 0 < 1-μ*h →
        invPower (h-1) N ≤ 1+progressSum h (1-μ*h) N := by
      intro ha
      have hn : ¬(h-1)^N*(1+progressSum h (1-μ*h) N) ≤ 1 := by
        intro hp
        exact hlow ⟨ha, fun _ => hp⟩
      exact (branch_comparison (show 0 < h-1 by linarith) N).2.mp
        (le_of_lt (lt_of_not_ge hn))
    have hg := upper_branch_gradient cert N h μ x g f hN hh1 hh2 hμ0 hμ1
      hbranch hstep hQ hstar hto
    have hn := weighted_sq_to_norm (invPower_pos (show 0 < h-1 by linarith) N) hg
    have hi : (invPower (h-1) N)⁻¹ = |1-h|^N := by
      simp only [invPower, ← inv_pow, inv_inv]
      rw [abs_of_neg (show 1-h < 0 by linarith)]
      congr 1
      ring
    rw [hi] at hn
    exact le_trans hn (mul_le_mul_of_nonneg_right
      (oscillation_le_gradientRate μ h N) (norm_nonneg _))

lemma interpolation_cocoercive {f : ℝ} {x g : E}
    (hfrom : 0 ≤ Q 0 0 x 0 g 0 f) (hto : 0 ≤ Q 0 x 0 g 0 f 0) :
    sq g ≤ ⟪g,x⟫_ℝ := by
  simp only [Q, sq, zero_mul, sub_zero, smul_zero, zero_smul,
    inner_zero_left, inner_zero_right, zero_sub, inner_neg_left,
    inner_neg_right] at hfrom hto
  unfold sq
  nlinarith

lemma interpolation_nonexpansive_step {h f : ℝ} {x g : E}
    (hh : 0 ≤ h) (hh2 : h ≤ 2)
    (hfrom : 0 ≤ Q 0 0 x 0 g 0 f) (hto : 0 ≤ Q 0 x 0 g 0 f 0) :
    sq (x-h • g) ≤ sq x := by
  have hc := interpolation_cocoercive hfrom hto
  have hm := mul_nonneg hh (sub_nonneg.mpr hc)
  have hn := mul_nonneg (mul_nonneg hh (sub_nonneg.mpr hh2)) (sq_nonneg g)
  simp only [sq, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right] at *
  rw [real_inner_comm g x]
  nlinarith only [hm, hn]

lemma interpolated_distance_bound (N : ℕ) (h : ℝ) (x g : ℕ → E) (f : ℕ → ℝ)
    (hh : 0 ≤ h) (hh2 : h ≤ 2)
    (hstep : ∀ i < N, x (i+1) = x i-h • g i)
    (hstar : ∀ i ≤ N, 0 ≤ Q 0 0 (x i) 0 (g i) 0 (f i))
    (hto : ∀ i ≤ N, 0 ≤ Q 0 (x i) 0 (g i) 0 (f i) 0) :
    ‖g N‖ ≤ ‖x 0‖ := by
  have hx (i : ℕ) (hi : i ≤ N) : sq (x i) ≤ sq (x 0) := by
    induction i with
    | zero => exact le_rfl
    | succ i ih =>
      rw [hstep i (Nat.lt_of_succ_le hi)]
      exact le_trans (interpolation_nonexpansive_step hh hh2
        (hstar i (by omega)) (hto i (by omega))) (ih (by omega))
  have ht := (terminal_bounds_of_interpolation (μ := 0) (by norm_num) (by norm_num)
    (hstar N le_rfl) (hto N le_rfl)).1
  have hn := le_trans ht (hx N le_rfl)
  simp only [sq, real_inner_self_eq_norm_sq] at hn
  nlinarith [norm_nonneg (g N), norm_nonneg (x 0)]

lemma gradientRate_ge_one_at_boundary {μ h : ℝ} {N : ℕ}
    (hedge : N = 0 ∨ h = 0 ∨ h = 2) : 1 ≤ gradientRate μ h N := by
  have ho : |1-h|^N = 1 := by
    rcases hedge with hN | hh | hh
    · simp [hN]
    · simp [hh]
    · norm_num [hh]
  simpa [ho] using oscillation_le_gradientRate μ h N

lemma interpolated_gradient_rate_closed (cert : BalancedHistoryBound E)
    (N : ℕ) (h μ : ℝ) (x g : ℕ → E) (f : ℕ → ℝ)
    (hh : 0 ≤ h) (hh2 : h ≤ 2) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hstep : ∀ i < N, x (i+1) = x i-h • g i)
    (hQ : ∀ i ≤ N, ∀ j ≤ N, 0 ≤ Q μ (x i) (x j) (g i) (g j) (f i) (f j))
    (hstar : ∀ i ≤ N, 0 ≤ Q μ 0 (x i) 0 (g i) 0 (f i))
    (hto : ∀ i ≤ N, 0 ≤ Q μ (x i) 0 (g i) 0 (f i) 0) :
    ‖g N‖ ≤ gradientRate μ h N*‖x 0‖ := by
  by_cases hedge : N = 0 ∨ h = 0 ∨ h = 2
  · have hstar0 (i : ℕ) (hi : i ≤ N) :=
      parameter_change_nonneg μ 0 0 (f i) 0 (x i) 0 (g i) hμ1 hμ0 (hstar i hi)
    have hto0 (i : ℕ) (hi : i ≤ N) :=
      parameter_change_nonneg μ 0 (f i) 0 (x i) 0 (g i) 0 hμ1 hμ0 (hto i hi)
    have hb := interpolated_distance_bound N h x g f hh hh2 hstep hstar0 hto0
    have hr := mul_le_mul_of_nonneg_right (gradientRate_ge_one_at_boundary (μ := μ) hedge)
      (norm_nonneg (x 0))
    exact le_trans hb (by simpa only [one_mul] using hr)
  · have hN : 0 < N := Nat.pos_of_ne_zero (fun he => hedge (Or.inl he))
    have hh0 : 0 < h := lt_of_le_of_ne hh (by
      intro he
      exact hedge (Or.inr (Or.inl he.symm)))
    have hh2' : h < 2 := lt_of_le_of_ne hh2 (by
      intro he
      exact hedge (Or.inr (Or.inr he)))
    exact interpolated_gradient_rate cert N h μ x g f hN hh0 hh2' hμ0 hμ1
      hstep hQ hstar (hto N le_rfl)

#print axioms lower_branch_joint
#print axioms upper_branch_gradient
#print axioms interpolated_gradient_rate
#print axioms interpolated_gradient_rate_closed

end THGStrong
