import KellerKlein.ZoneBAlias

noncomputable section
namespace KellerKlein

def zoneBAliasEta : ℝ := 1/2+3/Real.pi^2
def zoneBAliasDelta : ℝ := 4/(3*Real.pi)

lemma trig_linear_quadratic_bound {Q K : ℝ} (hQ : 0 < Q) (hK : 0 ≤ K) (z : ℝ) :
    Q*|Real.cos z| + K*|Real.sin z|-Q ≤ K^2/(2*Q) := by
  let C := |Real.cos z|
  let S := |Real.sin z|
  let D := K^2/(2*Q)
  have hCS : C^2+S^2=1 := by
    dsimp [C,S]
    nlinarith [Real.sin_sq_add_cos_sq z, sq_abs (Real.cos z), sq_abs (Real.sin z)]
  have hid : (Q*C+K*S)^2+(Q*S-K*C)^2=Q^2+K^2 := by
    calc
      _ = (Q^2+K^2)*(C^2+S^2) := by ring
      _ = _ := by rw [hCS]; ring
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDeq : 2*Q*D=K^2 := by dsimp [D]; field_simp
  have hnonneg : 0 ≤ Q*C+K*S := by dsimp [C,S]; positivity
  have htarget : 0 ≤ Q+D := by positivity
  change Q*C+K*S-Q ≤ D
  nlinarith [sq_nonneg (Q*S-K*C), sq_nonneg D]

lemma zoneBAlias_budget {ξ : ℝ} (hξ : 0 ≤ ξ) :
    phi0^2/2*(ξ+zoneBAliasDelta)^2+8*ξ/(3*Real.pi^3) ≤
      phi0^2/2*(ξ+zoneBAliasEta)^2+6*(ξ+1)/Real.pi^4 := by
  have hp : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hδ0 : 0 ≤ zoneBAliasDelta := by unfold zoneBAliasDelta; positivity
  have hδ : zoneBAliasDelta ≤ 4/9 := by
    unfold zoneBAliasDelta
    apply (div_le_iff₀ (by positivity : 0 < 3*Real.pi)).mpr
    linarith
  have hη : (4 : ℝ)/5 ≤ zoneBAliasEta := by
    have h : (3 : ℝ)/10 ≤ 3/Real.pi^2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) ZoneA.pi_sq_upper
    unfold zoneBAliasEta
    linarith
  have hdiff : (16 : ℝ)/45 ≤ zoneBAliasEta-zoneBAliasDelta := by linarith
  have hφ : (1521 : ℝ)/10000 ≤ phi0^2 := by
    nlinarith [ZoneA.phi0_lower, phi0_pos]
  have hp4 : Real.pi^4 ≤ 100 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ Real.pi^2) ZoneA.pi_sq_upper 2
    nlinarith
  have hsix : (3 : ℝ)/50 ≤ 6/Real.pi^4 := by
    apply (le_div_iff₀ (by positivity : 0 < Real.pi^4)).mpr
    linarith
  have hp3 : (27 : ℝ) ≤ Real.pi^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hp 3
    norm_num at h
    exact h
  have height : (8 : ℝ)/(3*Real.pi^3) ≤ 8/81 := by
    apply (div_le_iff₀ (by positivity : 0 < 3*Real.pi^3)).mpr
    linarith
  have hm : (1521:ℝ)/10000*(16/45) ≤
      phi0^2*(zoneBAliasEta-zoneBAliasDelta) :=
    mul_le_mul hφ hdiff (by norm_num) (sq_nonneg phi0)
  have hcoef : (8 : ℝ)/(3*Real.pi^3) ≤
      phi0^2*(zoneBAliasEta-zoneBAliasDelta)+6/Real.pi^4 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef hξ
  have hsq : zoneBAliasDelta^2 ≤ zoneBAliasEta^2 := by nlinarith
  have hconstant := mul_le_mul_of_nonneg_left hsq
    (by positivity : 0 ≤ phi0^2/2)
  have hpos : 0 ≤ 6/Real.pi^4 := by positivity
  ring_nf at hmul hconstant hpos ⊢
  linarith only [hmul, hconstant, hpos]

theorem zoneBAliasValue_compensated {a ξ : ℝ} (ha : 0 < a) (hξ : 0 ≤ ξ) :
    zoneBAliasValue a ξ-a^2/Real.pi^2 ≤
      phi0^2/2*(ξ+zoneBAliasEta)^2*a^4+6*(ξ+1)*a^4/Real.pi^4 := by
  have hQ : 0 < a^2/Real.pi^2 := by positivity
  have hphi := phi0_pos
  have hK : 0 ≤ (phi0/Real.pi)*(ξ+zoneBAliasDelta)*a^3 := by
    unfold zoneBAliasDelta
    positivity
  have h := trig_linear_quadratic_bound hQ hK (Real.pi*ξ)
  have he : ((phi0/Real.pi)*(ξ+zoneBAliasDelta)*a^3)^2/(2*(a^2/Real.pi^2)) =
      phi0^2/2*(ξ+zoneBAliasDelta)^2*a^4 := by
    field_simp
    ring
  rw [he] at h
  have hb := mul_le_mul_of_nonneg_right (zoneBAlias_budget hξ) (by positivity : 0 ≤ a^4)
  unfold zoneBAliasValue
  change a^2/Real.pi^2*|Real.cos (Real.pi*ξ)| +
      (phi0/Real.pi)*(ξ+zoneBAliasDelta)*a^3*|Real.sin (Real.pi*ξ)| +
      8*ξ*a^4/(3*Real.pi^3)-a^2/Real.pi^2 ≤ _
  calc
    _ = (a^2/Real.pi^2*|Real.cos (Real.pi*ξ)| +
      (phi0/Real.pi)*(ξ+zoneBAliasDelta)*a^3*|Real.sin (Real.pi*ξ)| -
      a^2/Real.pi^2) + 8*ξ*a^4/(3*Real.pi^3) := by ring
    _ ≤ phi0^2/2*(ξ+zoneBAliasDelta)^2*a^4 + 8*ξ*a^4/(3*Real.pi^3) :=
      add_le_add_right h _
    _ = (phi0^2/2*(ξ+zoneBAliasDelta)^2+8*ξ/(3*Real.pi^3))*a^4 := by ring
    _ ≤ (phi0^2/2*(ξ+zoneBAliasEta)^2+6*(ξ+1)/Real.pi^4)*a^4 := hb
    _ = _ := by ring

theorem zoneBAliasIntegral_compensated {a ξ : ℝ} (ha : 0 < a) (hξ : 0 ≤ ξ) :
    zoneBAliasIntegral a ξ-a^2/Real.pi^2 ≤
      phi0^2/2*(ξ+zoneBAliasEta)^2*a^4+6*(ξ+1)*a^4/Real.pi^4 :=
  (sub_le_sub_right (zoneBAliasIntegral_le ha hξ) _).trans
    (zoneBAliasValue_compensated ha hξ)

end KellerKlein
