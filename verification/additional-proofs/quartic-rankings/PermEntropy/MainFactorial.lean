import PermEntropy.Energy
import PermEntropy.Split
import PermEntropy.Crossing
import PermEntropy.Restriction
import PermEntropy.FactorialAlgebra

noncomputable section
namespace PermEntropy
namespace FinDist
universe u

set_option maxHeartbeats 1000000 in
private theorem entropy_factorial_aux (n : ℕ) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V], Fintype.card V = n →
    ∀ (p : FinDist (Ranking V)) (b : ℝ), 0 < b →
      (∀ x y : V, x ≠ y → b ≤ |p.meanComparison x y|) →
      p.entropy ≤ (1 - b^4 / 2304) * Real.log ((Fintype.card V).factorial : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ hn p b hb hbias
    classical
    by_cases hsmall : Fintype.card V ≤ 1
    · haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hsmall
      rw [p.entropy_of_subsingleton]
      have hfac : (Fintype.card V).factorial = 1 := by
        have hzero : Fintype.card V = 0 ∨ Fintype.card V = 1 := by omega
        rcases hzero with hzero | hone
        · simp [hzero]
        · simp [hone]
      simp [hfac]
    · have hm : 2 ≤ Fintype.card V := by omega
      obtain ⟨L, R, hd, hL, hR, hcut⟩ := p.exists_meanComparison_cut b hb hm hbias
      let Q : Finset V := L ∪ R
      let S : Finset Q := inside Q R
      let pQ : FinDist (Ranking Q) := p.map (fun r => r.restrict Q)
      let pW : FinDist (Ranking (↥(Qᶜ : Finset V))) := p.map (fun r => r.restrict Qᶜ)
      let pR : FinDist (Ranking S) := pQ.map (fun r => r.restrict S)
      let pA : FinDist (Ranking (↥(Sᶜ : Finset Q))) := pQ.map (fun r => r.restrict Sᶜ)
      have hQcard : Q.card = L.card + R.card := Finset.card_union_of_disjoint hd
      have hScard : S.card = R.card := card_inside Q R Finset.subset_union_right
      have hAcard : (Sᶜ).card = L.card := by
        dsimp [S, Q]
        rw [inside_union_compl L R hd]
        exact card_inside _ _ Finset.subset_union_left
      have hQle : Q.card ≤ Fintype.card V := Finset.card_le_univ Q
      have hLpos : 0 < L.card := Finset.card_pos.mpr hL
      have hRpos : 0 < R.card := Finset.card_pos.mpr hR
      have hQpos : 0 < Q.card := by omega
      have hQW : Q.card + (Qᶜ).card = Fintype.card V := Finset.card_add_card_compl Q
      have hSlt : Fintype.card S < n := by
        simp only [Fintype.card_coe]
        omega
      have hAlt : Fintype.card (↥(Sᶜ : Finset Q)) < n := by
        simp only [Fintype.card_coe]
        omega
      have hWlt : Fintype.card (↥(Qᶜ : Finset V)) < n := by
        simp only [Fintype.card_coe]
        omega
      have hbQ : ∀ x y : Q, x ≠ y → b ≤ |pQ.meanComparison x y| := by
        intro x y hxy
        simpa [pQ] using hbias x.val y.val (fun h => hxy (Subtype.ext h))
      have hbW : ∀ x y : ↥(Qᶜ : Finset V), x ≠ y → b ≤ |pW.meanComparison x y| := by
        intro x y hxy
        simpa [pW] using hbias x.val y.val (fun h => hxy (Subtype.ext h))
      have hbR : ∀ x y : S, x ≠ y → b ≤ |pR.meanComparison x y| := by
        intro x y hxy
        simpa [pR] using hbQ x.val y.val (fun h => hxy (Subtype.ext h))
      have hbA : ∀ x y : ↥(Sᶜ : Finset Q), x ≠ y → b ≤ |pA.meanComparison x y| := by
        intro x y hxy
        simpa [pA] using hbQ x.val y.val (fun h => hxy (Subtype.ext h))
      have hrecR := ih (Fintype.card S) hSlt S rfl pR b hb hbR
      have hrecA := ih (Fintype.card (↥(Sᶜ : Finset Q))) hAlt (↥(Sᶜ : Finset Q)) rfl pA b hb hbA
      have hrecW := ih (Fintype.card (↥(Qᶜ : Finset V))) hWlt (↥(Qᶜ : Finset V)) rfl pW b hb hbW
      simp only [Fintype.card_coe, hScard] at hrecR
      simp only [Fintype.card_coe, hAcard] at hrecA
      simp only [Fintype.card_coe] at hrecW
      have houter := p.entropy_ranking_split Q
      have hinner := pQ.entropy_ranking_split S
      change p.entropy ≤ pQ.entropy + pW.entropy +
        (p.map (fun r => r.membershipWord Q)).entropy at houter
      change pQ.entropy ≤ pR.entropy + pA.entropy +
        (pQ.map (fun r => r.membershipWord S)).entropy at hinner
      have houterWord := p.membershipWord_entropy_le_log_choose_no_deficit Q
      have hinnerWord := pQ.membershipWord_entropy_le_log_choose S
      have hcutId : cutSum pQ.meanComparison Sᶜ S = cutSum p.meanComparison L R := by
        change cutSum (p.map (fun r => r.restrict (L ∪ R))).meanComparison
          (inside (L ∪ R) R)ᶜ (inside (L ∪ R) R) = _
        exact p.meanComparison_cut_restrict_union L R hd
      rw [hcutId] at hinnerWord
      simp only [Fintype.card_coe, hScard] at hinnerWord
      have hcut' : (b^4 * (Fintype.card V : ℝ) / 576) * (Q.card : ℝ)^3 ≤
          (cutSum p.meanComparison L R)^2 := by simpa only [hQcard] using hcut
      have hloss := cut_entropy_loss_ge b (Fintype.card V) Q.card
        (cutSum p.meanComparison L R) hQpos hcut'
      apply factorial_entropy_induction_step b (Fintype.card V) p.entropy
        (Real.log (L.card.factorial : ℝ) + Real.log (R.card.factorial : ℝ) +
          Real.log ((Qᶜ).card.factorial : ℝ))
        (Real.log (Q.card.choose R.card : ℝ) +
          Real.log ((Fintype.card V).choose Q.card : ℝ))
        (Real.log ((Fintype.card V).factorial : ℝ))
      · exact factorial_merge_identity L.card R.card Q.card (Qᶜ).card
          (Fintype.card V) hQcard.symm hQW
      · exact factorial_merge_le_two_mul Q.card R.card (Fintype.card V)
          (by omega) hQle
      · nlinarith only [houter, hinner, houterWord, hinnerWord, hrecR, hrecA, hrecW, hloss]

/-- The entropy bound for every finite size, stated in signed mean comparisons. -/
theorem entropy_quartic_log_factorial_all {V : Type u} [Fintype V] [DecidableEq V]
    (p : FinDist (Ranking V)) (b : ℝ) (hb : 0 < b)
    (hbias : ∀ x y : V, x ≠ y → b ≤ |p.meanComparison x y|) :
    p.entropy ≤ (1 - b^4 / 2304) * Real.log ((Fintype.card V).factorial : ℝ) :=
  entropy_factorial_aux (Fintype.card V) V rfl p b hb hbias

end FinDist
end PermEntropy
