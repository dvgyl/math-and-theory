import Family
import Conjecture
import CertificateAnalysis

namespace Kunisky

/-- The defined objective cannot exceed n+1 on the complete full-clause formula. -/
theorem full_certificate_le (n : ℕ) {t : Tree (Fin n)}
    (ht : t.Valid (fullFormula n)) :
    certificateValue (fullFormula n) t ≤ (n : ℝ) + 1 := by
  rw [certificateValue_fullFormula ht]
  apply certificate_le n (fun s : Fin n → Bool => t.mass (fullClause s))
  · exact fun s => t.mass_nonneg (fullClause s)
  · rw [← sum_fullFormula]
    exact t.sum_mass ht

/-- A complete family theorem: finite genuine resolution refutations make the
defined coalesced-mass certificate arbitrarily close to n+1, for every n≥3. -/
theorem exists_certificate_near (n : ℕ) (hn : 3 ≤ n) (η : ℝ) (hη : 0 < η) :
    ∃ t : Tree (Fin n), t.Valid (fullFormula n) ∧ t.conclusion = ∅ ∧
      ((n : ℝ) + 1) / (1 + η) ≤ certificateValue (fullFormula n) t := by
  let N : ℝ := Fintype.card (Fin n → Bool)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos_iff.mpr (show Nonempty (Fin n → Bool) from ⟨fun _ => true⟩))
  let ε : ℝ := η / N
  have hε : 0 < ε := div_pos hη hN
  obtain ⟨t, ht, hc, hm⟩ := exists_concentrated_refutation n hn (ε^2) (sq_pos_of_pos hε)
  refine ⟨t, ht, hc, ?_⟩
  rw [certificateValue_fullFormula ht]
  apply certificate_approx n (fun s : Fin n → Bool => t.mass (fullClause s))
    (fun s => t.mass_nonneg (fullClause s))
    (by rw [← sum_fullFormula]; exact t.sum_mass ht)
    (fun _ => true) ε η hε.le hη.le
  · exact hm.le
  · change N * (η / N) ≤ η
    rw [mul_div_cancel₀ _ (ne_of_gt hN)]

/-- The exact set over which the sharp-supremum assertion quantifies. -/
def fullCertificateValues (n : ℕ) : Set ℝ :=
  {x | ∃ t : Tree (Fin n), t.Valid (fullFormula n) ∧ t.conclusion = ∅ ∧
    certificateValue (fullFormula n) t = x}

/-- Sharp worst-case value for each explicit formula F_n. -/
theorem full_certificate_isLUB (n : ℕ) (hn : 3 ≤ n) :
    IsLUB (fullCertificateValues n) ((n : ℝ) + 1) := by
  constructor
  · rintro x ⟨t, ht, hc, rfl⟩
    exact full_certificate_le n ht
  · intro b hb
    by_contra h
    have hlt : b < (n : ℝ) + 1 := lt_of_not_ge h
    have hM : 0 < (n : ℝ) + 1 := by positivity
    by_cases hb0 : b ≤ 0
    · obtain ⟨t, ht, hc, hq⟩ := exists_certificate_near n hn 1 (by norm_num)
      have hval : certificateValue (fullFormula n) t ≤ b := hb ⟨t, ht, hc, rfl⟩
      norm_num at hq
      linarith
    · have hbp : 0 < b := lt_of_not_ge hb0
      let η : ℝ := (((n : ℝ) + 1) - b) / (2 * b)
      have hη : 0 < η := div_pos (sub_pos.mpr hlt) (by positivity)
      obtain ⟨t, ht, hc, hq⟩ := exists_certificate_near n hn η hη
      have hval : certificateValue (fullFormula n) t ≤ b := hb ⟨t, ht, hc, rfl⟩
      have hden : 0 < 1 + η := by linarith
      have hdiv : ((n : ℝ) + 1) ≤ b * (1 + η) :=
        (div_le_iff₀ hden).mp (le_trans hq hval)
      have hmul : η * (2 * b) = (n : ℝ) + 1 - b := by
        dsimp [η]
        exact div_mul_cancel₀ _ (ne_of_gt (show 0 < 2 * b by positivity))
      nlinarith

/-- No universal constant bounds this prescribed certificate, even on the
explicit complete full-clause formulas. -/
theorem certificate_unbounded (B : ℝ) :
    ∃ (n : ℕ) (t : Tree (Fin n)), 3 ≤ n ∧ Unsatisfiable (fullFormula n) ∧
      t.Valid (fullFormula n) ∧ t.conclusion = ∅ ∧
      B < certificateValue (fullFormula n) t := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (3 : ℝ) (2 * B))
  have hthree : (3 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hn3 : 3 ≤ n := by exact_mod_cast hthree.le
  have hB : 2 * B < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  obtain ⟨t, ht, hc, hq⟩ := exists_certificate_near n hn3 1 (by norm_num)
  refine ⟨n, t, hn3, t.unsatisfiable ht hc, ht, hc, ?_⟩
  norm_num at hq
  linarith

#print axioms full_certificate_le
#print axioms exists_certificate_near
#print axioms full_certificate_isLUB
#print axioms certificate_unbounded

end Kunisky
