import BookInnerSimplicity
import BookRealRootCount

noncomputable section
namespace BookCompletion
open Set

theorem book_origin_isRoot (n : ℕ) (hn : 1 ≤ n) : (realPolynomial n).IsRoot 0 := by
  apply (Polynomial.rootMultiplicity_pos (actual_polynomial_ne_zero n)).mp
  rw [realPolynomial_origin_multiplicity n hn]
  norm_num

theorem book_even_real_roots (n : ℕ) (hn : 2 ≤ n) (he : Even n) :
    ∃ a ∈ Ioo (-3) (-2), ∃ b ∈ Ioo (-(1/2)) 0,
      (∀ x : ℝ, (realPolynomial n).IsRoot x ↔ x = 0 ∨ x = a ∨ x = b) ∧
      (realPolynomial n).rootMultiplicity a = 1 ∧
      (realPolynomial n).rootMultiplicity b = 1 ∧
      (complexPolynomial n).rootMultiplicity (a:ℂ) = 1 ∧
      (complexPolynomial n).rootMultiplicity (b:ℂ) = 1 := by
  obtain ⟨a,ha3,ha2,hra,hua⟩ := outer_even_actual_root n hn he
  obtain ⟨t,ht,hFt,hut⟩ := innerF_exists_unique n hn
  let b := -t
  have hb : b ∈ Ioo (-(1/2)) 0 := by dsimp [b]; constructor <;> linarith [ht.1,ht.2]
  have hrb : (realPolynomial n).IsRoot b := (inner_even_root_iff n (by omega) he ht).mpr hFt
  have hclass : ∀ x : ℝ, (realPolynomial n).IsRoot x ↔ x = 0 ∨ x = a ∨ x = b := by
    intro x
    constructor
    · intro hr
      by_cases hx : x = 0
      · exact Or.inl hx
      · rcases even_nonzero_root_regions n hn he hx hr with hout | hint
        · exact Or.inr (Or.inl (hua x hout hr))
        · right
          right
          have hs : -x ∈ Ioo 0 (1/2) := ⟨by linarith [hint.2],by linarith [hint.1]⟩
          have hsr : (realPolynomial n).IsRoot (-(-x)) := by simpa only [neg_neg] using hr
          have hF := (inner_even_root_iff n (by omega) he hs).mp hsr
          have heq := (hut (-x) hs).mp hF
          dsimp [b]
          linarith
    · rintro (rfl | rfl | rfl)
      · exact book_origin_isRoot n (by omega)
      · exact hra
      · exact hrb
  have hma : (realPolynomial n).rootMultiplicity a = 1 := by
    have h := outer_even_actual_simple n hn he (t:=-a) (by linarith) (by simpa only [neg_neg] using hra)
    simpa only [neg_neg] using h
  have hmb : (realPolynomial n).rootMultiplicity b = 1 := inner_even_actual_simple n hn he ht hrb
  exact ⟨a,⟨ha3,ha2⟩,b,hb,hclass,hma,hmb,complex_simple_of_real_simple n a hma,
    complex_simple_of_real_simple n b hmb⟩

theorem book_odd_real_roots (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) :
    ∃ a ∈ Ioo (-(1/2)) 0, ∃ b ∈ Ioo (-(1/2)) 0, a ≠ b ∧
      (∀ x : ℝ, (realPolynomial n).IsRoot x ↔ x = 0 ∨ x = a ∨ x = b) ∧
      (realPolynomial n).rootMultiplicity a = 1 ∧
      (realPolynomial n).rootMultiplicity b = 1 ∧
      (complexPolynomial n).rootMultiplicity (a:ℂ) = 1 ∧
      (complexPolynomial n).rootMultiplicity (b:ℂ) = 1 := by
  obtain ⟨l,hl,r,hr,hlr,hGl,hGr⟩ := innerG_exists_two n hn ho
  let a := -l
  let b := -r
  have ha : a ∈ Ioo (-(1/2)) 0 := by dsimp [a]; constructor <;> linarith [hl.1,hl.2]
  have hb : b ∈ Ioo (-(1/2)) 0 := by dsimp [b]; constructor <;> linarith [hr.1,hr.2]
  have hab : a ≠ b := by dsimp [a,b]; linarith
  have hra : (realPolynomial n).IsRoot a := (inner_odd_root_iff n (by omega) ho hl).mpr hGl
  have hrb : (realPolynomial n).IsRoot b := (inner_odd_root_iff n (by omega) ho hr).mpr hGr
  have hclass : ∀ x : ℝ, (realPolynomial n).IsRoot x ↔ x = 0 ∨ x = a ∨ x = b := by
    intro x
    constructor
    · intro hz
      by_cases hx : x = 0
      · exact Or.inl hx
      · right
        have hint := odd_nonzero_real_root_interval n (by omega) ho hx hz
        have hs : -x ∈ Ioo 0 (1/2) := ⟨by linarith [hint.2],by linarith [hint.1]⟩
        have hsr : (realPolynomial n).IsRoot (-(-x)) := by simpa only [neg_neg] using hz
        have hG := (inner_odd_root_iff n (by omega) ho hs).mp hsr
        rcases (innerG_zero_classification hn hl hr hlr hGl hGr hs).mp hG with hc | hc
        · left
          dsimp [a]
          linarith
        · right
          dsimp [b]
          linarith
    · rintro (rfl | rfl | rfl)
      · exact book_origin_isRoot n (by omega)
      · exact hra
      · exact hrb
  have hma : (realPolynomial n).rootMultiplicity a = 1 := inner_odd_actual_simple n hn ho hl hra
  have hmb : (realPolynomial n).rootMultiplicity b = 1 := inner_odd_actual_simple n hn ho hr hrb
  exact ⟨a,ha,b,hb,hab,hclass,hma,hmb,complex_simple_of_real_simple n a hma,
    complex_simple_of_real_simple n b hmb⟩

theorem book_real_roots_card (n : ℕ) (hn : 2 ≤ n) : (realPolynomial n).roots.card = 4 := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨a,ha,b,hb,hclass,hma,hmb,_,_⟩ := book_even_real_roots n hn he
    exact real_roots_card_four_of_classification n (by omega)
      (by linarith [ha.2]) (by linarith [hb.2]) (by linarith [ha.2,hb.1]) hclass hma hmb
  · have hn3 : 3 ≤ n := by rcases ho with ⟨k,hk⟩; omega
    obtain ⟨a,ha,b,hb,hab,hclass,hma,hmb,_,_⟩ := book_odd_real_roots n hn3 ho
    exact real_roots_card_four_of_classification n (by omega)
      (by linarith [ha.2]) (by linarith [hb.2]) hab hclass hma hmb

#print axioms book_origin_isRoot
#print axioms book_even_real_roots
#print axioms book_odd_real_roots
#print axioms book_real_roots_card
end BookCompletion
