import ShortChain.Data

/-!
# Endpoints

The chamber list is complete for short-chain sizes one to four, and every
certified chamber polynomial is nonnegative on the closed orthant with the
quantitative linear lower bound.
-/

namespace ShortChain

/-- Every endpoint word has `a` letters of each kind. -/
theorem chambers_word_length : ∀ c ∈ chambers, c.word.length = 2 * c.a := by
  decide +kernel

/-- For each size `a ≤ 4` the chamber words are exactly the Dyck words. -/
theorem chambers_complete :
    ∀ a ∈ [1, 2, 3, 4], ((chambers.filter (fun c => c.a = a)).map Chamber.word).Perm
      (dyckWords a) := by
  decide +kernel

/-- No chamber has a short chain of another size. -/
theorem chambers_sizes : ∀ c ∈ chambers, c.a ∈ [1, 2, 3, 4] := by
  decide +kernel

/-- **Certified chambers.**  For every chamber with a short chain of size at
most four, the certificate polynomial `F_{a,w}` is nonnegative at every gap
vector with nonnegative entries in any linearly ordered field, and it is at
least `(a-1)!` times the sum of the gaps whose elements are comparable with
some element of the short chain. -/
theorem certified_chambers {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (c : Chamber) (hc : c ∈ chambers) (x : ℕ → R) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ c.F x ∧ ((c.a - 1).factorial : R) * ((comparableSegments c).map x).sum ≤ c.F x := by
  have hv : c.valid = true := List.all_eq_true.mp chambers_valid c hc
  have hl := chambers_word_length c hc
  exact ⟨c.nonneg hv hl x hx, c.lower_bound hv hl x hx⟩

end ShortChain
