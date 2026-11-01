import BergeBroom.Exceptional
import BergeBroom.Arithmetic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Berge
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- An exact minimum: both an actual saturated witness and the universal lower bound. -/
def IsSaturationNumber (a r n m : ℕ) : Prop :=
  (∃ H : UniformHypergraph (Fin n) r, Saturated a H ∧ H.edges.card=m) ∧
    ∀ H : UniformHypergraph (Fin n) r, Saturated a H → m≤H.edges.card

theorem saturated_lower_bound {a s : ℕ} (ha : 3≤a) (hs : 2≤s)
    (H : UniformHypergraph V (s+1)) (hSat : Saturated a H)
    (hn : s*a+1≤Fintype.card V) :
    upperValue a s (Fintype.card V) ≤ H.edges.card := by
  have hr : 3≤s+1 := by omega
  have hm := component_mass_bound H (by omega)
  have ht := largeTree_mass_bound H ha hr hSat
  obtain ⟨he,hz,hdisj,hz'⟩ := saturated_exceptional_component_budgets H ha hr hSat
  have hsmall : singleComponentCount H+zeroComponentCount H≤s := by
    rcases hdisj with h | h <;> omega
  have hsmall' : 0<largeTreeCount H → singleComponentCount H+zeroComponentCount H≤s-1 := by
    intro hlarge
    have hzz := hz' hlarge
    rcases hdisj with h | h <;> omega
  apply counting_lower_arithmetic ha hs hn
  · simpa only [Nat.add_sub_cancel] using hm
  · simpa only [Nat.add_sub_cancel] using ht
  · exact hsmall
  · exact hsmall'

/-- The central exact saturation theorem for every uniformity at least three. -/
theorem exact_saturation {a s n : ℕ} (ha : 3≤a) (hs : 2≤s)
    (hn : s*a+1≤n) :
    IsSaturationNumber a (s+1) n (upperValue a s n) := by
  constructor
  · exact exists_saturated_upper (by omega) hs hn
  · intro H hSat
    simpa using saturated_lower_bound ha hs H hSat (by simpa using hn)

theorem exact_saturation_uniform {a r n : ℕ} (ha : 3≤a) (hr : 3≤r)
    (hn : (r-1)*a+1≤n) :
    IsSaturationNumber a r n
      (a*(n/((r-1)*a+1))+(n%((r-1)*a+1))/(r-1)) := by
  have hh : r-1+1=r := by omega
  simpa only [hh,upperValue] using exact_saturation ha (by omega : 2≤r-1) hn

theorem exact_saturation_three {a n : ℕ} (ha : 3≤a) (hn : 2*a+1≤n) :
    IsSaturationNumber a 3 n (a*(n/(2*a+1))+(n%(2*a+1))/2) := by
  simpa only [upperValue] using exact_saturation ha (by omega : 2≤2) hn

end Berge
