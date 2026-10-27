import PermEntropy.Ranking
import PermEntropy.Slice

noncomputable section
open scoped BigOperators
namespace PermEntropy
namespace Ranking
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem wordCount_membershipWord (r : Ranking V) (s : Finset V) :
    wordCount (r.membershipWord s) = s.card := by
  unfold wordCount membershipWord
  have h := (Equiv.ofBijective r.enum r.enum_bijective).sum_comp
    (fun v : V => if v ∈ s then (1 : ℕ) else 0)
  simpa using h

end Ranking
end PermEntropy
