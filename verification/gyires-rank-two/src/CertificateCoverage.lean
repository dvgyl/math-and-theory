module

public import CertificatePolynomials

@[expose] public section

namespace MathAndTheory.Gyires.RankTwo.Certificate

def profiles (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap (fun a => (List.range (n-a)).map (fun m => (a, m+1)))

def profilePairCheck (n : ℕ) (p q : ℕ × ℕ) : Bool :=
  if max p.1 q.1 < min (p.1+p.2) (q.1+q.2) then
    SparsePolynomial.coeffsNonneg
      (Hpoly n p.1 p.2 q.1 q.2 (max p.1 q.1) (min (p.1+p.2) (q.1+q.2)))
  else true

def allProfileChecks (n : ℕ) : Bool :=
  (profiles n).all (fun p => (profiles n).all (profilePairCheck n p))

theorem mem_profiles (n a m : ℕ) :
    (a, m) ∈ profiles n ↔ 0 < m ∧ a+m ≤ n := by
  simp only [profiles, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha', k, hk, heq⟩
    rcases heq with ⟨rfl, rfl⟩
    omega
  · rintro ⟨hm, ham⟩
    refine ⟨a, by omega, m-1, by omega, rfl, ?_⟩
    omega

theorem profile_check_of_all (n a m c l : ℕ) (hm : 0 < m) (ham : a+m ≤ n)
    (hl : 0 < l) (hcl : c+l ≤ n)
    (hoverlap : max a c < min (a+m) (c+l))
    (hcheck : allProfileChecks n = true) :
    SparsePolynomial.coeffsNonneg (Hpoly n a m c l (max a c) (min (a+m) (c+l))) = true := by
  have hp : (a, m) ∈ profiles n := (mem_profiles n a m).mpr ⟨hm, ham⟩
  have hq : (c, l) ∈ profiles n := (mem_profiles n c l).mpr ⟨hl, hcl⟩
  have hrow := List.all_eq_true.mp hcheck (a, m) hp
  have hpair := List.all_eq_true.mp hrow (c, l) hq
  simpa only [profilePairCheck, hoverlap, ite_true] using hpair

end MathAndTheory.Gyires.RankTwo.Certificate
