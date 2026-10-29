# A pure-state matched-basis information family with an unbounded ratio

**Autonomous AI research disclosure.** This work is fully autonomous agentic research. Automated systems produced the mathematical arguments and manuscript preparation. Dev D. Goyal is responsible for publication. No expert validation or peer review is claimed.

This conventional companion proves an all-prime extension of the five-dimensional construction. The theorem fixes the measurement family and all optimization quantifiers. Historical novelty and correspondence with an external ECQC statement remain unverified. **The Lean package covers dimension five only.**

## The literal measurement model and the theorem

Let p be a prime with p≡1 (mod4). Let F_p be the field with p elements, choose t∈F_p with t²=−1, and let ω=exp(2πi/p). Exponents of ω are interpreted modulo p. In the p-dimensional computational basis {|x⟩:x∈F_p}, define

|b_(a,k)⟩=p^(−1/2) Σ_(x∈F_p) ω^(a x²+kx)|x⟩,
for a,k∈F_p.

Let B_a={|b_(a,k)⟩:k∈F_p}, and let B_∞ be the computational basis. Both parties use the identical physical basis B_b in setting b∈F_p∪{∞}. Bob does not replace it by a separately conjugated family. Define the normalized pure state

|Ψ_t⟩=p^(−1/2) Σ_(x∈F_p)|x,t x⟩,
ρ_t=|Ψ_t⟩⟨Ψ_t|.

For a setting b, let P_b(i,j) be the actual Born probability for the corresponding two basis outcomes, and let I_cl(P_b) be their classical mutual information. For the fixed collection of p+1 settings define the score

C_p(ρ_t)=min_{S⊆F_p∪{∞}, |S|=p} Σ_(b∈S) I_cl(P_b).

Let I_q(ρ_t)=S(ρ_A)+S(ρ_B)−S(ρ_t), where S is the von Neumann entropy. All logarithms use the same base greater than one; use natural logarithms by default.

**Theorem.** The displayed p+1 bases form a complete set of mutually unbiased orthonormal bases. The state ρ_t is normalized and pure, both marginals are I_p/p, and every setting has the same actual Born table

P_b(i,j)=1/p if j=t i, and P_b(i,j)=0 otherwise.

Consequently,

I_cl(P_b)=log p for every b,
C_p(ρ_t)=p log p,
I_q(ρ_t)=2 log p,
C_p(ρ_t)−I_q(ρ_t)=(p−2)log p,
C_p(ρ_t)/I_q(ρ_t)=p/2.

Such primes are arbitrarily large. Hence these ratios are unbounded for this exact fixed-family, same-basis measurement model. The assertion includes every prime p≡1 (mod4), not just the existence of a subsequence of numerical examples.

## Finite-field characters and the complete MUB calculation

For c∈F_p,

Σ_x ω^(c x)=p if c=0, and 0 if c≠0.

For c≠0, multiplication by c permutes F_p. The sum is therefore Σ_x ω^x=0, by the finite geometric-series identity and the primitivity of ω. This also proves orthogonality within each B_a, since

⟨b_(a,i)|b_(a,j)⟩=(1/p)Σ_x ω^((j−i)x)=δ_(i,j).

For distinct a,b let c=b−a≠0 and d=j−i. Put T=Σ_x ω^(c x²+d x). Its squared modulus is

|T|²=Σ_(x,y) ω^(c(x²−y²)+d(x−y))
     =Σ_(h,y) ω^(c h²+d h) ω^(2c h y).

The substitution h=x−y is a bijection on F_p². For h≠0, the coefficient 2ch is nonzero because p is odd, and the inner y-sum vanishes. For h=0 it is p. Thus |T|²=p. The squared overlap of the normalized basis vectors is |T/p|²=1/p. Every computational/quadratic overlap also has squared modulus 1/p because each displayed coordinate has modulus p^(−1/2). This proves all normalization, orthogonality and mutual-unbiasedness statements for the full p+1 settings.

This quadratic finite-field MUB construction and its character-sum argument are standard supporting mathematics. The proposed contribution of this note, if source comparison supports novelty, is the explicit parameterized pure-state score calculation and its consequence for the specified optimization model. The MUB construction itself is not claimed as new.

## The literal pure state and every Born table

Since t²=−1, t≠0, so x↦t x is a permutation. The p computational product vectors in |Ψ_t⟩ are distinct and orthonormal. Thus the vector has norm one, ρ_t is its rank-one orthogonal projector, and S(ρ_t)=0. Taking either partial trace gives I_p/p. Both marginal entropies are log p, so I_q(ρ_t)=2log p.

In the computational setting, the state formula gives probability 1/p exactly at j=t i and zero elsewhere. In a quadratic setting a, the actual amplitude for outcomes i,j is

(⟨b_(a,i)|⊗⟨b_(a,j)|)|Ψ_t⟩
 =1/(p√p) Σ_x ω^(−a x²−i x−a(t x)²−j(t x))
 =1/(p√p) Σ_x ω^(−(i+t j)x).

The second equality uses 1+t²=0. The two conjugations in the first line arise from the two bras; they do not change either party's physical measurement family. The character sum equals p precisely when i+t j=0. Since t²=−1, that condition is equivalent to j=t i. The nonzero amplitude is exactly 1/√p. Squaring its modulus proves the asserted probability table at every one of the p quadratic settings as well as the computational setting.

Each table has exactly p nonzero entries, all equal to 1/p. Its two marginals are uniform because i↦t i is bijective. The marginal Shannon entropies and the joint Shannon entropy are all log p, with 0log0 defined as zero. Therefore its mutual information is log p. Every p-element subset of the p+1 settings has exactly the same score p log p. This proves the minimum over all allowed selections, not only one selection or an average. Subtracting and dividing by the positive quantum mutual information gives the theorem's exact excess and ratio. Since p≥5, the excess is strictly positive. Conversion from natural units to bits multiplies every entropy and score by the same positive factor 1/log2.

For p=5 and t=2, the state is exactly (|00⟩+|12⟩+|24⟩+|31⟩+|43⟩)/√5. Thus the five-dimensional example is a literal member of this family, with the same quadratic-basis and Born-table conventions.

## Existence of t and unbounded dimensions

The group F_p^× is cyclic of order p−1. Choose a generator g. Because4 divides p−1, set t=g^((p−1)/4). Then t²=g^((p−1)/2) is a nonidentity element of order two. Over an odd field, the only roots of X²−1 are1 and−1, so t²=−1. This proves the existence used by every instance of the construction.

For completeness, infinitely many primes are1 modulo4 by an elementary argument. If p_1,…,p_k were all such primes, put N=2p_1⋯p_k, allowing the empty product. The odd integer N²+1>1 has an odd prime divisor q. Modulo q, N²=−1 and N≠0. Fermat's theorem gives

1=N^(q−1)=(−1)^((q−1)/2).

Since q is odd, this forces q≡1 (mod4). But none of the listed primes divides N²+1, because each divides N. This is a contradiction. Hence the available primes, dimensions, and ratios p/2 are unbounded. These standard number-theoretic facts are supporting results, not new claims of the project.

## Source, formal and publication boundary

The theorem proves exactly the score C_p defined above for a fixed complete quadratic MUB family, identical local basis vectors, and minimization over p-element subsets of that collection. If an external source permits independent optimization over different MUB collections, applies local basis changes before the optimization, uses conjugated local settings, has a dimension restriction, or defines a different score, this theorem alone does not establish a refutation of that different statement. The exact source quantifiers must be checked. The motivating ECQC proposal is attributed to Iqbal, and prior mixed-state counterexamples to Wang–Wang–Chen. The precise Iqbal and later Wang–Wang–Chen/Qian comparisons remain unverified; reference metadata is in [references.bib](manuscript/references.bib).

No priority claim is made. In particular, a parameterized version may already exist in the current pure-state or finite-field literature. The five-dimensional source package has a complete checked Lean development, but that does not formally prove this all-prime theorem. The character sums, arbitrary prime fields, MUB construction, entropy/score bridge and unbounded-ratio endpoint still need a faithful general Lean development. This note gives a conventional all-prime proof. It makes no priority claim and no claim that the all-prime theorem is formally verified.
