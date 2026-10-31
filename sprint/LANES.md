# LANES: 15 lane cards (paste ASTRA_PREAMBLE.md, then one card, into a fresh Astra Pro session)

Repo base: `https://github.com/dvgyl/math-and-theory/tree/main/`

Every card has the same parts:
- **Why this lane**: why it is ripe, and what the moat is.
- **R1–R5**: the ladder. Every rung is a standalone theorem.
- **Framework**: the lane-specific search mechanism.
- **Evaluator**: what Claude will run blind.
- **Crowding watch**: where a collision is most likely.
- **First moves**: what to do first.

Frontier statements about the repo's own results are quoted from its README. Any external fact a card cites must be verified by the Scout at S0 before it is relied on.

---

## L01 — Exact universal multiplier step τ* for two-block ADMM

**Why this lane.** The repo proves convergence for every 0 < τ ≤ 1.886 and a nonconstant periodic orbit for every τ ≥ 1.8868954… on fixed compact polytopes in R¹²⁸. So τ* lies in an interval of width below 0.0009. Nobody else stands at this boundary, and the convergence certificates and orbit construction already exist in Lean.
Files: `papers/mathematics/admm-multiplier-step/`, `papers/mathematics/admm-counterexample/`.

- **R1:** determine τ* exactly. Prove convergence for all τ < τ* and give a nonconvergent instance for all τ > τ*, with τ* given as an algebraic number with its minimal polynomial, or as an explicit root of an explicit equation.
- **R2:** the exact threshold τ*(d) for problems in fixed low dimension d (start with d = 1, 2). This is a standalone theorem: "In R^d the multiplier-step threshold is …".
- **R3:** shrink the interval by at least 10×, with certificates on both sides: a rational Lyapunov/PEP certificate at τ_lo and an exact orbit at τ_hi.
- **R4:** a nonconvergent instance in dimension ≪ 128 (target ≤ 8) for some τ < 1.8868954…. This lowers the published upper bound *and* compresses the witness.
- **R5:** a rational, τ-parametrized convergence certificate family, plus a public exact-arithmetic orbit verifier.

**Framework: two-sided squeeze with exact reconstruction.**
1. Lower side: search for Lyapunov/PEP-style SDP certificates of the multiplier-relaxed iteration at increasing τ, at high precision, then round to rationals and verify exactly.
2. Upper side: search for structured periodic orbits (polytopes with few facets, symmetric orbits) at decreasing τ.
3. Bisect. Keep a ledger of (τ_lo certified, τ_hi certified).
4. When the gap is below 10⁻⁶, run PSLQ/LLL on the bracket endpoints and on the extremal-instance parameters to guess τ*, then prove it.
The key heuristic: the *extremal orbit structure* (period, active facets) at τ_hi usually reveals the algebraic equation that defines τ*.

**Evaluator:** exact rational iteration of ADMM on the supplied polytope instance, confirming periodicity, and exact verification of the PSD/LMI certificate with rational entries (LDLᵀ over Q).

**Crowding watch:** the PEP community (Taylor, Hendrickx, Glineur, Goujaud, Ryu, Rotaru). Search for "ADMM" with "dual step" or "Glowinski" and "golden ratio" since 2025.

**First moves:** reproduce both repo certificates. Identify which inequality in the 1.886 proof is slack. Record the period and active-set pattern of the 1.8868954 orbit.

---

## L02 — Nesterov flows and iterates: the finite-dimensional range 2 < r < 3

**Why this lane.** The repo proves boundedness for r ≥ 3, sharpness on ℓ² for every 0 < r < 3 via block sums of smoothed valleys, and an explicit planar escape for 0 < r ≤ 2. The finite-dimensional range 2 < r < 3 is open. Only this repo holds the block construction.
Files: `papers/mathematics/nesterov-subcritical/`.

- **R1:** settle 2 < r < 3 in finite dimension. Either every trajectory is bounded in every R^d, or there is an explicit escape in some R^d for every r < 3. The same for the discrete iteration.
- **R2:** the exact planar threshold r₂* ∈ [2, 3]: escape in R² for r < r₂*, and boundedness in R² for r > r₂*.
- **R3:** a threshold function r(d): escape in R^d for every r < r(d), with explicit r(d) → 3 as d → ∞ (truncate the ℓ² construction to d blocks and quantify). This is standalone: "d blocks suffice for damping up to r(d)".
- **R4:** boundedness for 2 < r < 3 within a natural restricted class (quadratic-plus-indicator, separable, radial, or piecewise-quadratic with k pieces). This is either a proof or a counterexample inside the class.
- **R5:** the discrete-iteration analogue of whichever of R2–R4 was reached.

**Framework: dimension descent.** Start from the ℓ² block sum. Measure how much "escape" each block contributes as a function of r. Find the minimum number of blocks that gives escape at a given r, which yields R3 directly. In parallel, search Lyapunov-type energies in R² for r slightly above 2 (an SOS search in (X, X′, t) with polynomial weights). Whichever side gets stuck tells you which way R2 goes.

**Evaluator:** for escape claims, a rigorous interval-ODE enclosure (validated numerics with an explicit error bound) or an exact discrete-iteration computation. For boundedness claims, a symbolic check of the Lyapunov derivative.

**Crowding watch:** Attouch, Chbani, Peypouquet and Riahi; Su–Boyd–Candès follow-ups; "vanishing damping" with "subcritical" and "r < 3".

**First moves:** quantify the escape rate per block of the repo's construction. Compute numerically the best planar escape at r = 2.1, 2.3, 2.5.

---

## L03 — Unconditional Keller–Klein: eliminate the unrefereed dependency

**Why this lane.** The repo proves the small-coefficient upper half for |vᵢ| ≤ 7/100, and this implies the full conjecture *only together with* Ivanisvili's computer-assisted Theorems 1.1 and 10.9, which are unrefereed. An independent, verified replacement of those dependencies would give the full conjecture unconditionally. That is the highest-significance target in the portfolio. Nathan Keller has expressed interest in reviewing.
Files: `papers/mathematics/keller-klein/`.

- **R1:** the full Keller–Klein conjecture with a self-contained proof: every computational part rigorously verified (interval arithmetic with two independent implementations, or Lean).
- **R2:** extend the small-coefficient theorem from a ≤ 7/100 to the largest a₀ the method allows, together with a precise map of what remains for Ivanisvili's part. This is standalone: "Keller–Klein holds for all a ≤ a₀".
- **R3:** an independent rigorous re-verification of Ivanisvili's Theorem 1.1 or 10.9, the kind of independent check that computer-assisted proofs get published for.
- **R4:** the matching lower-half bound in the same coefficient regime, if not already covered. Or else a sharp counterexample showing where a natural strengthening (e.g. replacing Φ(a) − 1/2 by a smaller function) fails.
- **R5:** a Lean library for the Prawitz-smoothing / characteristic-function machinery used here, so that future Berry–Esseen-type bounds can be formalized.

**Framework: dependency elimination.** Build the proof dependency graph of the full conjecture: repo theorem + Ivanisvili 1.1 + 10.9. For each external node, classify it as analytic (re-prove), computational (re-verify) or replaceable (substitute your Prawitz approach). Push the analytic range of your method (R2) first; every bit of extra range shrinks what R3 must verify.

**Evaluator:** an interval-arithmetic script (mpmath `iv` or Arb/flint) for every numerical inequality, run in two implementations, plus the Lean build.

**Crowding watch:** high-value target. Ivanisvili himself, Keller–Klein follow-ups, and "Tomaszewski" / "Rademacher sums" / "Berry–Esseen" since 2025. Do the R-3 poser email early, to Keller (interest already expressed) and possibly Ivanisvili.

**First moves:** get Ivanisvili's paper. List exactly which statements 1.1 and 10.9 assert and which coefficient ranges they cover. Find the binding constraint in the repo's 7/100 proof.

---

## L04 — Operator-splitting orbit factory (Chambolle–Pock, then siblings)

**Why this lane.** The repo already has exact periodic-orbit technology for ADMM (period five, and the R¹²⁸ family) and Chambolle–Pock (cycles for every κ > 2 at small θ, with 21 Lean modules). Many splitting methods have published sufficient step-size conditions whose sharpness is unknown. This is a *factory*: the same verifier yields a theorem per method.
Files: `papers/mathematics/chambolle-pock-cycles/`, `admm-counterexample/`, `admm-multiplier-step/`.

- **R1:** the exact universal threshold curve c(θ) for unmodified Chambolle–Pock on an interval θ ∈ (0, θ₀). The repo gives limsup c(θ) ≤ 2 as θ ↓ 0.
- **R2:** for at least two *other* methods, an exact periodic orbit just beyond the best published sufficient condition, proving that condition sharp. Or a first counterexample beyond it. Candidates for the Scout to verify: Douglas–Rachford with relaxation, Davis–Yin three-operator splitting, linearized/preconditioned ADMM, golden-ratio primal-dual (Malitsky), PDHG "larger step" variants, optimistic gradient / extragradient on convex–concave problems.
- **R3:** minimal-dimension (R² or R³) cycles for the methods in R2, each one a separate short theorem.
- **R4:** a no-go theorem: no dimension-free sufficient condition beyond c for method M.
- **R5:** an open-source exact-arithmetic orbit verifier and catalogue (method → threshold → witness).

**Framework: exact periodic-orbit factory.** Parametrize instances as small polytopes with rational vertices (indicator functions plus linear terms). An orbit of period p is a solution of a piecewise-linear fixed-point system, so for each active-set pattern solve a linear system exactly and check consistency. Search active-set patterns by symmetry. Each success is one exact witness, checkable in milliseconds.

**Evaluator:** exact rational iteration over p steps returning to the start, plus a nonconvergence check (the orbit is not a fixed point).

**Crowding watch:** medium. "Step size", "sharp", "counterexample", "cycle" together with the method name, since 2024. PEP groups publish sharpness results.

**First moves:** the Scout tabulates published sufficient conditions and known sharpness for 6–8 methods and picks the 2 with the largest unexplained gap.

---

## L05 — Upper PPT entanglement-cost hierarchy in fixed dimension

**Why this lane.** The repo proves noncollapse of the Lami–Mele–Regula upper hierarchy, but its witnesses have local dimension 2^((2q+4)4^q). "Noncollapse in one fixed dimension is open" (UNFINISHED.md). Only this repo holds the strict-separation SDP certificates.
Files: `papers/physics/upper-ppt-hierarchy/`.

- **R1:** settle the fixed-dimension question. Either for some fixed d the hierarchy is strict at infinitely many levels on d × d states, or for each d some finite level is exact on all d × d states.
- **R2:** witnesses with dimension polynomial, or single-exponential, in q. This is a standalone dimension-compression theorem.
- **R3:** exact collapse levels for natural families: two-qubit states, Werner, isotropic, Bell-diagonal in d = 2, 3. Prove level 1 or 2 is exact there (or not). Each family is its own theorem.
- **R4:** an explicit smallest-dimension state with κ₂ < κ₁ (target d ≤ 8), with a rational SDP certificate.
- **R5:** a rational-certificate library for these SDPs.

**Framework: witness compression plus collapse classification.** Run the SDP hierarchy numerically on symmetric families (Werner, isotropic, Bell-diagonal, group-covariant), where symmetry reduction makes the SDPs small. Plot κ_q against q and d. Families with an exactly flat κ_q give R3 collapse theorems through dual certificates. Families with a gap at small d give R4. A gap pattern that grows with d suggests the R1 direction.

**Evaluator:** exact rational verification of the primal and dual feasibility certificates (PSD via exact LDLᵀ) and of the objective gap.

**Crowding watch:** low to medium. Lami, Regula, Mele, Brinster, Wang–Wilde.

**First moves:** reproduce the q = 1 witness. Compute κ₁ and κ₂ on two-qubit and two-qutrit Werner/isotropic families.

---

## L06 — Nonnegative rank of tensor products: from counterexample to law

**Why this lane.** The repo disproved rank₊(M ⊗ M) ≥ rank₊(M)·rank(M) (Vandaele–Gillis–Glineur–Tuyttens) with an order-(k + 11) family and additive violation growing in k. The smallest witness factorizes at width 109 against the conjectured 110. arXiv:2607.27037 restates the conjecture and has restricted positive results (Theorems 1.3–1.4). The obvious next questions are fresh and in your hands.
Files: `papers/mathematics/nonnegative-rank-kronecker/`, `research/active/MAT-C-NNR-Kronecker.md`.

- **R1:** the correct law. Either a provable lower bound on rank₊(M ⊗ M) in terms of rank₊(M) and rank(M) that the repo family shows to be tight up to lower order, or a family where the ratio rank₊(M ⊗ M) / (rank₊(M)·rank(M)) is bounded away from 1.
- **R2:** prove the conjectured inequality on the largest natural class that the counterexamples avoid (e.g. irreducible or strictly positive matrices, or a structural condition from 2607.27037), extending its Theorems 1.3–1.4.
- **R3:** the exact rank₊(C ⊗ C) for the 11 × 11 witness: a lower-bound certificate at 109, or a factorization at 108.
- **R4:** the smallest order of a counterexample, or a proof that none exists below order n₀ within a structured class.
- **R5:** an exact-factorization search tool and a database of certified small cases.

**Framework: counterexample to law.** Fit the violation (t − 5 against order) and find which part of the construction (the J + εI block) drives it. Vary that part in a parametric family and maximize the violation. A lower bound needs fooling-set, rectangle-cover or hyperplane-separation certificates; compute these on the witnesses to see how close the lower bounds come.

**Evaluator:** exact rational factorization check (entrywise ≥ 0, product equals M ⊗ M) and exact verification of the lower-bound certificate.

**Crowding watch:** the 2607.27037 authors, Gillis's group, "nonnegative rank" with "Kronecker" or "tensor product" since 2026-07.

**First moves:** read 2607.27037's open questions. Compute standard lower bounds for C ⊗ C at t = 6.

---

## L07 — Gyires's permanent inequality: uniform rank-two and general order seven

**Why this lane.** The repo proves Gyires's inequality (Gyires 1978; Cheon–Wanless 2005, Conjecture 20) for many structured classes: rank ≤ 2 doubly stochastic matrices through order 15 (Lean for orders 2–8), nonnegative circulants of orders 5–7, and others. Nobody else holds these certificate families.
Files: `papers/mathematics/gyires/`, `lean/docs/mathematics/gyires.md`.

- **R1:** the rank-at-most-two case for **all** orders, by one uniform proof.
- **R2:** nonnegative circulants of all orders, or of all prime orders.
- **R3:** rank-three doubly stochastic matrices of orders ≤ 6, by exact certificates.
- **R4:** a counterexample to a natural strengthening (sharper constant, a different matrix class), or an exact characterization of the equality cases.
- **R5:** complete the Lean proofs for order-7 circulants and rank-two orders 9–15 (UNFINISHED.md). This is infrastructure, not a discovery.

**Framework: certificate-family induction.** Line up the order-n certificates for n = 2…15 side by side, look for an explicit n-parametrized form (a polynomial identity in n, a recurrence in the SOS multipliers), and then prove that form for all n. The unexplained regularity across orders is the signal.

**Evaluator:** exact polynomial-identity checks for each n, and the Lean build.

**Crowding watch:** low, though "permanent" + "doubly stochastic" conjectures are a standard AI-target genre. Check formal-conjectures and the Omega Institute's list.

**First moves:** extract the rank-two certificates for n = 2–15 into one table and look for patterns.

---

## L08 — Spectral tiles in F₂⁹ (reserve, high collision)

**Why this lane.** The repo has a 64-point spectral tile in F₂⁹ with no periodic complement and a full classification of its 512 complements. "Whether every spectral 64-point subset of F₂⁹ tiles is open." Ferguson–Iosevich proved Fuglede in F₂⁸ and are certainly working on dimension 9.
Files: `papers/mathematics/binary-spectral-tile/`.

- **R1:** every spectral 64-point subset of F₂⁹ tiles, or an explicit spectral non-tile.
- **R2:** the same for all spectral subsets of F₂⁹ of size ≤ 32.
- **R3:** the classification of spectral 64-subsets of F₂⁹ up to affine equivalence (a count, with representatives).
- **R4:** a spectral set in F₂^10 with no tiling complement. Any spectral non-tile in F₂ⁿ would be a major result.
- **R5:** an isomorph-free enumeration tool with certificates.

**Framework: isomorph-free exhaustive classification.** Spectral sets correspond to Hadamard-type orthogonality conditions on the dual group. Enumerate the spectra up to GL(9, 2) ⋉ F₂⁹ using canonical forms, then test tiling for each class with a SAT exact-cover search.

**Evaluator:** exact checks of spectrality (character sums) and tiling (exact cover), each on the supplied set.

**Crowding watch:** **high.** Recommended: email Ferguson (you already correspond) and offer to coordinate rather than race. Run this lane only if it emits a `WITNESS` by G1.

---

## L09 — Conditional independence, polymatroids and the entropy region

**Why this lane.** The repo answered Boege's Question 4.18 (structural ≠ numerical selfadhesivity). This is a small community (Matúš, Studený, Boege, Kühne, Yeung) with essentially no AI-lab presence, and every question here is decided by a **linear program**: either a Farkas certificate or an explicit polymatroid. That makes this the ideal oracle-backed lane.
Files: `papers/mathematics/structural-selfadhesivity/`.

- **R1:** answer another named open question from Boege's papers or thesis, Studený's "Probabilistic Conditional Independence Structures" open problems, or Matúš's problem lists. The Scout chooses by §2 score.
- **R2:** a complete classification of one property (selfadhesive, structurally selfadhesive, entropic-closure, Gaussian-realizable) for all CI structures on 5 variables, up to symmetry.
- **R3:** a new linear information inequality from an iterated copy lemma on 4 or 5 variables, with an exact LP certificate, that is not implied by the published lists of non-Shannon inequalities.
- **R4:** the smallest CI structure separating two published closure operators.
- **R5:** a certified database (LP certificates plus polymatroid witnesses) for 5-variable CI inference.

**Framework: LP-duality oracle.** Every candidate statement "A implies B" or "structure S has property P" is turned into an LP. A feasible point is a counterexample polymatroid (exact rational vertex); infeasibility comes with a Farkas certificate. The model's job is choosing *which* LPs to run and turning patterns in the certificates into general theorems. Run thousands of instances.

**Evaluator:** exact rational LP certificate checks (Farkas multipliers ≥ 0 and the identity holds exactly), and exact polymatroid axiom checks.

**Crowding watch:** low. Check the Boege–Kühne software ecosystem and recent arXiv cs.IT/math.CO work on "selfadhesive" and "copy lemma".

**First moves:** the Scout extracts every open question from Boege's selfadhesivity paper and the latest Matúš/Studený problem lists, then scores them.

---

## L10 — Sharp current-cumulant bounds beyond the single cycle

**Why this lane.** The repo proves −1/16 ≤ C₃/C₁ ≤ 1 for marked-edge currents on every finite bidirectional Markov ring (n ≥ 3), and has a thermal-kurtosis counterexample. Stochastic thermodynamics has many *conjectured universal sharp bounds* (thermodynamic-uncertainty-relation (TUR)-type, higher cumulants), a small math community, and exact matrix-derivative verifiers.
Files: `papers/physics/unicyclic-skewness/`, `papers/physics/thermal-kurtosis-counterexample/`.

- **R1:** sharp universal bounds on C₃/C₁ (or C₄/C₂) for **all finite networks**, or a proof that no universal bound exists beyond the unicyclic case.
- **R2:** the exact n-dependence of the unicyclic bounds, C₃/C₁ ∈ [ℓ(n), u(n)], with attainment.
- **R3:** exact sharp bounds for all networks with ≤ 4 states (finite topology classes), each with a certificate.
- **R4:** an explicit network violating a published conjectured higher-cumulant bound. The Scout searches 2023–2026 papers for such conjectures.
- **R5:** an exact symbolic toolkit for full counting statistics: the cumulant-generating-function derivatives as rational functions of the rates.

**Framework: extremizer-first sharp constants.** Do not start with proofs. Numerically optimize the cumulant ratio over rates for each topology, and watch where the optimum goes (a boundary, a limit of rates, or an interior point). Reconstruct the extremal family exactly. Only then prove the bound, using the extremizer to choose the certificate.

**Evaluator:** exact rational evaluation of the cumulants of the supplied rate matrices, a check of the bound, and verification of the limit sequence.

**Crowding watch: HIGH (upgraded after the local crowding check).**
- The Omega Institute has `ptaszynski-2022-unicyclic-skewness-minimum` (issue #22468). That is the same minimum-skewness bound as the repo's unicyclic result: g(N) → −1/16.
- Omega has also refuted the Meer–Weeks kurtosis limit.
- Ptaszyński 2022 (arXiv:2204.08421) conjectures min/max topologies for S, K, S+K, S−K and S×K, so the **whole paper counts as opened** under the source-paper rule.
- **Do not target any Ptaszyński 2022 conjecture.** Retarget R1 and R4 to *multicyclic* networks and to sources Omega has not opened (run `crowd.py --id <id>` on each candidate). Also check Barato–Seifert, Pietzonka, Dechant, Horowitz–Gingrich and Van Vu–Saito, plus "skewness", "higher cumulants" and "TUR" since 2025.
- This lane moves to the reserves.

**First moves:** extend the repo's unicyclic computation to two-cycle (theta-graph) networks numerically.

---

## L11 — Quantitative replacements for nonexistent AME states

**Why this lane.** The Higuchi–Sudbery bound (collided, but your infrastructure exists) is the n = 4 case of a general question. Qubit AME(n, k) states exist only in specific cases (the Scout must verify: AME(n, 2) is believed to exist only for n = 2, 3, 5, 6, with nonexistence for n = 4 by Higuchi–Sudbery, n = 7 by Huber–Gühne–Siewert 2017 and n ≥ 8 by Scott 2004). When no AME state exists, the *maximum average ⌊n/2⌋-body marginal entropy* is a natural sharp constant, and is largely uncomputed.
Files: `papers/physics/higuchi-sudbery/`, `fidelity-three-state/`, `steering-bounds/`.

- **R1:** the exact maximum of the average 3-qubit marginal entropy (von Neumann or Rényi-2) over pure 7-qubit states, with a certificate.
- **R2:** the same maximum over **stabilizer** 7-qubit states. This is finite: enumerate up to local-Clifford equivalence. A standalone exact theorem.
- **R3:** the Rényi-2 (purity) version, which is *polynomial* and therefore amenable to SOS, for n = 7 or 8.
- **R4:** a non-stabilizer state that beats every stabilizer state (or a proof that the optimum is stabilizer).
- **R5:** a certified table of optimal stabilizer values for n ≤ 9.

**Framework: stabilizer exhaustion to general bound.** Exhaust the finite stabilizer class exactly (R2). Use the best stabilizer states as starting points for local optimization over all states (R4). If the stabilizer optimum survives, attack R3 with an SOS/purity certificate built around it.

**Evaluator:** exact entropy/purity computation for stabilizer states (via the rank of the stabilizer restricted to subsets), exact SOS identity checks, and rational state verification.

**Crowding watch: medium–high.** The Omega Institute has a `higuchi-sudbery-2000-four-qubit-average-entropy-maximum` file, plus many quant-ph entropy problems, including Pauwels–Gühne 2026 and Życzkowski-group problems. The n = 4 case is taken, and Omega will plausibly look at n = 7 next. Run `crowd.py --kw "absolutely maximally|k-uniform|marginal entropy|seven.qubit"` and check live Omega issues before S1. Also check Huber, Gühne, Siewert, Rather, Życzkowski, Burchardt and Raissi, plus "maximally multipartite entangled", "k-uniform" and "AME" since 2024.

---

## L12 — Valuation theory sequels with your Lean stack

**Why this lane.** The repo proved Conjecture 4.1 of Nart–Novacoski (depth-one Artin–Schreier defect towers are composita) and has a 100-module Lean development of Mac Lane–Vaquié chains, Okutsu sequences and Hahn fields. **No one else has this formal infrastructure.** That makes this a Lean-first lane.
Files: `papers/mathematics/artin-schreier-depth/`, the NT-C entries in git history (`git show 659a267^:ACTIVE_PROBLEMS.md`).

- **R1:** a characterization of depth-two Artin–Schreier defect towers, or a general formula for the depth in terms of tower data.
- **R2:** depth bounds for towers of degree p² (or of length two), with sharp examples.
- **R3:** explicit towers of every depth n, generalizing Nart–Novacoski Section 4.
- **R4:** a counterexample to the natural extension of Conjecture 4.1 beyond the standing assumptions (non-henselian base, finite accumulation points).
- **R5:** a released Lean library for MLV chains and Okutsu depth.

**Framework: Lean-first exploration.** Use the existing formal definitions to state candidate characterizations *in Lean first*, check them on the formal examples, and let failed `decide`/`simp` attempts on concrete examples act as the counterexample search. Prose proofs come after the formal statement is stable.

**Evaluator:** the Lean build with an axiom audit, plus explicit-tower computations in a CAS where available.

**Crowding watch:** low. Nart, Novacoski, Kuhlmann, Kedlaya; the citing paper arXiv:2608.21210.

---

## L13 — Graph-polynomial conjecture lattice

**Why this lane.** The repo has ultra-log-concavity of domination sequences for powers of paths and cycles (Galvin–Zhang, Conjecture 1.8), domination-root escape, and leaf-deletion mode movement. Failed universal claims in this genre yield minimal counterexamples and refined theorems.
Files: `papers/mathematics/galvin-zhang/`, `graph-roots/`, `leaf-deletion/`, `domirank-entropy/`.

- **R1:** the unimodality of domination polynomials for a broad family (Alikhani–Peng conjecture: every domination polynomial is unimodal), or the strongest true version the lattice reaches.
- **R2:** ultra-log-concavity or log-concavity for circulants, grids P_m × P_n, or trees of bounded degree. Each family is its own theorem.
- **R3:** the remaining conjectures of Galvin–Zhang arXiv:2408.12731 beyond 1.8.
- **R4:** the smallest counterexample to the strongest refuted node in the lattice.
- **R5:** a certified enumeration of domination polynomials for all graphs up to n vertices.

**Framework: conjecture lattice.** Build a poset of statements from strongest (real-rooted) through ultra-log-concave, log-concave and unimodal to "mode located at …", crossed with graph families from all graphs down to paths. Every counterexample moves the lane down one edge. Every proof moves the neighbouring statement up. The output is the boundary of the lattice: the strongest true statements plus the smallest counterexamples.

**Evaluator:** exact enumeration of domination polynomials of the supplied graphs and coefficient-inequality checks.

**Crowding watch: medium–high.**
- The Omega Institute has Rather's book domination-root Conjecture 5.4 (issue #23025, arXiv:2604.08998). That overlaps the repo's `graph-roots` book classification.
- Omega has Zhang–Zhao DomiRank entropy (issue #13267). That overlaps the repo's `domirank-entropy`.
- Omega has Ball–Galvin–Hyry–Weingartner Question 4.6 (unimodal coefficient permutations).
- **The Galvin group's papers count as opened**, so check R3's source (arXiv:2408.12731) with `crowd.py --id 2408.12731` before starting.
- PatternBoost/RL-counterexample work also targets graph conjectures.

---

## L14 — Old-journal conjecture disproof factory

**Why this lane.** Your Kovačec and nonnegative-rank results came from conjectures with cheap exact counterexample checks. Labs scraping for targets prioritize *recent arXiv* papers. Conjectures from 1990–2015 in journals that are mainly print/journal-only (Linear Algebra Appl., ELA, Linear Multilinear Algebra, J. Inequal. Appl., Math. Inequal. Appl., Discrete Math., Ars Combin.) are less trafficked.

- **R1:** a counterexample to a named conjecture that has been open at least 10 years, cited at least 5 times, and has an exact counterexample check.
- **R2:** the *minimal* counterexample (in dimension, order or size), with a proof of minimality.
- **R3:** the corrected statement: the conjecture proved under the extra hypothesis that the counterexample violates.
- **R4:** the exact threshold or parameter boundary where the conjecture switches from true to false.
- **R5:** a triage table of 30+ old conjectures with executable predicates, search results and status.

**Framework: counterexample-first triage.**
1. Harvest 30 candidate conjectures.
2. Encode each as an executable predicate.
3. Run a cheap randomized and structured search (1 hour total across all 30).
4. Rank by "near-miss margin".
5. Spend deep effort only on the top 3.
6. Rationalize any witness, then minimize it.
Each lane output is then a family of small theorems (R2–R4) around one witness.

**Evaluator:** the predicate checker on the exact witness.

**Crowding watch:** medium. Check the Omega Institute's list and formal-conjectures for each harvested conjecture *before* searching.

---

## L15 — Fresh-arXiv race lane (posted 24–31 Oct 2026)

**Why this lane.** Exactly one lane plays the speed game deliberately. A question posted in the last 7 days has not yet been registered by the Omega Institute or others (their Higuchi–Sudbery registration lag was days to weeks).

- **R1:** answer an explicit open question or conjecture from an arXiv paper posted 24–31 Oct 2026 in math.OC, math.CO, math.PR, quant-ph, math.FA or cs.DS that has a verifier (V ≥ 2).
- **R2:** a special case or restricted class of that question.
- **R3:** a counterexample to the strongest version.
- **R4:** a sharp numerical frontier with exact certificates.
- **R5:** the formal statement in Lean, which helps priority because the formal statement can be timestamped immediately.

**Framework: speed and ask.**
1. Within 1 hour, shortlist 10 questions and score them.
2. Within 2 hours, pick one and **commit a hash of the target** publicly (R-5).
3. Email the authors *at D1*, not at the end.
4. Timestamp at status B immediately (Zenodo/commit), and write the manuscript after.

**Evaluator:** per target, defined in the contract.

**Crowding watch:** high by design. Recheck the Omega Institute's list every 6 hours.
