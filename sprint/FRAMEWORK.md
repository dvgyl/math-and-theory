# FRAMEWORK-1.0: discovery sprint, Sat 31 Oct to Sun 1 Nov 2026

Status: **draft for freeze**. Written by Claude for Phase 1. Replaces the 72-hour plan in `deep-research-report.md` wherever the two disagree.

Deadline: **Sun 1 Nov 23:59 UTC**, about 44 hours from the time of writing (Sat 03:15 UTC).

---

## 0. Red team of the GPT framework: what is wrong and what changes

The GPT report gets the general shape of the loop right: measurable target, executable evaluator, failure memory, independent referee, result ladder. Keep that. It has six problems that matter for *this* sprint and *this* repo.

### 0.1 It solves the wrong bottleneck

Your discovery engine already works. The repo holds 45 manuscripts produced in about five days, and 30 October alone added roughly 14 results. **What fails is novelty, not discovery.** Six results already have priority collisions (`PRIORITY_AND_NOVELTY.md`), and the strongest one was just scooped. The GPT framework has a generic novelty checklist but no strategy for **not choosing a collided target in the first place**.

### 0.2 Its 15 directions are the most crowded real estate in AI mathematics

Cap sets, kissing numbers, Sidon sets, small Ramsey numbers and finite codes are exactly the problems that AlphaEvolve published a public problem repository for ([google-deepmind/alphaevolve_repository_of_problems](https://github.com/google-deepmind/alphaevolve_repository_of_problems), 67 problems). Erdős and OEIS problems are being worked through by AlphaProof Nexus (reported as 9 of 353 Erdős problems and 44 of 492 OEIS conjectures, [arXiv:2605.22763](https://arxiv.org/abs/2605.22763)). The Omega Institute's `trureturing` repository claims 565 open problems closed (406 proved, 159 refuted) in Lean. It is the group that pre-empted your Higuchi–Sudbery result.

**Structural cause of collisions:** competitors run the *same model* (GPT-6 Astra Pro) with essentially the *same prompt* ("find a ripe open conjecture in a recent arXiv paper, prove or refute it, formalize in Lean"). The same model ranks the same targets highest, so a default Astra target choice is a target someone else is also attacking. **Target selection must be anti-correlated with what a default Astra would choose.**

### 0.3 The 72-hour timeline does not exist

You have about 44 hours. The GPT plan's 15 lanes × 5 roles is 75 Astra conversations, all relayed by one human proxy. That is not feasible. The redesign below uses **one Astra Pro session per lane**, which plays the roles in sequence under a hard output contract, plus **one fresh referee session per surviving candidate**. That comes to about 15 + 8 = 23 sessions.

### 0.4 It assumes compute Astra does not have

nauty, SAT, MILP, SDP at scale, CPU clusters and Lean builds: an Astra chat session has a sandbox with timeouts, not a cluster. **Fix: this container (Claude, Phase 3) runs the frozen evaluators and Lean.** Astra emits witnesses and certificates as files in a fixed format. Claude runs the checkers *blind*: it is given the witness file and the frozen checker, never Astra's reasoning, so Phase 3 stays independent.

### 0.5 It has no statement-fidelity gate

The main criticism of the August Astra announcement was whether *the formal statements matched the original problems*. Passing Lean proves the Lean statement, nothing more. **New hard gate (G-FID):** Claude compares the Lean/formal statement word by word against the source PDF's statement before anything is promoted.

### 0.6 Its yield target is honest but miscalibrated for you

Measured against your own throughput, **5–10 verified, research-grade packages by Sunday night is realistic**. Five to ten that survive novelty review *and* would be called breakthroughs by a specialist is not. Plan for 5–10 packages, expect 1–3 standouts, and treat anything beyond that as upside.

---

## 1. Six rules that are new relative to the GPT framework

**R-1 Anti-correlated targeting.** Every lane targets one of:
- **(a) your own frontier**: a boundary that one of *your* published results created. Nobody else knows its exact shape, and you already hold the code, certificates and Lean modules for it. This is your moat, and 8 of the 15 lanes use it.
- **(b) a low-traffic source**: a journal-only or pre-2015 conjecture, a thesis "open problems" chapter, an Oberwolfach/BIRS/AIM problem-session report, or a small community with no AI-math presence.
- **(c) a speed race**: an open question from arXiv posted in the last 7 days. You win only by speed, so exactly one lane is allowed here.

**R-2 Crowding check before work (blacklist ≠ ignore).** **The Astra Scout runs every check below itself at S0** and logs each query and result in the `CONTRACT`'s CROWDING LOG. A hit means stop and choose again, or downgrade the target to a ladder rung. At G0, Claude reviews the log for missing sources rather than redoing the searches. `sprint/crowd.py` is an optional backstop: it searches local clones of the repos and the arXiv/Zenodo/Semantic Scholar APIs, if anyone wants a second pass.

*Layer 1: AI-lab result repositories (search each by conjecture name, poser names and the source arXiv ID).*
- **openai/math**: **the main OpenAI repository.** It holds 721 manuscripts in 373 families from about 4,000 problems posed to an internal model, with roughly 3 hours of Pro thinking each. Lean covers about 42%. It is updated in releases (`history.md`: 6, 7, 26 and 29 Oct so far). Titles carry dates, and its problems are mostly large named conjectures (Hodge for CM abelian varieties, ETH, Kakeya/local smoothing, the quasi-Riemann hypothesis, Kaplansky direct-finiteness, mutually unbiased bases in dimension 6). Treat every family *and its stated follow-ups* as occupied. Re-pull before G0 and before Phase 3; it moves fast.
- **openai/ten-proofs**: OpenAI's Astra "Ten advances" (Aug 2026). It covers sphere packing, binary/spherical codes, non-sofic groups, Connes rigidity, permanent circuit lower bounds, quantum parallel repetition, CVP hardness, Ehrhart volume, multicolor triangle Ramsey (Erdős 183) and the compactness/degeneracy conjectures (Erdős 146, 180). Treat these fields *and their immediate follow-up questions* as occupied by OpenAI. Also read the companion paper `cdn.openai.com/pdf/ten-proofs-oai.pdf` and the reasoning walkthroughs, because their "further questions" sections are where OpenAI goes next.
- **the-omega-institute/trureturing**: 1,595 problem files in `Problems/`, each recording the source arXiv ID, the exact quoted conjecture and the issue number. Search by **source arXiv ID**, not only by keywords: Omega mines *every* conjecture in a source paper once it has opened that paper.
- **google-deepmind/formal-conjectures**: Erdős, MathOverflow, Wikipedia, OEIS and paper conjectures, stated in Lean.
- **google-deepmind/alphaevolve_repository_of_problems**: 67+ construction and bound problems.
- **teorth/erdosproblems**: the erdosproblems.com database.

*Layer 1b: explicit preprint-server checks (run them on the target name, the conjecture name and every source arXiv ID).* These are mandatory. A repo-only check would have missed the 27 Oct anonymous Zenodo deposit that overlaps the repo's thermal-kurtosis result:
- **arXiv.** Run each of these:
  - (i) A keyword search, newest first (`arxiv.org/search` or the `export.arxiv.org/api/query` API).
  - (ii) Every version of the source paper (v2/v3 often add "Note added: this conjecture was resolved in …"). Check its listing page and comments field.
  - (iii) Papers citing each source arXiv ID (Semantic Scholar or Google Scholar "cited by"). Read everything dated within 120 days.
  - (iv) The new-submission listings for the last 14 days in the lane's categories (`arxiv.org/list/<cat>/pastweek`). Search engines and APIs lag by 1–3 days.
  - (v) A Google full-text search: `site:arxiv.org "<conjecture name>"` and `site:arxiv.org "<source arXiv id>"`.
- **Zenodo.** Search `zenodo.org/search?q="<term>"&sort=newest` on every term combination and on the source arXiv ID. Zenodo is where AI-math groups and anonymous agents timestamp results *before* arXiv. Open every record dated within 120 days, and read its creators, related identifiers (GitHub links) and description.
- **ResearchGate.** It has no API and blocks scripts (HTTP 403), so the Astra Scout or a browser does this:
  - `site:researchgate.net "<conjecture name>"` and `site:researchgate.net "<source arXiv id>"`.
  - The **poser's and coauthors' ResearchGate profiles**: Research tab, sorted by date, including preprints, data and presentations. Posers often put "solution" notes there and nowhere else.
  - The source paper's ResearchGate page: its citations and its Q&A section.
- **Also:** HAL (`hal.science`), OSF Preprints, Preprints.org, SSRN, TechRxiv, Authorea (`site:` searches), and the poser's personal homepage.

*Layer 2: everything else:*
- **Live Omega issues** (`github.com/the-omega-institute/trureturing/issues?q=<name>`). New registrations appear there days before a `Problems/` file exists. The local clone is a snapshot from Sat 31 Oct.
- **The AI-solved results literature**:
  - AlphaProof Nexus ([arXiv:2605.22763](https://arxiv.org/abs/2605.22763)): its tables of solved Erdős and OEIS problems.
  - DeepMind Aletheia: its Erdős results.
  - AxiomProver: its solved list, including Fel's conjecture.
  - Harmonic Aristotle.
  - OpenAI's May 2026 unit-distance disproof.
  - Running lists such as The Neuron's "open problems AI has solved".
- **erdosproblems.com forum threads** for the problem.
- **OEIS** conjecture entries.
- **MathOverflow.**
- **arXiv full text since 2026-06-01**: the target's name together with "LLM", "AI-assisted", "AlphaEvolve", "Lean", "GPT" or "Gemini".
- **GitHub code search** for the conjecture name and for the source's arXiv ID: many AI-math groups commit Lean files named after the source.
- **Google Scholar "cited by"** on the source paper.
- **This repo's own history** (`git log`, the removed `ACTIVE_PROBLEMS.md`), so no two lanes repeat an earlier lane.

**Source-paper rule:** if Omega or OpenAI has *any* problem file from the same source paper, the whole paper counts as opened. Every other conjecture in that paper gets C −2 automatically.

**R-3 Ask the poser first.** In 4 of your 6 collisions the problem's poser knew the answer and told you *after* you published. As soon as a lane reaches status D1 or C (see §4), send the poser a two-line email: "Is Question X of [paper] still open? I have a candidate result I would like to check against your knowledge before posting." A 24-hour reply is the cheapest and strongest novelty check that exists. Send it on Saturday, not on Sunday.

**R-4 Byproduct by construction (the "quasi-RH" rule).** Every ladder rung below R1 must be a **standalone theorem with its own precise statement**, chosen *before* work starts, that a specialist would accept as a contribution on its own. "Partial progress toward X" is not a rung. "X holds for the class C, which contains the known extremizers" is a rung. Each lane pre-registers its ladder (commit with a timestamp) before attacking R1.

**R-5 Timestamp on verification, not on polish.** As soon as a result reaches status B, commit a hash of the theorem statement and witness to the public repo, plus a Zenodo DOI if possible. The manuscript comes later. Your 27-October Fourier commit preceded Fang–Huang's arXiv posting by 47 hours; it only failed because their proof had circulated privately. Speed still matters.

**R-6 Significance prefilter.** Your old ledger shows several lanes ending with the verdict "verified but not exceptional significance" (ALG-B B06, NT-C, TCS-C). Score significance *before* proof work (§2). Do not start on any target with S < 2.

---

## 2. Target selection score (the Scout computes this; Claude checks it at gate G0)

| Factor | Range | Meaning |
|---|---|---|
| **V** verifier | 0–3 | 3 = exact finite or rational check, or a Lean-feasible statement; 0 = only informal proof possible |
| **F** frontier precision | 0–2 | the current best result is a precise number or statement with a citation |
| **S** significance | 0–3 | poser stature, years open, named conjecture in a refereed venue, citations |
| **M** moat | 0–3 | you hold infrastructure (your code, certificates, Lean modules) that others lack |
| **L** ladder depth | 0–2 | at least 3 rungs that are independently publishable |
| **C** crowding | 0 to −4 | −1 per crowding hit from R-2; −2 if the target is in an AI-labs' public list |

**Score = V + F + S + M + L + C.** Proceed only if Score ≥ 8 **and** S ≥ 2 **and** C ≥ −1.

---

## 3. Lane protocol (one Astra Pro session per lane)

Each lane session runs these stages *in order*, in one conversation, and must emit the named artifact at each stage. The user relays only the artifacts; Claude never reads Astra's reasoning.

| Stage | Astra role | Must emit | Time box |
|---|---|---|---|
| S0 | Scout | `CONTRACT` (template in `ASTRA_PREAMBLE.md`), §2 score, crowding-check log, pre-registered ladder | 60–90 min |
| — | **Gate G0 (Claude, 10 min per lane)** | approve, re-target, or kill | — |
| S1 | Builder | witnesses, data and candidate objects in the `WITNESS` format | 4–6 h |
| S2 | Breaker | attack log: every strengthening that failed, smallest counterexamples | 1–2 h |
| S3 | Theorist | `CLAIM` blocks: one precise theorem per rung reached, with proof | 3–6 h |
| — | **Gate G1 (Sat ~21:00 UTC)** | keep about 8 lanes | — |
| S4 | **fresh** Astra Referee session (not the lane's own) | `REFEREE` verdict produced from `CLAIM` + `WITNESS` only | 1–2 h |
| S5 | Lane session | Lean statement + proof attempt for the surviving claim | 2–6 h |
| — | **Phase 3 (Claude)** | G-FID, blind evaluator run, Lean build, novelty audit, poser email | Sunday |

**Descend-don't-restart rule:** when a rung fails, the lane moves to the next rung *with the failure log attached*. A counterexample to a strengthening is usually the next rung.

**Kill rules:**
- No `WITNESS` or `CLAIM` at any rung by G1: narrow the lane to R4/R5 only.
- Still nothing 6 hours later: terminate the lane.
- A crowding hit discovered mid-run: freeze the lane, record it, and switch to the lane's designated low-crowding rung.

---

## 4. Status ladder (claim language is bound to status)

| Status | Meaning | Permitted language |
|---|---|---|
| D0 | hypothesis | "we are investigating" |
| D1 | reproducible computational signal | "computations suggest" |
| C | complete informal proof, unrefereed | "candidate theorem" |
| B | passed G-FID + blind evaluator + fresh referee, *or* Lean | "verified; novelty pending" |
| A2 | B + full novelty audit + poser contacted, no prior work found | "apparently new" |
| A1 | A2 + improves a precisely cited frontier + poser reply or 48 h silence | "new result" |

"Breakthrough" is never used before A1, and only by you (the human coordinator).

---

## 5. Phase 3 protocol (Claude, Sunday)

For each surviving `CLAIM`, Claude receives **only** the `CLAIM`, `WITNESS`, `CONTRACT` and Lean files. It does the following, in order:

1. **G-FID (statement fidelity):** retrieve the source paper and compare its statement with the `CLAIM` and the Lean statement, quantifier by quantifier. List every deviation (domain, boundary cases, empty sets, field, strictness).
2. **Blind evaluator:** run the lane's checker on the witness here. Exact arithmetic only; floating point is never accepted as proof.
3. **Adversarial attack:** a fresh counterexample search on the claim as stated.
4. **Independent reconstruction:** re-derive the key step without the supplied proof, then read the proof.
5. **Lean:** build and run an axiom audit (allowed axioms: `propext`, `Classical.choice`, `Quot.sound`), checking for `sorry`, `native_decide` usage and custom axioms.
6. **Novelty audit:** run the R-2 list plus the GPT report's §"Novelty/prior-art audit checklist", and draft the R-3 poser email.
7. **Package** in the repo layout (`docs/ADDING_RESULTS.md`), and set the status.

*Container note:* Python with numpy, scipy, sympy, mpmath, networkx, cvxpy and python-sat is installed. The Lean toolchain needs your OK to install, because the elan installer is a remote script. Say so and I will set it up before Sunday.

---

## 6. Schedule (UTC)

| When | What | Who |
|---|---|---|
| Sat 03–06 | Freeze this framework (FRAMEWORK-1.0) | you + GPT + Claude |
| Sat 06–08 | Launch all 15 lanes at S0; paste back `CONTRACT`s | you → Astra |
| Sat 08–09 | **G0**: approve, re-target or kill each contract (reviewing the Scout's crowding log) | Claude |
| Sat 09–21 | S1–S3 discovery. R-3 poser emails go out as lanes reach D1/C | Astra; you relay |
| Sat ~21 | **G1**: score lanes, keep about 8 | you + Claude |
| Sat 21–Sun 07 | S3 proofs on survivors; S4 fresh referees | Astra |
| Sun 07–19 | **Phase 3** on each survivor; S5 Lean in parallel | Claude + Astra |
| Sun 19–23 | Packages, R-5 timestamps, claim calibration | you + Claude |

Sleep is a resource. Lanes S1–S3 can run unattended overnight if you launch them with the full preamble.

---

## 7. Portfolio

See `LANES.md` for the 15 lane cards. Summary:

| # | Lane | Type | Collision risk | Unique framework |
|---|---|---|---|---|
| L01 | Exact ADMM multiplier-step threshold τ* | own frontier | low | two-sided squeeze + exact reconstruction |
| L02 | Nesterov finite-dimensional gap 2 < r < 3 | own frontier | low–med | dimension descent |
| L03 | Unconditional Keller–Klein | own frontier | medium | dependency elimination |
| L04 | Operator-splitting orbit factory | own frontier → factory | low–med | exact periodic-orbit factory |
| L05 | PPT entanglement-cost hierarchy: fixed dimension | own frontier | low | witness compression + collapse classes |
| L06 | Nonnegative rank of tensor products: the true law | own frontier | low–med | counterexample → law |
| L07 | Gyires conjecture: uniform rank-two and order 7 | own frontier | low | certificate-family induction |
| L08 | Spectral tiles in F₂⁹ | own frontier | **high** | isomorph-free classification |
| L09 | Conditional independence and polymatroids | small community | low | LP-duality oracle |
| L10 | Sharp current-cumulant bounds beyond the single cycle | small community | **high: Omega has Ptaszyński 2022** | extremizer-first |
| L11 | Quantitative replacements for nonexistent AME states | adjacent to own | med–high | stabilizer exhaustion → general bound |
| L12 | Valuation theory sequels with your Lean stack | own infrastructure | low | Lean-first exploration |
| L13 | Graph-polynomial sequence conjecture lattice | own frontier | med–high | conjecture lattice |
| L14 | Old-journal conjecture disproof factory | low-traffic source | medium | counterexample-first triage |
| L15 | Fresh-arXiv race lane | speed race | high, by design | speed and ask |

**Compute priority at launch** (revised after the local crowding check):
- **First:** L01, L03, L04, L06, L09. Each has an exact verifier, your moat, and **zero hits** in the five local repos.
- **Second:** L02, L05, L07, L12.
- **Reserves:** L08, L10, L11, L13, L14, L15. They lose resources quickly unless they emit a `WITNESS` by G1.

Local crowding results, Sat 31 Oct (zero hits means none in any of the five local repos):

| Lane | Hits |
|---|---|
| L01 | zero (the ADMM source 1503.06387 is opened by Omega, but only for projection AM–GM) |
| L02 | zero |
| L03 | zero |
| L04 | zero |
| L05 | Omega uses Lami–Mele–Regula states in two other problems: C −1 |
| L06 | zero |
| L07 | zero (formal-conjectures Erdős 499 is a different question) |
| L08 | zero for F₂ⁿ (formal-conjectures has only Euclidean Fuglede) |
| L09 | zero |
| L10 | **Omega #22468** |
| L11 | **Omega Higuchi–Sudbery** |
| L12 | zero |
| L13 | **Omega #23025, #13267** |

Re-run at G0 on each `CONTRACT`'s actual source ID with `--online`.

openai/math (added later): **zero real hits** for every lane and for every existing repo result. All keyword matches were incidental citations.
