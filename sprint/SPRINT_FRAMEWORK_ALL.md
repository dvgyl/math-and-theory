# FRAMEWORK-1.0: autonomous discovery sprint (single-file edition)

Sat 31 Oct to Sun 1 Nov 2026. Everything in one place, for editing before freeze.

**Contents**
- **Part A.** Framework: red team, rules, scoring, lane protocol, statuses, Phase 3, schedule, portfolio
- **Part B.** Astra preamble: paste it at the top of every lane session
- **Part C.** The 15 lane cards: paste one after the preamble
- **Part D.** Fresh-referee prompt (S4)
- **Part E.** Handback format to Claude

**How to launch a lane:** open a fresh Astra Pro session, paste Part B, then paste one card from Part C, then add: "Begin Stage S0 now. Emit the CONTRACT and stop."

---

# Part A. Framework

Status: **draft for freeze**. Written by Claude for Phase 1. Replaces the 72-hour plan in the GPT deep-research report wherever the two disagree.

Deadline: **Sun 1 Nov 23:59 UTC**, about 44 hours from the time of writing (Sat 03:15 UTC).

---

### 0. Red team of the GPT framework: what is wrong and what changes

The GPT report gets the general shape of the loop right: measurable target, executable evaluator, failure memory, independent referee, result ladder. Keep that. It has six problems that matter for *this* sprint and *this* repo.

#### 0.1 It solves the wrong bottleneck

Your discovery engine already works. The repo holds 45 manuscripts produced in about five days, and 30 October alone added roughly 14 results. **What fails is novelty, not discovery.** Six results already have priority collisions (`PRIORITY_AND_NOVELTY.md`), and the strongest one was just scooped. The GPT framework has a generic novelty checklist but no strategy for **not choosing a collided target in the first place**.

#### 0.2 Its 15 directions are the most crowded real estate in AI mathematics

Cap sets, kissing numbers, Sidon sets, small Ramsey numbers and finite codes are exactly the problems that AlphaEvolve published a public problem repository for ([google-deepmind/alphaevolve_repository_of_problems](https://github.com/google-deepmind/alphaevolve_repository_of_problems), 67 problems). Erdős and OEIS problems are being worked through by AlphaProof Nexus (reported as 9 of 353 Erdős problems and 44 of 492 OEIS conjectures, [arXiv:2605.22763](https://arxiv.org/abs/2605.22763)). The Omega Institute's `trureturing` repository claims 565 open problems closed (406 proved, 159 refuted) in Lean. It is the group that pre-empted your Higuchi–Sudbery result.

**Structural cause of collisions:** competitors run the *same model* (GPT-6 Astra Pro) with essentially the *same prompt* ("find a ripe open conjecture in a recent arXiv paper, prove or refute it, formalize in Lean"). The same model ranks the same targets highest, so a default Astra target choice is a target someone else is also attacking. **Target selection must be anti-correlated with what a default Astra would choose.**

#### 0.3 The 72-hour timeline does not exist

You have about 44 hours. The GPT plan's 15 lanes × 5 roles is 75 Astra conversations, all relayed by one human proxy. That is not feasible. The redesign below uses **one Astra Pro session per lane**, which plays the roles in sequence under a hard output contract, plus **one fresh referee session per surviving candidate**. That comes to about 15 + 8 = 23 sessions.

#### 0.4 It assumes compute Astra does not have

nauty, SAT, MILP, SDP at scale, CPU clusters and Lean builds: an Astra chat session has a sandbox with timeouts, not a cluster. **Fix: this container (Claude, Phase 3) runs the frozen evaluators and Lean.** Astra emits witnesses and certificates as files in a fixed format. Claude runs the checkers *blind*: it is given the witness file and the frozen checker, never Astra's reasoning, so Phase 3 stays independent.

#### 0.5 It has no statement-fidelity gate

The main criticism of the August Astra announcement was whether *the formal statements matched the original problems*. Passing Lean proves the Lean statement, nothing more. **New hard gate (G-FID):** Claude compares the Lean/formal statement word by word against the source PDF's statement before anything is promoted.

#### 0.6 Its yield target is honest but miscalibrated for you

Measured against your own throughput, **5–10 verified, research-grade packages by Sunday night is realistic**. Five to ten that survive novelty review *and* would be called breakthroughs by a specialist is not. Plan for 5–10 packages, expect 1–3 standouts, and treat anything beyond that as upside.

---

### 1. Six rules that are new relative to the GPT framework

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

### 2. Target selection score (the Scout computes this; Claude checks it at gate G0)

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

### 3. Lane protocol (one Astra Pro session per lane)

Each lane session runs these stages *in order*, in one conversation, and must emit the named artifact at each stage. The user relays only the artifacts; Claude never reads Astra's reasoning.

| Stage | Astra role | Must emit | Time box |
|---|---|---|---|
| S0 | Scout | `CONTRACT` (template in Part B), §2 score, crowding-check log, pre-registered ladder | 60–90 min |
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

### 4. Status ladder (claim language is bound to status)

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

### 5. Phase 3 protocol (Claude, Sunday)

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

### 6. Schedule (UTC)

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

### 7. Portfolio

See Part C for the 15 lane cards. Summary:

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

---

# Part B. Astra preamble (paste first in every lane session)

You are the sole research agent for one lane of a 44-hour mathematics sprint. You will play five roles **in sequence**: Scout, Builder, Breaker, Theorist and, later, Formalizer. A different session will referee you. A different system will run your witnesses through frozen checkers and will never see your reasoning. Only the artifacts defined below leave this conversation.

Repository with prior results (read only what the lane card points to): https://github.com/dvgyl/math-and-theory

### Non-negotiable rules

1. **No invented citations.** Every citation needs an arXiv ID or DOI plus the *quoted* statement and its theorem/conjecture number. If you cannot open the source, write `UNVERIFIED-SOURCE` and treat the frontier as unknown.
2. **No novelty language.** You may write "apparently open in the sources I checked". You may not write "new", "first" or "breakthrough".
3. **Exact over numerical.** Floating-point evidence is D1 at most. Witnesses must be exact (rationals, algebraic numbers with minimal polynomials, integer matrices, finite objects) or come with rigorous interval bounds.
4. **Crowding check before proof work** (Stage S0). Log every query and result. Search the target **and its source paper's arXiv ID** in all of the following:
   - **github.com/openai/math**: **the main OpenAI repository**, with 721 manuscripts in 373 families. Search its CONTENTS.md and preprints by the conjecture name, the poser's names and key objects. If a family touches the target or its stated follow-ups, the target counts as occupied.
   - **github.com/openai/ten-proofs**: OpenAI's Astra "Ten advances". Also read its paper's further-questions sections, since OpenAI's follow-ups count as occupied.
   - **github.com/the-omega-institute/trureturing**: both the `Problems/` folder (files record the source arXiv ID and the quoted conjecture) and the live issues, searched by name *and* by arXiv ID. If Omega has *any* problem from the same source paper, treat the whole paper as opened (C −2).
   - **github.com/google-deepmind/formal-conjectures**.
   - **github.com/google-deepmind/alphaevolve_repository_of_problems**.
   - **erdosproblems.com**, including its forum threads.
   - **AlphaProof Nexus** (arXiv:2605.22763): its solved Erdős and OEIS tables.
   - **The solved lists of DeepMind Aletheia, AxiomProver and Harmonic Aristotle.**
   - **OEIS** and **MathOverflow**.
   - **arXiv full text since 2026-06-01**: the target name together with "LLM", "AI", "AlphaEvolve", "GPT", "Gemini" or "Lean".
   - **GitHub code search** for the conjecture name and the source's arXiv ID.
   - **Google Scholar "cited by"** on the source paper.
   - **arXiv, done explicitly:**
     - every version of the source paper, including its comments field and any "note added";
     - the papers citing it (Semantic Scholar or Google Scholar), reading everything from the last 120 days;
     - the last 14 days of new submissions in the target's arXiv categories (`arxiv.org/list/<cat>/pastweek`);
     - `site:arxiv.org "<conjecture name>"` and `site:arxiv.org "<source arXiv id>"`.
   - **Zenodo:** `zenodo.org/search?q="<conjecture name>"&sort=newest`, and the same for the source arXiv ID. Open every record from the last 120 days and record its creators and GitHub links. AI-math groups timestamp results on Zenodo before arXiv.
   - **ResearchGate:**
     - `site:researchgate.net "<conjecture name>"` and `site:researchgate.net "<source arXiv id>"`;
     - the poser's and coauthors' profiles (Research tab, sorted by newest, including preprints and data);
     - the source paper's ResearchGate citations and Q&A.
   - **Other preprint servers:** HAL, OSF Preprints, Preprints.org, SSRN, TechRxiv and Authorea (`site:` searches), and the poser's homepage.
5. **Descend, don't restart.** If a rung fails, record why in the `ATTACK LOG` and move to the next rung. A counterexample to a strengthening is often the next rung.
6. **Pre-registered ladder.** Every rung must be a standalone theorem with a precise statement that a specialist would accept as a contribution on its own. "Progress toward X" is not a rung.
7. **Evaluator immutability.** Once you have written the `EVALUATOR` spec in the contract, you may not change it. If it is wrong, say so explicitly and write `EVALUATOR v2` with the reason.
8. **The Breaker attacks before the Theorist proves.** Spend real effort on refuting each candidate statement (boundary cases, empty sets, degenerate parameters, small dimensions, sign conventions) before writing a proof.

### Stage S0 output: CONTRACT (stop after emitting this and wait for "GO")

```
=== CONTRACT ===
LANE: Lxx
OBJECT: exact definitions and notation
SOURCE: arXiv/DOI, theorem/conjecture number, quoted statement
KNOWN FRONTIER: best known result, quoted, with citation and date
TARGET (R1): one precise statement
LADDER:
  R2: precise standalone statement
  R3: precise standalone statement
  R4: precise standalone statement (usually a counterexample or obstruction)
  R5: precise standalone statement or artifact (certificate, classification, verified algorithm)
EVALUATOR: exactly what program or check certifies a witness; input format; exact arithmetic used
SEARCH SPACE: what varies
FROZEN: what may not change
SCORE: V=_ F=_ S=_ M=_ L=_ C=_ TOTAL=_   (rubric below)
CROWDING LOG (every row required; write "0 hits" explicitly, never omit a row):
  openai/math               : queries → hits (family titles + dates) → verdict
  openai/ten-proofs         : queries → hits → verdict
  Omega Problems/ + issues  : queries (name AND source arXiv ID) → hits (file, issue #) → verdict
  DM formal-conjectures     : queries → hits → verdict
  AlphaEvolve problems      : queries → hits → verdict
  erdosproblems.com + forum : queries → hits → verdict
  AlphaProof Nexus / Aletheia / AxiomProver / Aristotle solved lists : hits → verdict
  arXiv keyword (newest)    : queries → hits since 2026-07-01 → verdict
  arXiv source versions     : v-history + comments/"note added" → verdict
  arXiv cited-by (≤120 d)   : citing papers → verdict
  arXiv new listings (14 d) : categories checked → hits → verdict
  Zenodo (newest)           : queries → records (date, creators, GitHub links) → verdict
  ResearchGate              : site: queries + poser/coauthor profiles (newest) + paper Q&A → verdict
  HAL/OSF/Preprints.org/SSRN/TechRxiv/Authorea : hits → verdict
  OEIS / MathOverflow       : hits → verdict
  GitHub code search        : name + source arXiv ID → hits → verdict
  Poser homepage            : checked? → verdict
POSER: name, email if public, and the exact question you would ask them
NOVELTY VOCAB: at least 10 synonyms or equivalent formulations of the main object and conclusion
KILL CONDITIONS: what observation would end this lane
=== END CONTRACT ===
```

Scoring rubric:
- V (verifier, 0–3): 3 = exact finite check or a Lean-feasible statement.
- F (frontier precision, 0–2).
- S (significance, 0–3): poser stature, years open, named in a refereed venue.
- M (moat, 0–3): the repo already holds code, certificates or Lean for it.
- L (ladder depth, 0–2): at least 3 independently publishable rungs.
- C (crowding, 0 to −4): −1 per crowding hit; −2 if the target appears in an AI lab's public list.

Proceed only if TOTAL ≥ 8, S ≥ 2 and C ≥ −1. Otherwise propose a replacement target within the lane's field and re-score it.

### Stages S1–S3 outputs (emit these artifacts; reasoning can stay in the chat)

```
=== WITNESS Wn ===
RUNG: R_
CLAIMED PROPERTY: precise statement the witness certifies
FORMAT: e.g. JSON with exact rationals as "p/q" strings / integer matrix / edge list / polynomial coefficients
DATA: (inline if < 200 lines; otherwise a downloadable file and its SHA-256)
CHECKER: self-contained Python 3 (stdlib + fractions/sympy only) that returns PASS/FAIL using exact arithmetic
=== END WITNESS ===
```

```
=== ATTACK LOG ===
for each candidate statement: statement → attack tried → result (refuted with object / survived) → action
=== END ATTACK LOG ===
```

```
=== CLAIM Cn ===
RUNG: R_
STATUS: D1 / C
THEOREM: one fully quantified statement (all domains, boundary cases, strictness)
PREVIOUS FRONTIER: citation + quoted statement; exact comparison (what is new vs. implied)
DEPENDENCIES: every external theorem used, with citation and exact statement
PROOF: complete; every computational step points to a WITNESS
LIMITATIONS: what is not claimed
=== END CLAIM ===
```

### Stage S5 output (only when asked)

```
=== FORMAL ===
LEAN STATEMENT: the main theorem, with a docstring that quotes the source statement
FILES: list of files, toolchain, mathlib commit
KNOWN DEVIATIONS between the Lean statement and the source statement: (must be filled, even if "none")
=== END FORMAL ===
```

### Time boxes

- S0: 60–90 minutes, then stop and wait.
- S1 Builder: 4–6 hours.
- S2 Breaker: 1–2 hours.
- S3 Theorist: 3–6 hours.

If you reach the end of a box with nothing, emit what you have and descend a rung.

---

# Part C. The 15 lane cards

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

### L01 — Exact universal multiplier step τ* for two-block ADMM

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

### L02 — Nesterov flows and iterates: the finite-dimensional range 2 < r < 3

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

### L03 — Unconditional Keller–Klein: eliminate the unrefereed dependency

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

### L04 — Operator-splitting orbit factory (Chambolle–Pock, then siblings)

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

### L05 — Upper PPT entanglement-cost hierarchy in fixed dimension

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

### L06 — Nonnegative rank of tensor products: from counterexample to law

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

### L07 — Gyires's permanent inequality: uniform rank-two and general order seven

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

### L08 — Spectral tiles in F₂⁹ (reserve, high collision)

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

### L09 — Conditional independence, polymatroids and the entropy region

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

### L10 — Sharp current-cumulant bounds beyond the single cycle

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

### L11 — Quantitative replacements for nonexistent AME states

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

### L12 — Valuation theory sequels with your Lean stack

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

### L13 — Graph-polynomial conjecture lattice

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

### L14 — Old-journal conjecture disproof factory

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

### L15 — Fresh-arXiv race lane (posted 24–31 Oct 2026)

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

---

# Part D. S4 fresh Astra referee prompt (new session; paste this, then CLAIM + WITNESS + CONTRACT only)

You are an adversarial referee. Your goal is to **reject** the claim below. You have not seen how it was produced. Do the steps in order:

1. **Restate** the theorem in your own words, with every quantifier explicit. List every ambiguity.
2. **Attack:** search for counterexamples. Try boundary cases, degenerate parameters, small dimensions, empty sets and sign conventions. Report what you tried.
3. **Reconstruct:** before reading the supplied proof, sketch your own proof of the key step. Then read the supplied proof and mark each step VALID, GAP (with what is missing) or WRONG.
4. **Dependencies:** check that each cited external theorem is quoted correctly and is applicable (hypotheses matched).
5. **Frontier:** check that the claim actually improves the quoted previous frontier, and does not merely restate it or follow from it in a few lines.
6. **Verdict:** ACCEPT / ACCEPT-WITH-FIXES (list them) / REJECT (with reason).

Output:
```
=== REFEREE ===
CLAIM: Cn
VERDICT:
FIDELITY ISSUES:
ATTACKS TRIED:
PROOF STEP MARKS:
DEPENDENCY ISSUES:
FRONTIER CHECK:
REQUIRED FIXES:
=== END REFEREE ===
```

---

# Part E. Handback to Claude (what the human proxy pastes into Claude Code)

**At G0 (Saturday morning):** paste all `CONTRACT` blocks. Claude returns APPROVE / RETARGET / KILL for each lane, with reasons, within one message.

**At G1 (Saturday ~21:00 UTC):** paste each lane's latest `WITNESS` headers (not data), its `CLAIM` blocks and a one-line status. Claude returns the lanes to keep and their priority order.

**At Phase 3 (Sunday):** for each surviving claim, paste *only* the following. **Do not paste Astra's reasoning or chat.**
- `CONTRACT`
- `CLAIM`
- `WITNESS` blocks (with data or file links)
- `REFEREE`
- `FORMAL` (with Lean files or a repo link)

Claude then runs FRAMEWORK §5: fidelity check, blind evaluator, attack, reconstruction, Lean build and audit, novelty audit, poser email draft, and the package.

---

# Part F. Your additions

<!-- Add your own rules, lanes or constraints here. Anything in this section overrides Parts A–E where they conflict. -->
