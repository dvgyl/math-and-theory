# Priority and novelty disclosures

This record was first written on 30 October 2026 and updated later the same day and on 31 October 2026. It documents six results in this collection for which I learned of overlapping or earlier work through correspondence with researchers in the field after I had published them. In each case the information reached me only through that correspondence. My agents' original novelty searches did not find this work, and I was not aware of it when I first published the result. A [check against public problem records](#overlap-check-against-public-problem-records) on 31 October 2026 found earlier or related public work for eight further results and a later related record for a ninth.

These are scholarly priority disclosures, not retractions. Overlapping or earlier work does not by itself invalidate a mathematical proof. The proofs, Lean formalizations and verification records of all affected results are unchanged. Where a manuscript made an originality claim that the new information no longer supports, I have corrected it; the earlier versions remain in the Git history of this repository.

I summarize private correspondence factually and only to the extent needed here. I do not quote it.

## How to read these disclosures

I distinguish five kinds of information:

- **Prior public work**: results or claims that were publicly available before my publication, with a public source I can cite.
- **Private communication**: information a researcher told me in correspondence. I report it as what I was told and have not seen the underlying work unless I say so.
- **Competing claim**: a reported solution by another person or group that I have not seen or checked.
- **Provisional AI-generated finding**: an analysis produced by an AI system and shared with me. Neither I nor, to my knowledge, anyone else has independently verified it.
- **Established mathematical equivalence**: a comparison of the actual mathematical content that shows two results or certificates agree. Only the Higuchi–Sudbery case has an established equivalence of certificates. For the density-one-eighth bound, the published statements coincide, but the proofs have not been compared.

| Result | Correspondence | What I learned | Kind | Equivalence | My position |
|---|---|---|---|---|---|
| [Higuchi–Sudbery entropy bound](#higuchisudbery-four-qubit-entropy-bound) | Dr. Jef Pauwels, 30 October 2026 | The Omega Institute registered the problem on 5 October 2026 and committed a claimed Lean proof on 7 October 2026 | Prior public work | Certificates algebraically equivalent | No originality or priority claim |
| [Density-one-eighth Fourier-weight bound](#sharp-level-one-fourier-weight-at-density-one-eighth) | Professor Lei Yu, 30 October 2026 | Yijia Fang and Hao Huang had already proved the same bound, with equality cases; their manuscript circulated privately about a month earlier and appeared on arXiv on 29 October 2026 | Prior work; public preprint | Same bound; they also characterize equality; proofs not compared | No originality or priority claim |
| [Kovačec polygon enclosure](#kovačec-polygon-enclosure) | Professor Alexander Kovačec, 29 October 2026 | His own counterexample from June 2026 in an unpublished preprint; another counterexample sent to him by Wenlin Zhang | Private communication; competing claim | Not established | Earlier discoveries acknowledged; no priority claim |
| [Root-fidelity entropy bound](#three-state-root-fidelity-entropy-bound) | Dr. Wojciech Roga, 29 October 2026 | Another group claimed to him, several days earlier, a solution using AI and Lean | Private communication; competing claim | Not compared | Competing claim acknowledged; neither equivalence nor priority established |
| [Power ranks](#power-ranks-of-a-constant-recursive-sequence) | Professor Eric Rowland, 29 October 2026 | His own infinite family of rank sequences for rank-three recurrences, obtained while experimenting with an LLM | Private communication; independent overlapping result | Not compared | Overlap acknowledged; no duplication implied |
| [Binary spectral tile](#binary-spectral-tile-in-dimension-nine) | Dr. Samuel Ferguson, 30 October 2026 | He and Professor Joshua Iosevich knew of counterexamples to the stronger statement shortly after submitting their arXiv paper; an AI-generated comparison he shared suggests my construction is not affinely equivalent to his examples | Private communication; provisional AI-generated finding | Not established; non-equivalence suggested but unverified | Their earlier counterexamples acknowledged |

## Higuchi–Sudbery four-qubit entropy bound

Result: [A sum-of-squares proof of the four-qubit Higuchi–Sudbery entropy bound](papers/physics/higuchi-sudbery/) (`higuchi-sudbery`), first published in this repository on 27 October 2026.

On 30 October 2026, following my correspondence with Dr. Jef Pauwels, he informed me that the Omega Institute had recently announced a similar result. I was previously unaware of this work. When I investigated, I found that the Omega Institute had registered the problem on 5 October 2026 and publicly committed a claimed Lean proof on 7 October 2026 ([public record](https://github.com/the-omega-institute/trureturing/issues/13454)). A subsequent comparison showed that their 272-term sum-of-squares certificate and mine are algebraically equivalent.

- **Prior public work.** The Omega Institute's registration of the problem and its claimed Lean proof were public before my publication on 27 October 2026.
- **Established equivalence.** The two 272-term sum-of-squares certificates are algebraically equivalent, so the overlap with my result is substantial. I have not independently checked the Omega Institute's Lean proof, and I describe it as claimed.
- **My position.** I acknowledge the Omega Institute's earlier public work and make no originality or priority claim for this result. My manuscript, Lean formalization and verification records remain available as an independent derivation and check of the bound.

## Sharp level-one Fourier weight at density one eighth

Result: [The sharp level-one Fourier weight at density one eighth](papers/mathematics/sharp-eighth/) (`sharp-eighth`), dated and first published in this repository on 27 October 2026.

On 30 October 2026, Professor Lei Yu informed me that Yijia Fang and Hao Huang had already proved the same density-1/8 Fourier-weight bound. He told me that their manuscript had been shared privately approximately one month earlier. It was submitted to arXiv on 29 October 2026 as [*Average pairwise Hamming distance of a subset in a hypercube*](https://arxiv.org/abs/2610.40486) (arXiv:2610.40486). Their result also characterizes the equality cases. I was previously unaware of their work, and my agents' original novelty searches had not found it.

- **Prior work.** Fang and Huang proved the bound before I did. The private circulation of their manuscript about a month earlier is as Professor Yu reported it to me; I have not seen that version.
- **Public source.** I confirmed the public arXiv record: authors, title, version 1 dated 29 October 2026, and a summary stating that a subset of density 1/8 in the n-dimensional hypercube has average pairwise Hamming distance at least (n − 3)/2, with equality only for (n − 3)-dimensional subcubes, which answers Professor Yu's question. This is the average-distance form of the bound 3/64 on the level-one Fourier weight. I have read the public summary but not compared the full proofs.
- **What is established.** The published statements coincide in the bound. Their result is stronger in that it classifies the equality cases, which my note does not claim. Whether the two proofs share their method has not been examined.
- **Chronological note.** I first committed this result on 27 October 2026 at 17:59:36 UTC ([commit 6859d4a](https://github.com/dvgyl/math-and-theory/commit/6859d4a10a1b5da4c99f3f1de98ac2bf8270ac91)) and moved it unchanged to its current folder on 29 October 2026 at 05:41:03 UTC ([commit 05b3d2b](https://github.com/dvgyl/math-and-theory/commit/05b3d2bc00fe96ff335deca3d8d43812012a7fc0)). Fang and Huang submitted their proof to arXiv on 29 October 2026 at 17:15:18 UTC, about 47 hours after my first commit. This is a chronological coincidence, not a priority claim: their proof had circulated privately about a month earlier, as Professor Yu informed me on 30 October. A commit timestamp does not by itself establish when a commit became publicly accessible.
- **My position.** I acknowledge Fang and Huang's earlier work and make no originality or priority claim for this bound. I have withdrawn the statements in my manuscript that presented the bound as its contribution. My proof, its exact certificates and the Lean formalization remain available as an independent derivation and formal check.

The question is Problem 2 in Section VII of Lei Yu, [*On Average Distance, Level-1 Fourier Weight, and Chang's Lemma*](https://arxiv.org/abs/2504.02593) (arXiv:2504.02593).

## Kovačec polygon enclosure

Result: [A polygon enclosure fails for sums of normal matrices](papers/mathematics/kovacec/) (`kovacec`), dated 28 October 2026 and first published in this repository on 29 October 2026.

On 29 October 2026, following my correspondence with Professor Alexander Kovačec, he informed me that he had independently discovered a counterexample to his own conjecture in June 2026, documented in an unpublished preprint. He also mentioned that Wenlin Zhang had independently contacted him with another counterexample, apparently involving Lean. These developments were previously unknown to me.

- **Private communication.** Professor Kovačec's June 2026 counterexample is documented in an unpublished preprint that I have not seen. It predates my note. Wenlin Zhang's counterexample was reported to me by Professor Kovačec; I have not seen it.
- **Competing claim.** Wenlin Zhang's counterexample is an independent claim that reached Professor Kovačec before our correspondence.
- **Equivalence not established.** I do not know whether either counterexample is equivalent to my construction, which uses the spectra (0, 1, i) and (−1−i, 1, −1+i) and the determinant 2/3 + 2i/9.
- **My position.** I acknowledge both earlier discoveries. My note already made no priority claim; it now records them explicitly.

The conjecture is stated in Professor Kovačec's report [*A conjecture more precise and stronger than the one by Marcus and de Oliveira*](https://www.mat.uc.pt/preprints/ps/p2611.pdf) (Universidade de Coimbra preprint 26-11, April 2026).

## Three-state root-fidelity entropy bound

Result: [The three-state root-fidelity entropy bound](papers/physics/fidelity-three-state/) (`fidelity-three-state`), first published in this repository on 29 October 2026.

On 29 October 2026, following my correspondence with Dr. Wojciech Roga, he informed me that another group had contacted him several days earlier claiming to have solved the same conjecture using AI and Lean. I had been unaware of this parallel effort.

- **Competing claim.** The other group's claimed solution was reported to me by Dr. Roga. I have not seen it.
- **Not compared.** The two proofs have not been compared. Neither mathematical equivalence nor priority has been conclusively established.
- **My position.** I acknowledge the competing claimed solution. My proof, Lean formalization and verification records stand on their own and are unchanged.
- **Later finding.** On 31 October 2026, a check of public records found a claimed Lean proof of the same conjecture in the Omega Institute's public repository, dated 19 October 2026. It is described [below](#omega-root-fidelity-entropy-bound). I do not know whether it is the claim Dr. Roga described.

The conjecture is Conjecture 1 of Fannes, de Melo, Roga and Życzkowski, [*Matrices of fidelities for ensembles of quantum states and the Holevo quantity*](https://doi.org/10.26421/QIC12.5-6-8), Quantum Information and Computation 12 (2012).

## Power ranks of a constant-recursive sequence

Result: [A positive constant-recursive sequence with nonquasipolynomial power ranks](papers/mathematics/power-rank/) (`power-rank`), dated 28 October 2026 and first published in this repository on 29 October 2026.

On 29 October 2026, following my correspondence with Professor Eric Rowland, he informed me that he had recently been experimenting with an LLM and had independently obtained an infinite family of rank sequences for rank-three recurrences. His family also challenges the fixed-rank finiteness assertion in his paper with Jesús Sistos Barrón, which my companion theorem contradicts for every rank r ≥ 3.

- **Private communication.** Professor Rowland's family was reported to me in correspondence; I have not seen its construction.
- **Independent overlapping result.** At rank three, his family and my companion family both give infinitely many power-rank sequences, so this part of my result overlaps with independent work.
- **Not compared.** I do not suggest that his construction duplicates my rank-thirteen example, its nonquasipolynomial power ranks, or my other companion theorems. The constructions have not been compared.
- **My position.** I acknowledge his independently discovered overlapping result.

The finiteness assertion appears on page 2 of Rowland and Sistos Barrón, [*Complexity of powers of a constant-recursive sequence*](https://arxiv.org/abs/2501.14643) (arXiv:2501.14643).

## Binary spectral tile in dimension nine

Result: [A 64-point spectral tile in F₂⁹ with no periodic complement](papers/mathematics/binary-spectral-tile/) (`binary-spectral-tile`), first published in this repository on 30 October 2026.

On 30 October 2026, following my correspondence with Dr. Samuel Ferguson, he informed me that he and his coauthor Professor Joshua Iosevich had already become aware of counterexamples to the stronger statement shortly after submitting their recent arXiv paper. These findings were previously unknown to me.

Later on 30 October 2026, Dr. Ferguson shared with me an AI-generated comparison of my construction with his examples. It suggests that my construction is not affinely equivalent to his displayed example or to any of 210 constructions he had saved, despite substantial structural overlap. It also suggests that the constructions share common classifications of their tiling complements and spectra.

- **Private communication.** Their awareness of counterexamples was reported to me in correspondence; I have not seen their examples.
- **Provisional AI-generated finding.** The comparison was produced by an AI system. I have not independently verified it, and I do not treat its conclusions, including non-equivalence up to affine maps, as established mathematics.
- **Equivalence not established.** Whether their examples are equivalent to my 64-point construction remains unestablished. The comparison suggests that they are not, but only provisionally.
- **My position.** I acknowledge Ferguson and Iosevich's earlier counterexamples to the stronger subspace-complement statement, so I no longer describe my example as the resolution of an open question. The classification of all 512 complements and its Lean formalization are unaffected.

The stronger statement is the subspace-complement part of Question 8.1 of Ferguson and Iosevich, [*Fuglede's conjecture holds in eight dimensions over the field with two elements*](https://arxiv.org/abs/2610.36417) (arXiv:2610.36417).

## Overlap check against public problem records

On 31 October 2026 I compared nine results with public records found without correspondence. Eight were flagged by matching the arXiv identifiers cited in this collection against the problem dossiers in the `Problems/` directory of the Omega Institute's public repository [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing). The ninth is a Zenodo record. I read each dossier and the Zenodo record and compared their statements with mine. In every case the Omega record is dated before my first commit. Several records answer a different question from mine, and I list them because they are close.

How the dates were obtained:

- **Omega dates** are commit dates in the Git history of the Omega repository's default branch, read on 31 October 2026 and converted to UTC. Each link points to the dossier at its first commit.
- **Issue dates.** I could not retrieve the creation dates of the Omega issues. Where a commit message cites an issue, the commit date is an upper bound for the issue's creation; otherwise the issue existed by the date of the dossier that cites it.
- **My dates** are the first commits of each result in the earlier history of this repository, in UTC.
- **Public access.** A commit date does not by itself establish when a commit became publicly accessible, for either repository.
- **Lean proofs.** I have not checked the Omega Institute's Lean proofs and describe them as claimed.

| Result | Earlier public record | Record date (UTC) | My first commit (UTC) | Same question? | Answers |
|---|---|---|---|---|---|
| [Root-fidelity entropy bound](#omega-root-fidelity-entropy-bound) | Omega issue #19184 (audit issue #19212) | 19 Oct 2026, 23:57 (claimed Lean proof) | 29 Oct 2026, 03:22 | Yes | Agree |
| [Pure-state ECQC in dimension five](#omega-pure-state-ecqc-in-dimension-five) | Omega issue #12896 | 4 Oct 2026, 12:18 | 29 Oct 2026, 00:35 | Yes | Agree; same state |
| [Projection AM–GM](#omega-projection-amgm) | Omega issues #15647 and #17674 | 12 Oct 2026, 07:26 | 29 Oct 2026, 03:22 | Yes (#15647) | Agree; same witness |
| [Fully entangled fraction at fixed steering centre](#omega-steering-centre-bounds) | Omega issue #14206 | 8 Oct 2026, 12:27 | 29 Oct 2026, 03:22 | Yes, for my companion theorem | Agree |
| [CHSH value at fixed steering centre](#omega-steering-centre-bounds) | Omega issue #16558 | 14 Oct 2026, 08:40 | 29 Oct 2026, 03:22 | No; related quantity | Not compared |
| [Book-graph domination roots](#omega-book-graph-domination-roots) | Omega issue #23025 | 28 Oct 2026, 07:40 | 29 Oct 2026, 00:35 | Partly, for my companion proposition | Agree at n = 1 |
| [Unicyclic skewness](#omega-unicyclic-skewness) | Omega issue #22468 | 26 Oct 2026, 20:22 | 29 Oct 2026, 03:22 | No; unidirectional special case | Consistent |
| [DomiRank entropy](#omega-domirank-entropy) | Omega issue #13267 | 5 Oct 2026, 15:28 | 26 Oct 2026, 19:01 | No; broader assertion | Consistent |
| [Conditional hockey-stick contraction](#omega-conditional-hockey-stick-contraction) | Omega issue #17637 | 16 Oct 2026, 11:10 | 29 Oct 2026, 05:41 | No; general reduction | Consistent |
| [Thermal heat-current kurtosis](#zenodo-thermal-heat-current-kurtosis) | Zenodo 10.5281/zenodo.23689958 | 27 Oct 2026, 12:29 | 27 Oct 2026, 05:49 | Yes | Agree |

### Omega: root-fidelity entropy bound

Result: [The three-state root-fidelity entropy bound](papers/physics/fidelity-three-state/) (`fidelity-three-state`).

- **Earlier public record.** The [Omega dossier](https://github.com/the-omega-institute/trureturing/blob/81743e5d0ee1b300b9b36a2c3dbe15d05d39c993/Problems/fannes-demelo-roga-zyczkowski-2012-root-fidelity-holevo-bound.md) states Conjecture 1 of Fannes, de Melo, Roga and Życzkowski for three states of arbitrary dimension, including singular states and zero weights, and records a claimed Lean proof. The first commit with that proof, citing preregistration issue #19184, is dated 19 October 2026 at 23:57:03 UTC ([commit 40442e2](https://github.com/the-omega-institute/trureturing/commit/40442e237415d04ccfbdd856990fedfb757c713c)). The dossier followed on 21 October 2026 at 00:22:00 UTC. Issue #19212 concerns an unfinished audit of that proof, not the statement.
- **Same question, same answer.** Both prove the unrestricted three-state bound χ ≤ S(C). My first commit of this result is dated 29 October 2026 at 03:22:17 UTC ([commit 9459d04](https://github.com/dvgyl/math-and-theory/commit/9459d0497a0dd767f75f1e8897f3fe9939513bb5)), about nine days later. The two proofs have not been compared.
- **Relation to the correspondence above.** I do not know whether this record is the competing claim that Dr. Roga described, and I do not assume so.
- **My position.** I acknowledge the Omega Institute's earlier public record and make no priority claim for this bound.

### Omega: pure-state ECQC in dimension five

Result: [A pure-state matched-basis information inequality violation in dimension five](papers/physics/pure-ecqc/) (`pure-ecqc`).

- **Earlier public record.** The [Omega dossier](https://github.com/the-omega-institute/trureturing/blob/a47aa292ae5090e6c9681bf6d41c5e5f6e9b9dcf/Problems/iqbal-2025-pure-state-ecqc.md) refutes the pure-state specialization of Iqbal's ECQC inequality in dimension five, preregistered as issue #12896. Its first commit is dated 4 October 2026 at 12:18:20 UTC ([commit 9c1447c](https://github.com/the-omega-institute/trureturing/commit/9c1447c1efcf43c0ce89f28052a30c744fedbcee)), and the claimed Lean proof was frozen at 12:39:22 UTC the same day.
- **Same question, same answer, same certificate.** Both use the state 5^(−1/2) Σₓ |x⟩|2x mod 5⟩ with the source's six mutually unbiased bases, used identically by both parties, and obtain the classical sum 5 log 5 against the quantum mutual information 2 log 5. My first commit is dated 29 October 2026 at 00:35:21 UTC ([commit 7ae9c4e](https://github.com/dvgyl/math-and-theory/commit/7ae9c4ed830c47ad1282acd9ee0f5e0003f6c509)), about 25 days later. My conventional all-prime companion does not appear in the dossier.
- **My position.** I acknowledge the Omega Institute's earlier public record of the same counterexample and make no priority claim for it.

### Omega: projection AM–GM

Result: [An unbounded obstruction to projection AM–GM in Loewner order](papers/mathematics/projection-amgm/) (`projection-amgm`).

- **Earlier public record.** The [Omega dossier](https://github.com/the-omega-institute/trureturing/blob/b0a8d9a413a6aefee1b1aeb9fb084ddbe2798388/Problems/sun-luo-ye-2020-projection-matrix-amgm.md) refutes Conjecture 3.1 of Sun, Luo and Ye (issue #15647). Its claimed Lean refutation was committed on 12 October 2026 at 07:26:18 UTC ([commit b0a8d9a](https://github.com/the-omega-institute/trureturing/commit/b0a8d9a413a6aefee1b1aeb9fb084ddbe2798388)). A later addition, first committed on 20 October 2026 at 03:53:40 UTC, gives a six-dimensional counterexample with a prose proof and exact checker for the block-structured target of issue #17674, which keeps the nonsingular block structure of the coordinate-descent application.
- **Same question, same witness.** The rank-one projections onto (−1, 1, 1), (1, −1, 1) and (1, 1, −1) and the quadratic form −8/243 are the same in both. My first commit is dated 29 October 2026 at 03:22:17 UTC ([commit 9459d04](https://github.com/dvgyl/math-and-theory/commit/9459d0497a0dd767f75f1e8897f3fe9939513bb5)), about 17 days later.
- **Differences.** My theorem that no real multiplier C repairs the inequality, even with a positive-definite mean, does not appear in the dossier. The block-structured counterexample for #17674 addresses the structure that my note explicitly leaves aside.
- **My position.** I acknowledge the Omega Institute's earlier public refutation with the same witness and make no priority claim for the three-projection counterexample.

### Omega: steering-centre bounds

Result: [Exact three-setting correlation bounds at fixed steering centre](papers/physics/steering-bounds/) (`steering-bounds`).

- **Earlier public record, same statement.** My companion theorem f(ρ) ≤ 1 − c/2, sharp at every centre length, is Conjecture 2 of Milne, Jennings, Jevtic and Rudolph. The Omega Institute's [dossier](https://github.com/the-omega-institute/trureturing/blob/49e63cc2124d91dc82b3e463c6a0fe9b2cc2a6dc/Problems/milne-jennings-jevtic-rudolph-2014-fully-entangled-fraction.md) records a claimed Lean proof of it, with attainment for every centre length, committed on 8 October 2026 at 12:27:48 UTC (issue #14206). This record was not among the flagged rows; I found it because the dossier for issue #16558 cites it. My manuscript describes this theorem as a short consequence of a known canonical spectral bound and does not identify it as that conjecture.
- **Earlier public record, related question.** The [dossier for issue #16558](https://github.com/the-omega-institute/trureturing/blob/af41108edc85c119837189f120c6d2d9aa3f5a25/Problems/milne-jennings-jevtic-rudolph-2014-chsh-centre-bound.md), committed on 14 October 2026 at 08:40:22 UTC, proves Conjecture 1 of the same paper, a sharp bound on the CHSH value at fixed centre length. My main theorem concerns the three-setting value F₃² = ‖T‖²_F, a different quantity. I have not compared the two.
- **Dates.** My first commit is dated 29 October 2026 at 03:22:17 UTC ([commit 9459d04](https://github.com/dvgyl/math-and-theory/commit/9459d0497a0dd767f75f1e8897f3fe9939513bb5)).
- **My position.** I make no priority claim for the fully-entangled-fraction bound. The exact three-setting supremum does not appear in either dossier.

### Omega: book-graph domination roots

Result: [Sharp escape of complex domination roots in square flowers](papers/mathematics/graph-roots/) (`graph-roots`).

- **Earlier public record.** The [Omega dossier](https://github.com/the-omega-institute/trureturing/blob/1fc77bf09793a9d76147b2262c53fbcb3db2bd96/Problems/rather-2026-book-domination-root-conjecture.md) for issue #23025, committed on 28 October 2026 at 07:40:05 UTC, refutes Rather's Conjecture 5.4 on the real domination roots of book graphs. The failure is its n = 1 instance, the four-cycle, whose domination polynomial 6x² + 4x³ + x⁴ has zero as its only real root.
- **Partly the same question; answers agree.** My main theorem, on square flowers, is a different question. My companion book-graph proposition classifies the real roots for every n: zero is the only real root at n = 1, and for every n ≥ 2 the four real roots have the locations and multiplicities the conjecture describes. It therefore agrees with the Omega refutation at n = 1. The dossier states that it gives no general root classification. My first commit is dated 29 October 2026 at 00:35:21 UTC ([commit 7ae9c4e](https://github.com/dvgyl/math-and-theory/commit/7ae9c4ed830c47ad1282acd9ee0f5e0003f6c509)), about 17 hours later.
- **My position.** I acknowledge the earlier public refutation of the conjecture at n = 1 and make no priority claim for it.

### Omega: unicyclic skewness

Result: [A sharp universal skewness bound for unicyclic currents](papers/physics/unicyclic-skewness/) (`unicyclic-skewness`).

- **Earlier public record, related question.** The [Omega dossier](https://github.com/the-omega-institute/trureturing/blob/036cdd4840c6bd823af165fa3c6db3ea6a790929/Problems/ptaszynski-2022-unicyclic-skewness-minimum.md) for issue #22468, committed on 26 October 2026 at 20:22:23 UTC, proves Ptaszyński's numerically conjectured minimum skewness for unidirectional cycles. It gives the exact minimum for every number of states and, in prose, −1/16 as the infimum over all state counts.
- **Not the same question.** My theorem concerns bidirectional rings with positive forward and reverse rates and proves both sides of the interval −1/16 ≤ C₃/C₁ ≤ 1, each sharp. The two results agree on −1/16 as the lower constant. My first commit is dated 29 October 2026 at 03:22:17 UTC ([commit 9459d04](https://github.com/dvgyl/math-and-theory/commit/9459d0497a0dd767f75f1e8897f3fe9939513bb5)), about 31 hours later.
- **My position.** I acknowledge this earlier result on the unidirectional case.

### Omega: DomiRank entropy

Result: [An entropy increase for a structurally disassortative DomiRank graph](papers/mathematics/domirank-entropy/) (`domirank-entropy`).

- **Earlier public record, broader assertion.** The [Omega dossier](https://github.com/the-omega-institute/trureturing/blob/3a5b8280cfdf4a7cf1f5002f6a503d10f741614d/Problems/zhang-zhao-2026-domirank-entropy-monotonicity.md) for issue #13267, committed on 5 October 2026 at 15:28:47 UTC, refutes the unconditional assertion of Remark 4.6 in version 1 of Zhang and Zhao's paper, that entropy decreases for every connected nonregular graph, with a six-vertex graph.
- **Not the same question.** My counterexample refutes Conjecture 4.9 of version 4, which assumes a structurally disassortative graph. The six-vertex graph has positive degree–log-degree covariance, so it does not satisfy that hypothesis. The answers are consistent. My first commit is dated 26 October 2026 at 19:01:06 UTC ([commit 568a20f](https://github.com/dvgyl/math-and-theory/commit/568a20f7e29db12a7890f695a296734780ce71c5)).
- **My position.** I acknowledge the earlier refutation of the broader assertion.

### Omega: conditional hockey-stick contraction

Result: [Exact conditional contraction for Pauli channels and depolarization in every dimension](papers/physics/quantum-exact-contraction/) (`quantum-exact-contraction`).

- **Earlier public record, general reduction.** The [Omega dossier](https://github.com/the-omega-institute/trureturing/blob/f348745a18aa2378c90384044b5d5b4d79744e20/Problems/hirche-george-nuradha-wilde-2026-conditional-hockey-stick-orthogonal-reduction.md) for issue #17637, committed on 16 October 2026 at 11:10:17 UTC, answers the question in Section 9 of Hirche, George, Nuradha and Wilde. It claims that, for every channel between finite systems, the conditional hockey-stick coefficient is optimized by orthogonal states and equals the conditional trace-distance coefficient for every γ ≥ 1.
- **Not the same question.** My result gives exact values for every stochastic Pauli qubit channel and for depolarization in every dimension. The independence of γ in my formulas is a special case of the general theorem in the dossier, which does not compute these values. My first commit is dated 29 October 2026 at 05:41:03 UTC ([commit 05b3d2b](https://github.com/dvgyl/math-and-theory/commit/05b3d2bc00fe96ff335deca3d8d43812012a7fc0)).
- **My position.** I acknowledge the earlier general result, which covers the γ-independence of my formulas.

### Zenodo: thermal heat-current kurtosis

Result: [A three-state thermal counterexample to a heat-current kurtosis conjecture](papers/physics/thermal-kurtosis-counterexample/) (`thermal-kurtosis-counterexample`).

- **Public record.** The Zenodo record [10.5281/zenodo.23689958](https://doi.org/10.5281/zenodo.23689958), by an anonymous creator, was created on 27 October 2026 at 12:29:01 UTC. It gives three-state, two-bath counterexamples to Ptaszyński's conjectured signs C₃/C₁ ≥ 0 and C₄/C₂ ≥ 0, with both ratios tending to minus infinity.
- **Same question, same answer.** My result is a single exact counterexample to the sign of C₄/C₂. The Zenodo record goes further, also refuting the sign of C₃/C₁ and showing that both ratios are unbounded below.
- **Chronology.** My first commit of this result is dated 27 October 2026 at 05:49:04 UTC ([commit eac07aa](https://github.com/dvgyl/math-and-theory/commit/eac07aa986dbe577b7dc7a02661626a20bbda7ba)), about 6 hours 40 minutes before the Zenodo record was created. This is a chronological note, not a priority claim. A commit date does not establish public access.

## Other correspondence

These exchanges concern review, not priority. I record them so that they are not mistaken for endorsement.

- **Keller–Klein small-coefficient bound** ([`keller-klein`](papers/mathematics/keller-klein/)). On 30 October 2026, Nathan Keller expressed interest in reviewing this work. He has not reviewed or validated the proof, and his interest is not an endorsement of it.
- **Last-gradient bound for gradient descent** ([`strong-gradient`](papers/mathematics/strong-gradient/)). On 30 October 2026, Salah Chikhi offered to examine this result. He has not validated the proof, and his offer is not an endorsement of it.

## What changed in the repository

- Each of the six project READMEs has a section "Priority and subsequent correspondence".
- Each of the six manuscripts has a dated note with the same information, and I corrected statements that the new information no longer supports:
  - the Higuchi–Sudbery manuscript no longer presents the bound as its own contribution;
  - the density-one-eighth manuscript no longer states that it closes the open gap or that the bound is its contribution;
  - the binary spectral tile manuscript no longer describes the example as resolving an open question or treats the open question as evidence of novelty, and it records the provisional AI-generated comparison.
- The Keller–Klein and gradient-descent READMEs note the review interest described above, without implying endorsement.
- [README.md](README.md), [CONTENTS.md](CONTENTS.md), the [catalogue](catalogue.json) and the research website link each affected result to this record.
- On 31 October 2026, the READMEs of the nine results in the public-record check gained a section "Earlier public work", and their catalogue entries, [CONTENTS.md](CONTENTS.md) entries and website pages link to it. Their manuscripts are unchanged; this record and the READMEs carry the corrections.
- No proof, Lean formalization, verification record or AI disclosure was removed. Earlier versions of every changed file are in the Git history.
