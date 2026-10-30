# Priority and novelty disclosures

This record was written on 30 October 2026. It documents five results in this collection for which I learned of overlapping or earlier work through correspondence with researchers in the field after I had published them. In each case the information reached me only through that correspondence. My agents' original novelty searches did not find this work, and I was not aware of it when I first published the result.

These are scholarly priority disclosures, not retractions. Overlapping or earlier work does not by itself invalidate a mathematical proof. The proofs, Lean formalizations and verification records of all five results are unchanged. Where a manuscript made an originality claim that the new information no longer supports, I have corrected it; the earlier versions remain in the Git history of this repository.

I summarize private correspondence factually and only to the extent needed here. I do not quote it.

## How to read these disclosures

I distinguish four kinds of information:

- **Prior public work**: results or claims that were publicly available before my publication, with a public source I can cite.
- **Private communication**: information a researcher told me in correspondence. I report it as what I was told and have not seen the underlying work unless I say so.
- **Competing claim**: a reported solution by another person or group that I have not seen or checked.
- **Established mathematical equivalence**: a comparison of the actual mathematical content that shows two results or certificates agree. Only one of the five cases has this.

| Result | Correspondence | What I learned | Kind | Equivalence | My position |
|---|---|---|---|---|---|
| [Higuchi–Sudbery entropy bound](#higuchisudbery-four-qubit-entropy-bound) | Dr. Jef Pauwels, 30 October 2026 | The Omega Institute registered the problem on 5 October 2026 and committed a claimed Lean proof on 7 October 2026 | Prior public work | Certificates algebraically equivalent | No originality or priority claim |
| [Kovačec polygon enclosure](#kovačec-polygon-enclosure) | Professor Alexander Kovačec, 29 October 2026 | His own counterexample from June 2026 in an unpublished preprint; another counterexample sent to him by Wenlin Zhang | Private communication; competing claim | Not established | Earlier discoveries acknowledged; no priority claim |
| [Root-fidelity entropy bound](#three-state-root-fidelity-entropy-bound) | Dr. Wojciech Roga, 29 October 2026 | Another group claimed to him, several days earlier, a solution using AI and Lean | Private communication; competing claim | Not compared | Competing claim acknowledged; neither equivalence nor priority established |
| [Power ranks](#power-ranks-of-a-constant-recursive-sequence) | Professor Eric Rowland, 29 October 2026 | His own infinite family of rank sequences for rank-three recurrences, obtained while experimenting with an LLM | Private communication; independent overlapping result | Not compared | Overlap acknowledged; no duplication implied |
| [Binary spectral tile](#binary-spectral-tile-in-dimension-nine) | Dr. Samuel Ferguson, 30 October 2026 | He and Professor Joshua Iosevich knew of counterexamples to the stronger statement shortly after submitting their arXiv paper | Private communication | Not established | Their prior awareness acknowledged |

## Higuchi–Sudbery four-qubit entropy bound

Result: [A sum-of-squares proof of the four-qubit Higuchi–Sudbery entropy bound](papers/physics/higuchi-sudbery/) (`higuchi-sudbery`), first published in this repository on 27 October 2026.

On 30 October 2026, following my correspondence with Dr. Jef Pauwels, he informed me that the Omega Institute had recently announced a similar result. I was previously unaware of this work. When I investigated, I found that the Omega Institute had registered the problem on 5 October 2026 and publicly committed a claimed Lean proof on 7 October 2026 ([public record](https://github.com/the-omega-institute/trureturing/issues/13454)). A subsequent comparison showed that their 272-term sum-of-squares certificate and mine are algebraically equivalent.

- **Prior public work.** The Omega Institute's registration of the problem and its claimed Lean proof were public before my publication on 27 October 2026.
- **Established equivalence.** The two 272-term sum-of-squares certificates are algebraically equivalent, so the overlap with my result is substantial. I have not independently checked the Omega Institute's Lean proof, and I describe it as claimed.
- **My position.** I acknowledge the Omega Institute's earlier public work and make no originality or priority claim for this result. My manuscript, Lean formalization and verification records remain available as an independent derivation and check of the bound.

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

- **Private communication.** Their awareness of counterexamples was reported to me in correspondence; I have not seen their examples.
- **Equivalence not established.** It has not been established whether their examples are equivalent to my 64-point construction.
- **My position.** I acknowledge their prior awareness of counterexamples to the stronger subspace-complement statement, so I no longer describe my example as the resolution of an open question. The classification of all 512 complements and its Lean formalization are unaffected.

The stronger statement is the subspace-complement part of Question 8.1 of Ferguson and Iosevich, [*Fuglede's conjecture holds in eight dimensions over the field with two elements*](https://arxiv.org/abs/2610.36417) (arXiv:2610.36417).

## What changed in the repository

- Each of the five project READMEs has a section "Priority and subsequent correspondence".
- Each of the five manuscripts has a dated note with the same information, and I corrected statements that the new information no longer supports:
  - the Higuchi–Sudbery manuscript no longer presents the bound as its own contribution;
  - the binary spectral tile manuscript no longer describes the example as resolving an open question or treats the open question as evidence of novelty.
- [README.md](README.md), [CONTENTS.md](CONTENTS.md), the [catalogue](catalogue.json) and the research website link each affected result to this record.
- No proof, Lean formalization, verification record or AI disclosure was removed. Earlier versions of every changed file are in the Git history.
