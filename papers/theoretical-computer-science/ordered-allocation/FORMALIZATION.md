# Manuscript and formal statement map

The source file is `OrderedAllocationReduction.lean`. The source pins Lean 4.19.0 and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Definitions

`OrderedReductionCompletion.multiplicity`, `extraCopies`, `totalCopies`, and `utility` are the paper's multiplicity, maximum of multiplicity minus one and zero, total extra-copy count, and additive utility. Lean subtracts natural numbers with truncation at zero. Thus `multiplicity A g - 1` is exactly the paper's extra-copy convention, including unused goods.

An allocation has type `Agent → Finset Good`, so bundles are sets. Each ranking has type `Good ≃ Fin (Fintype.card Good)` and is a bijection. The ordered-value condition is `Antitone (fun j => v i ((rank i).symm j))`. The formal theorem separately assumes every real weight is nonnegative.

The paper uses ranks `1,...,m`; Lean uses `0,...,m-1`. Eligibility is the same order comparison after adding one to a Lean index. In the counting proof, the number of ranks from prefix length `s` through maximum zero-based index `a` is `a+1-s`; this is the paper's `a_i-s` with one-based `a_i`.

## Main endpoints

| Manuscript result | Exact declaration |
|---|---|
| Theorem 1: utilities, exact extra copies, per-good cap, full coverage | `OrderedReductionAllocation.ordered_allocation_transfer_exact` |
| Corollary 2: total and per-good budgets | `OrderedReductionAllocation.ordered_allocation_transfer` |
| Corollary 2: achieved utility thresholds | `OrderedReductionAllocation.ordered_threshold_transfer` |

The exact endpoint assumes a nonempty finite agent type, a finite good type (including an empty one), nonnegative real weights, decreasing-value ranking equivalences, arbitrary finite-set ordered bundles, and a natural per-rank extra-copy cap. It has no total-budget hypothesis because it preserves the actual count exactly. The budget theorem adds `totalCopies A ≤ t`. The threshold theorem adds agent-specific achieved real thresholds. Its statement omits explicit coverage and exact-count conclusions, which follow from the stronger exact theorem used in its proof.

## Supporting argument

| Paper component | Exact declaration or definition |
|---|---|
| Completion without new extra copies | `OrderedReductionCompletion.complete`, `extraCopies_complete`, `totalCopies_complete` |
| Utility increase under completion | `OrderedReductionCompletion.utility_complete_ge` |
| Prefix-count bounds, Lemma 3 | `OrderedReduction.prefixSlots_card_bounds` |
| Rank-count inequality, Lemma 3 | `OrderedReduction.rank_count` |
| Left/right graph classes and edges | `OrderedReduction.HallGadget.Left`, `Copies`, `Right`, `Edge` |
| Hall matching existence | `OrderedReduction.HallGadget.exists_bijective_gadget` |
| Matching-to-assignment extraction | `OrderedReduction.HallGadget.exists_assignment_of_bijective_gadget` |
| Completed ordered slots transfer | `OrderedReduction.ordered_slots_transfer` |
| Allocation and utility extraction | `OrderedReductionAllocation.allocation_from_slot_assignment` |
| Transfer for covered input | `OrderedReductionAllocation.complete_allocation_transfer` |

In rows with a namespace shown only once, every comma-separated declaration belongs to that namespace. Surjectivity of the perfect matching is essential: it ensures every primary-copy vertex is used and hence every actual good is assigned.

Proposition 4, the polynomial-size graph and standard matching-algorithm consequence, is a conventional argument. The supplied Lean source does not formalize an executable matching implementation or its runtime. The two-agent numerical example is an elementary illustration added to the manuscript, not a separate Lean endpoint.

## Reproduction and limits

Follow the README commands in `formalization/`. A fresh Lean 4.19.0 replay succeeded on 28 October 2026 for the import-only variant. It uses `Mathlib.Tactic` and `Mathlib.Combinatorics.Hall.Finite` in place of the umbrella `Mathlib` import; the proof body is unchanged. The previously checked import-only source, before the comment-only source-context repair, has SHA-256 `98fbc8b20c1eb589cb1ceae39196ad2f3d52e84e4f93a3d9f877b43b8ff3f6c2`.

A separate `--trust=0` audit checked the three original endpoints and `OrderedAllocationIndependentAudit.exact_transfer_expanded`, which expands utilities, multiplicities, extra-copy sums, and the ordered-value condition. Its four complete reports contain only `propext`, `Classical.choice`, and `Quot.sound`. All four required reports were accepted. Five existing unused-section-variable warnings concern intermediate declarations; the replay is not claimed to be warning-free.

Fresh checking establishes the stated proof and its axiom dependencies. It does not establish novelty, source fidelity to the motivating paper, external expert validation, or peer review.

The publication copy changes only the opening source-context comment. All non-comment bytes match the previously checked source; no formal theorem, proof, import, or definition changed. No new Lean run is claimed for that comment-only delta.
