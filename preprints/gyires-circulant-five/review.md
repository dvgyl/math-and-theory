# Review of the continuous Gyires preprint

This record concerns the integrated preprint *Gyires's permanent inequality for structured matrices*, dated 26 October 2026. It combines the earlier order-five theorem with the all-order permutation-polynomial and four-block arguments. The public baseline is commit `b7e67bf67df0e2476a499f2de5df3cb274672484`.

## Mathematical scope

The principal order-five statements have complete Lean proofs. The two all-order arguments are ordinary proofs with incomplete Lean verification. The permutation proof includes exact polynomial certificates for orders 3 through 47 and an analytic bound for every order at least 48. The four-block proof is analytic and includes unequal block sizes, boundary entries, and the Gyires equality case.

The integration preserves the earlier source notes, five certificate files, their recorded outputs, and all Lean inputs. It adds one shared permanent coefficient identity and uses that identity throughout the combined argument. The directory name remains stable for existing links.

## Independent AI review

Two separate GPT-6.1 Sol review passes are complete. Both approved publication under the verification limits stated here. No blocking mathematical defect or unresolved review finding remains.

The first pass identified an omitted nonnegative-entry condition in the abstract and a reference to a removed conjecture label. Both were corrected. The body theorem already had the correct nonnegative hypothesis.

The first pass checked the transfer bijection, both transfer matrices, the spectral vector and factorization, the analytic tail, the finite recurrence interpretation, and the cycle constants. It also checked the shared coefficient identity, the Bernoulli extremal reduction, the likelihood bound, the contraction proof, the equality case, and all stated boundaries. Exact determinant, algebraic residual, integer threshold, certificate-record, and reference-key checks passed. Comparison with the baseline confirmed that the order-five proof content is preserved.

The second pass independently checked the integrated mathematics, the preserved order-five argument, the transfer and probability calculations, and the public verification scope. It found a stale five-file document-hash record. All five hashes were updated, and the reviewer verified the correction. The second pass then approved publication.

## Artifact checks

The 27-page preprint and four-page collection overview compiled with Tectonic 0.17.0. Their final logs have no unresolved references, citation warnings, or layout warnings. Every page was rendered and visually inspected. No clipping or missing mathematical glyphs was found. The PDF hashes are recorded in the central PDF record.

The new exposition does not change the Lean source or exact certificate programs. The earlier formal and certificate checks retain their stated historical scope. No new Lean build or independent-kernel run is claimed for this editorial revision.

AI review does not constitute independent human expert review or peer review. The preprint makes no novelty or first-priority claim. Its source-access limits remain explicit.
