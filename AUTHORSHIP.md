# Authorship and review

Dev D. Goyal directs the research and is responsible for publication. He selects problems and requests proofs, formal verification, and revisions. He does not provide proof ideas or intermediate mathematical arguments for the AI-generated results in this collection.

**ChatGPT (OpenAI), using the GPT-6 model with Pro reasoning**, developed the proposed proofs and Lean formalizations under his direction. The order-five Gyires records also identify **Claude Opus 5.5, used with Claude Code**, as a contributor to those proofs and their review. The source notices identify the reused work.

**Codex, using GPT-6**, checked the mathematics and searched the prior literature. It migrated the proofs to Lean 4.35, added source-definition proofs and matching statement modules, wrote independent checking programs, and revised the manuscripts and repository documentation. It completed the all-budget sampling extension and the Motzkin source-definition proof.

The [Gyires preprint](preprints/gyires-circulant-five/paper.pdf) contains the order-five circulant proof and broader matrix and polynomial results. Codex checked the arguments and exact certificates and edited the manuscript. The [supporting research record](research-notes/gyires-complete-support/README.md) preserves the source texts and their hashes. Lean verification and independent human expert review of the broader arguments remain incomplete. The [Gyires manuscript review](preprints/gyires-circulant-five/review.md) has its own scope.

A separate **GPT-6.1 Sol** referee completed two mathematical and editorial review passes on the seven formalized families. It inspected the corrections and local verification records, then approved publication with no blocking criticism. The [review record](verification/review.md) identifies the reviewed commit and states the scope and limits of that approval.

The [collection editorial review](verification/collection-editorial.md) records the later revision of all seven manuscripts and current guides. It separates the document checks from earlier mathematical and formal verification.

Dev D. Goyal's recorded personal review concerns the earlier order-five Gyires proofs. It must not be extended to new source statements, new Challenge modules, new proofs, or revised manuscripts. No independent human expert review of this collection is claimed.

Lean checks proof terms against formal statements. Comparator compares the separately stated Challenge with the proved Solution. NanoDa and con-ron provide additional proof checking where the pinned toolchain supports them. These checks do not establish that a source statement was transcribed correctly or that a result is new. Those questions require a separate mathematical and literature audit.

These papers have not been peer reviewed by human experts. No unconditional novelty or priority claim is made. Each paper credits the original problem and the prior results used in its proof.
