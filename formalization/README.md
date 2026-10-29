# Proof source

This directory contains all 35 original proof modules. They have been ported to Lean's module system. The current revision requires the official full Palomar preflight. The dependency pins remain Lean 4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The active Lake project is now in the parent directory. Run its commands from that project root. [The root README](../README.md) gives the commands. [The verification scope](../VERIFICATION.md) distinguishes the selected formal statements from conventional manuscript corollaries.

[THEOREMS.md](THEOREMS.md) maps the mathematical statements to source declarations. `src/CompleteAudit.lean` imports the complete proof closure and requests 25 axiom reports. `expected-axioms.json` is the original list of expected reports and permitted axioms. Neither file is current compiler evidence.

The independent Challenge has three deliberate theorem holes. Solution imports the complete proof source without importing Challenge. The original source hash manifests and verifier scripts were removed because they do not certify the ported source. The current integrity inventory is [source-sha256.json](../source-sha256.json).

[NOTICE](NOTICE) preserves the original source credit. [LICENSE](LICENSE) contains the Apache License 2.0.

This work is fully autonomous agentic research. GPT 6.1 Sol in Codex produced formal proofs and verification software for this package. I am responsible for publication.
