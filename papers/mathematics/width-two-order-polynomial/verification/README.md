# Fresh replay record

This directory records the verification of this package run for its publication on 31 October 2026.

- [`build.log`](build.log): `lake build ShortChain ShortChain.AxiomAudit` in a copy of `lean/` with no project build output, using Lean 4.35.0 on Linux x86_64 and a prebuilt Mathlib at revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. All three project modules, the root module and the audit module were compiled; the kernel checks of the 22 chambers in `ShortChain.Data` took 254 seconds and the whole project build 272 seconds.
- [`axiom-inventory.json`](axiom-inventory.json): the output of `scripts/check_axiom_audit.py` on that log. All 238 declarations defined in the project modules, including generated and auxiliary ones, depend only on `propext`, `Classical.choice` and `Quot.sound`.
- [`certificate-check.json`](certificate-check.json): the output of `certificate/check_certificates.py --extra 3` with Python 3 in isolated mode: 64 chambers, 1,072 squares, 194,112 point identities, 636 degree-one coefficients, 192 further random points, three rejected corrupted certificates and the three worked examples.

`scripts/generate_lean_data.py --check` confirmed that `lean/ShortChain/Data.lean` matches the certificate files. The original research package's verifiers, including its separate referee reconstruction, were also rerun and passed; they are not included. The CI workflow repeats the Lean build, the audit, the Lean-data check and the certificate checker on every push.
