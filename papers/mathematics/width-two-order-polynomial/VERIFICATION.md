# Verification

## Certificates

The certificate files in [certificate/data/](certificate/data/) are xz-compressed JSON: `SHORT_CHAIN_CERTIFICATE.json.xz` lists the chamber polynomials `F_{a,w}` for `a ≤ 3` by their integer monomial coefficients, and `GAP_SOS_A4.json.xz` and `GAP_SOS_A5.json.xz` give, for each chamber with `a = 4, 5`, the polynomial, the nonnegative remainder and the squares `weight · x^multiplier · (ratio · x^u − x^v)²` with exact rational entries. From this directory, with Python 3.10 or later and no other software,

```sh
python3 certificate/check_certificates.py --extra 3 --json certificate-check.json
```

checks, in about a minute: the chamber list for each `a ≤ 5` is exactly the set of Dyck words; every polynomial has `2a + 1` variables, total degree at most `a` and no constant term; positive integer coefficients for `a ≤ 3`; for `a = 4, 5`, nonnegative weights and remainder coefficients and exact reconstruction of the polynomial from squares and remainder; equality of the polynomial with `(a + b)! [t]Ω_P(t)/(b − 1)!` at all 194,112 integer gap vectors with gap sum at most `a`, where `Ω_P(m)` is computed from scratch by counting multichains of order ideals and the linear coefficient is taken from finite differences (no rook numbers are used); the degree-one remainder coefficients `(a − 1)!` behind the lower bound; agreement at three further random gap vectors per chamber with gap sum above `a`; rejection of three corrupted certificates; and the three worked examples of the manuscript. Section 4 of the manuscript explains why these finitely many identities determine the chamber polynomials for every length of the long chain. The checker is executable evidence, not a formal proof.

## Lean

The Lean project in [lean/](lean/) pins Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then from this directory, in a fresh copy of the package:

```sh
bash scripts/verify.sh /tmp/width-two-verification
```

The script first checks with [generate_lean_data.py](scripts/generate_lean_data.py) that [Data.lean](lean/ShortChain/Data.lean) is exactly the Lean rendering of the certificates for `a ≤ 4` (integer data scaled by a common denominator per chamber), downloads the Mathlib cache, refuses to run if the project already has build output, builds `ShortChain` and `ShortChain.AxiomAudit`, checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py) and runs the certificate checker. `ShortChain.AxiomAudit` enumerates every declaration whose defining module is one of the three project modules, including private and generated ones, and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`. The kernel checks of the 22 chambers take about four minutes.

`ShortChain.Chamber.valid` is the Boolean certificate test, evaluated by `decide +kernel`; its soundness theorems in [Poly.lean](lean/ShortChain/Poly.lean) evaluate polynomials in an arbitrary linearly ordered field, so the conclusions apply to real gap vectors. [theorem-map.json](theorem-map.json) lists the declarations for each result. The identification of the chamber polynomials with the linear coefficient of the order polynomial, the chambers with `a = 5` and the reduction to the linear coefficient are not formalized.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats the Lean build, the audit, the Lean-data check and the certificate checker on every push. Formal verification does not establish novelty or priority.
