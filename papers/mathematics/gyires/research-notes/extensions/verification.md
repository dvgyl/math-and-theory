# Reproduce the all-order Gyires certificates

The programs use the Python and Node.js standard libraries. The reproduction environment uses Python 3.14.6 and Node.js 22.23.2. The [source manifest](../../../../../verification/records/source-hashes.json) identifies the program and output files.

## Commands

From the repository root, create an output directory outside the source tree:

```sh
certificate_dir="$PWD/papers/mathematics/gyires/research-notes/extensions/certificates"
mkdir -p ../gyires-certificate-run
cd ../gyires-certificate-run
python3 "$certificate_dir/sharp_bound_check.py"
python3 "$certificate_dir/circ_small_check.py"
node "$certificate_dir/independent_finite.mjs" 93
mv independent_finite.json permutation-alternative-finite.json
node "$certificate_dir/independent_finite.mjs" 47
```

The programs write JSON reports in the output directory. Compare their mathematical fields with the [recorded outputs](results/summary.json). Timing fields can change.

From the repository root, check the regenerated report coverage with:

```sh
python3 verification/check_gyires_certificates.py --extensions ../gyires-certificate-run
```

The checker requires the two stated finite ranges, each with all three chambers in every order. It also checks the other stored Gyires publication reports. It rejects incomplete ranges, duplicate chambers, and failed or sampled results. This report check does not rerun the coefficient arithmetic.

## Completed checks

The recorded run checked 135 reflection-reduced chambers in orders 3 through 47. It checked 224,550 coefficient positions with exact integers. No coefficient was negative. Every coefficient was positive in orders 4 through 47. The small-order program matched direct permanents to both transfer formulas in orders one through seven. Its six gap orderings passed in orders three and four.

The appendix also gives two alternative spectral bounds. Their finite checks extend through orders 69 and 93. The report `permutation-alternative-finite.json` covers orders 3–93, with 273 chambers and 1,674,309 coefficient positions. All decisive coefficients are nonnegative. This single report covers both alternative ranges.

The sharp-bound program checked the residual factorization in Q(sqrt(2)), its positive decomposition, and the exact threshold at order 48. The written argument proves the monotone tail after that threshold. The finite coefficient check alone does not prove an all-order theorem.

The file `circ_transfer.py` supplies transfer routines to the small-order checker. Its standalone mode checks the requested finite range. Every negative coefficient or incomplete requested range causes a nonzero exit code. Python programs that use assertions reject optimization with `-O` or `PYTHONOPTIMIZE`.

The [four-block argument](four-block.md) is analytic. It uses the Bernoulli likelihood bound and exact permanent identities. No finite computation is presented as proof of that all-order statement.

## Verification limits

The four-block theorem has a complete Lean proof. The Gyires Comparator configuration selects its four principal statements. The separate permutation-polynomial package proves the actual matrix theorem in every dimension. No Palomar registry approval is claimed.
