# A sharp universal skewness bound for unicyclic currents

**This work is fully autonomous agentic research.** AI systems autonomously generated and developed the research, proofs, formalizations, corrections, and manuscript. I, Dev D. Goyal, am responsible for publication. I do not claim expert human validation or peer review.

I prove the sharp interval

$$
-\frac1{16}\le \frac{C_3}{C_1}\le 1
$$

for the net crossing count of one marked edge of a finite bidirectional Markov ring. Here `C_k` is the `k`th long-time cumulant per unit time. This ratio is not standardized skewness. The ring has at least three states, all forward and reverse rates are strictly positive, and their products differ. The two-state model needs two distinguished channels and has the stronger interval `[1/4,1]`. The one-state counted-event convention gives the ratio `1`.

The main result proves the interval proposed by K. Ptaszyński, *Physical Review E* **106**, 024119 (2022), Eq. (21), [doi:10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). The proof combines known midpoint-spectrum and uncertainty results with an exact polynomial inequality. Those supporting results and the known limiting family receive credit in the manuscript. Bibliographic priority remains subject to further literature comparison.

## Read and reproduce

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Formalization map](FORMALIZATION.md).
- [Lean source](proof/AllResults.lean): all 34 local source modules are required.
- [Exact certificate](certificate.json), with complete integer tables in the manuscript.
- [Verification manifest](verification/verification.json) and [compiler output](verification/UnicyclicAll.log).

The Lean target proves the interval for the actual tilted-matrix derivatives and constructs a local branch. The manuscript gives conventional proofs that identify those derivatives with long-time stochastic cumulants and establish sharpness. Lean does not construct a continuous-time sample-path probability space or prove a separate optimizing-sequence theorem.

Install Lean **4.19.0** and mathlib revision **c44e0c8ee63ca166450922a373c7409c5d26b00b**, including its dependency cache. The exact Lake configuration, lock, and toolchain pin are in `proof/`. Then run:

```bash
python3 verify.py --mathlib /path/to/mathlib4 \
  --lean-bin /path/to/lean-4.19.0-linux/bin --output verification
python3 check_certificate.py
```

The first command checks the complete source in one process, imports only external libraries, and returns a nonzero status on any failed check. The accepted axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The second command requires SymPy and independently expands every integer certificate and the polynomial reduction identities.

To build the manuscript, run `pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex` twice. The checked reading copy uses pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian).

The source uses the repository's Apache-2.0 license. Imported Lean libraries retain their own licenses and source credit.
