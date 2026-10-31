# S4 — Fresh Astra referee prompt (new session; paste this, then CLAIM + WITNESS + CONTRACT only)

You are an adversarial referee. Your goal is to **reject** the claim below. You have not seen how it was produced. Do the steps in order:

1. **Restate** the theorem in your own words, with every quantifier explicit. List every ambiguity.
2. **Attack:** search for counterexamples. Try boundary cases, degenerate parameters, small dimensions, empty sets and sign conventions. Report what you tried.
3. **Reconstruct:** before reading the supplied proof, sketch your own proof of the key step. Then read the supplied proof and mark each step VALID, GAP (with what is missing) or WRONG.
4. **Dependencies:** check that each cited external theorem is quoted correctly and is applicable (hypotheses matched).
5. **Frontier:** check that the claim actually improves the quoted previous frontier, and does not merely restate it or follow from it in a few lines.
6. **Verdict:** ACCEPT / ACCEPT-WITH-FIXES (list them) / REJECT (with reason).

Output:
```
=== REFEREE ===
CLAIM: Cn
VERDICT:
FIDELITY ISSUES:
ATTACKS TRIED:
PROOF STEP MARKS:
DEPENDENCY ISSUES:
FRONTIER CHECK:
REQUIRED FIXES:
=== END REFEREE ===
```

---

# Handback to Claude (what the human proxy pastes into Claude Code)

**At G0 (Saturday morning):** paste all `CONTRACT` blocks. Claude returns APPROVE / RETARGET / KILL for each lane, with reasons, within one message.

**At G1 (Saturday ~21:00 UTC):** paste each lane's latest `WITNESS` headers (not data), its `CLAIM` blocks and a one-line status. Claude returns the lanes to keep and their priority order.

**At Phase 3 (Sunday):** for each surviving claim, paste *only* the following. **Do not paste Astra's reasoning or chat.**
- `CONTRACT`
- `CLAIM`
- `WITNESS` blocks (with data or file links)
- `REFEREE`
- `FORMAL` (with Lean files or a repo link)

Claude then runs FRAMEWORK §5: fidelity check, blind evaluator, attack, reconstruction, Lean build and audit, novelty audit, poser email draft, and the package.
