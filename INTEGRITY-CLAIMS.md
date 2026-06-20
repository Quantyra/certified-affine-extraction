# Integrity & Claims Ledger

**Scope:** this document states, precisely and conservatively, what this repository proves and what it
does **not**. Every axiom profile below was read directly from the Lean kernel via `#print axioms`
(toolchain `leanprover/lean4:v4.13.0`) and is pinned (`lean/CertifiedAffine/Audit.lean`).

## Non-claims (hard boundary)

This repository does **not** establish or imply, and makes **no** claim toward:

- P = NP or P ≠ NP;
- any NP or circuit lower bound;
- a general CNF / SAT → XOR (GF(2)) reduction.

It is scoped to **certified, search-free, semantically-verified affine/GF(2) extraction for specific
Tseitin families** (uniform directed cycles, plus generic helpers). That is the whole of the claim.

## What is proven

| Declaration | What it says | Axioms | Kind |
|---|---|---|---|
| `…AtomicClassBridge.extractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate` | For every non-degenerate `n`, the canonical-fingerprint splitter recognizes the uniform Tseitin **cycle** CNF residual-free and yields its GF(2) parity blocks. **General over `n`** (no `native_decide`). | propext, Classical.choice, Quot.sound | **General theorem (the real content)** |
| `…ExtractorCompleteness.extractorCompleteOn_{threeCycle,fourCycle,cycle5,cycle6}` | The executable splitter's residual-free output equals the extracted GF(2) target, at `n = 3,4,5,6`. | + `Lean.ofReduceBool` | Concrete instances (`native_decide`) |
| `…ExtractorCompleteness.semanticExtractorCompleteOn_{threeCycle,fourCycle,cycle5,cycle6}` | The above **plus** per-assignment CNF ↔ GF(2) equivalence. | + `Lean.ofReduceBool` | Concrete instances (`native_decide`) |
| `…ExtractorCompleteness.extractorCompleteOn_of_residualFree` | Generic reduction: a residual-free split implies extractor completeness. | (none) | Axiom-free helper |
| `…AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormula_of_privateIncident_degreePos` | Reusable graph-local private-incident sufficient condition for semantic extractor completeness over Tseitin CNF formulas, assuming positive degree. | propext, Classical.choice, Quot.sound | General bridge theorem |
| `…AtomicClassBridge.path3_privateIncidentWitnesses` | Concrete private-incident witness package for the path P3. | propext, Quot.sound | Non-cycle witness data |
| `…AtomicClassBridge.semanticExtractorCompleteOn_path3_privateIncident` | P3 semantic extractor completeness routed through the private-incident bridge and public surface. | propext, Classical.choice, Quot.sound | Non-cycle witness theorem |
| `…AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_append_sameSupportComponents_of_keyDisjoint` | Two generated same-support collision components compose through the no-search fallback splitter when their canonical support keys are disjoint. The concrete `…twoDisjointTwoCycleSameSupportWitness` instantiates two disjoint two-charge components over supports `[0,1,2,3]` and `[4,5,6,7]`. | propext, Classical.choice, Quot.sound | General append bridge + concrete affine witness |

**No declaration depends on `sorryAx`.** The `Lean.ofReduceBool` axiom marks `native_decide`-checked
**concrete instances** — finite computations, not general theorems.

## A correction worth stating plainly

`…ExtractorCompleteness.uniformCycleExtractorCompleteness` (and its lemma `cycleSplit_residualFree`) is a
**restatement**, not a new theorem. Its proof is a thin wrapper that reduces directly to the
**pre-existing** general theorem `…extractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate`, which was
proven in commit `6783d8a` on **2026-06-12**. An earlier internal note described this wrapper as a
newly-proven result closing an "open" frontier; that was an over-statement and is **retracted**. The
mathematical content (uniform-cycle completeness for all `n ≥ 3`) was already established by the
pre-existing theorem; the wrapper only exposes it under a uniform name, and the `n = 5, 6` instances
corroborate it at concrete sizes.

## What remains open

Completeness over **arbitrary** Tseitin graphs is **not** proven and is the genuine open frontier
for this line of work.  v0.3.0 broadens the reusable sufficient-condition family beyond cycles
through private-incident witnesses, but it does not discharge the arbitrary-graph case.

## How to re-verify

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.13.0 lake env lean lean/CertifiedAffine/Audit.lean
```

`Audit.lean` pins the `#print axioms` profile of every declaration above with `#guard_msgs`, so any drift
(a new `sorry`, a hidden axiom, a vanished firewall) fails the build.
