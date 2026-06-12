# Claim Boundary

This artifact is a Lean 4 formalization and audit surface for certified
affine-structure extraction from CNF.

## Claims

- Uniform direct recognized GF(2) semantic preservation for the generated cycle
  Tseitin family `encoding_cycle_derived n` under `1 < n`.
- Uniform resource accounting for that direct surface:
  `expandedClauseCount = n * 8` and `equationCount = n`.
- A guarded axiom audit for the exported theorem path in `lean/CertifiedAffine/Audit.lean`.
- A finite canonical-fingerprint extractor scaffold retained as internal
  infrastructure for future compositionality work.

## Non-Claims

- No proof of P = NP.
- No proof of P != NP.
- No arbitrary SAT algorithm.
- No general CNF-to-XOR recognizer.
- No residual-free theorem for the full canonical fingerprint extractor.
- No matchgate, Pfaffian, Yang-Baxter, holographic, or GCT witness.
- No halting-style impossibility theorem.

## Open Obligation

The next theorem-forming obligation is canonical extractor compositionality:
support grouping should commute with disjoint-support union, and parity blocks
sharing variables should admit a bounded-overlap gluing lemma.  Until those are
proved, the canonical extractor must not be advertised as a uniform
residual-free extractor.
