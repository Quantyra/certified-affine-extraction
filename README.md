# Certified Affine Extraction

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20660863.svg)](https://doi.org/10.5281/zenodo.20660863)

This repository is a Lean 4 artifact for certified affine-structure extraction
from CNF and GF(2) semantic preservation for scoped Tseitin-style families.

This is the curated public artifact.  It intentionally excludes the broader
private planning history and speculative research notes.

## Headline Theorem Surface

- `TseitinCycleGF2NormalizationSurface_correctnessInvariant`: semantic
  preservation for the uniform direct recognized GF(2) surface over
  `encoding_cycle_derived n` under `1 < n`.
- `TseitinCycleCNFFormula_length`: uniform expanded CNF length for the cycle
  family.
- `TseitinParityFormulaFromEncoding_length`: uniform compact GF(2) equation
  count for the cycle family.
- `TseitinCycleGF2NormalizationSurface_resourceCounts`: resource accounting
  with `expandedClauseCount = n * 8` and `equationCount = n`.

The audit surface is `lean/CertifiedAffine/Audit.lean`.

Supporting documentation:

- `docs/CLAIM_BOUNDARY.md`
- `docs/AXIOM_AUDIT.md`
- `docs/RELEASE_CHECKLIST.md`

## Build

```bash
lake build
lake env lean lean/CertifiedAffine/Audit.lean
```

The pinned Lean/mathlib dependencies are carried by `lean-toolchain` and
`lake-manifest.json`.

CI runs the full build and audit commands from a clean checkout.

## Non-Claims

This artifact does not claim P = NP, P != NP, a general SAT algorithm, a
general CNF-to-XOR recognizer, a matchgate/Pfaffian witness, a GCT obstruction,
or a halting-style theorem.

The current clean theorem path is a direct recognized GF(2) surface.  The
canonical fingerprint extractor still needs compositionality over
disjoint-support union and bounded-overlap gluing for shared variables before
it can be advertised as a uniform residual-free extractor.

## AI Assistance Disclosure

Development used AI coding assistance.  Human authors are responsible for the
claims, release decisions, and final artifact review.
