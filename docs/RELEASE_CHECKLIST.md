# Public Release Checklist

This checklist is the gate for tagging this curated public artifact and
minting a Zenodo DOI.  The broader private planning repository should not be
made public directly because it contains planning history, exploratory lane
logs, scratch artifacts, and internal claim-control material.

## Release Boundary

- Public repo name: `certified-affine-extraction` or another neutral
  SAT/proof-logging name.
- Public claim: certified affine-structure extraction from CNF and Lean-checked
  GF(2) semantic preservation for scoped Tseitin-style families.
- Non-claims: no P = NP proof, no P != NP proof, no arbitrary SAT solver, no
  general CNF-to-XOR recognizer, no matchgate/Pfaffian witness, no GCT
  obstruction, and no halting-style theorem.
- Public history: one fresh initial commit for this curated export.
- Private history: keep the development repository private as the research
  diary and development record.

## Minimum Files

- `LICENSE` with Apache-2.0.
- `README.md` with headline theorems, build commands, and non-claims.
- `CITATION.cff` with verified author names, repository URL, version, and
  release date.
- Optional `.zenodo.json` after verifying author/ORCID metadata.  Do not add
  guessed ORCID or affiliation data.
- `lean/PvNP/Audit.lean` with guarded `#print axioms` checks for exported
  theorem claims.
- `.github/workflows/lean-audit.yml` building the audited Lean target and
  running the audit module.

## Before Public

- Confirm scratch files, generated logs, local paths, planning-only lane
  vocabulary, speculative P = NP/GCT/matchgate diary material, and bulky
  generated artifacts remain excluded.
- Run a secret scan over the curated export.
- Build from a clean checkout with the pinned `lean-toolchain` and
  `lake-manifest.json`.
- Confirm `Audit.lean` has no `Lean.ofReduceBool` on the exported theorem path.
- Verify `README.md` has the non-claims in the first screen.
- Confirm no external-facing title or abstract contains P = NP route language.

## Zenodo Sequence

1. Publish the curated repository.
2. Let public CI pass.
3. Enable Zenodo GitHub integration for the curated repository.
4. Cut a GitHub release from a defensible tag such as `v0.1.0`.
5. Let Zenodo archive the release and mint the version DOI.
6. Put the concept DOI badge in the README.
7. Cite the version DOI in any paper or note.

## Current Status

The current artifact has the first clean uniform direct-cycle theorem path:
`TseitinCycleGF2NormalizationSurface_correctnessInvariant`,
`TseitinCycleCNFFormula_length`, and
`TseitinCycleGF2NormalizationSurface_resourceCounts` audit without
`Lean.ofReduceBool`.  The stronger canonical extractor theorem is still open:
support grouping must commute with disjoint-support union, and shared-variable
parity blocks need a bounded-overlap gluing lemma.
