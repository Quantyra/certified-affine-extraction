# Changelog

All notable changes to this artifact are documented here. Versions are archived on Zenodo;
cite the version DOI minted from the corresponding tagged release.

## v0.2.0 — 2026-06-15

### Added — executable extractor completeness (scoped Tseitin families)
- `ExtractorCompleteness.ExtractorCompleteOn` instances proven for concrete recognized families:
  the canonical-fingerprint splitter returns its GF(2) blocks with **empty residual CNF** for the
  three-cycle (3 parity equations) and four-cycle (4 parity equations) Tseitin formulas
  (`extractorCompleteOn_threeCycle`, `extractorCompleteOn_fourCycle`).
- Combined semantic + executable completeness for both families
  (`semanticExtractorCompleteOn_threeCycle`, `semanticExtractorCompleteOn_fourCycle`): per-assignment
  CNF ↔ GF(2) equivalence *and* residual-free executable extraction.
- New module `lean/CertifiedAffine/ExtractorCompletenessInstances.lean`; audit entries added to
  `lean/CertifiedAffine/Audit.lean` with the honest `#print axioms` profile.

### Carried from the v0.2 working surface
- `ParityEncoded.Class.sound` / `.append`; `ExtractorCompleteness` reduction lemmas;
  `GroupFrame` canonical-support append/disjoint-key frame theorems; the no-search splitter.

### Quality
- Full `lake build` green; `lean/CertifiedAffine/Audit.lean` passes (`#guard_msgs`-pinned axiom
  profiles, no `sorryAx`); zero `sorry`/`admit`; secret scan clean.

### Non-claims (binding)
This release does **not** claim or imply P = NP, P != NP, a general SAT algorithm, a general
CNF-to-XOR recognizer, a matchgate/Pfaffian/GCT/holographic/halting-style result, or any result
beyond the explicitly-scoped, Lean-checked theorems for the named Tseitin-style families. Affine/GF(2)
systems are classically polynomial-time solvable; this artifact certifies *extraction* of that
structure for a scoped family, nothing more.

## v0.1.0 — 2026-06-12
- Initial public release: GF(2) semantic-preservation surface for the uniform Tseitin cycle family
  (`TseitinCycleGF2NormalizationSurface_correctnessInvariant`, resource counts), axiom-audited.
- Zenodo concept DOI 10.5281/zenodo.20660863; v0.1.0 version DOI 10.5281/zenodo.20660864.
