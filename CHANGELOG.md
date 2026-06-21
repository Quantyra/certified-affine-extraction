# Changelog

All notable changes to this artifact are documented here. Versions are archived on Zenodo;
cite the version DOI minted from the corresponding tagged release.

## v0.3.2 — 2026-06-21

### Added — mixed ordinary + same-support quotient key-disjoint component list + nonempty 3-component witness
- `AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_of_mixedQuotientKeyDisjointComponentList`:
  finite mixed quotient-component composition under canonical-key-disjointness for ordinary certified
  no-search components combined with generated same-support fallback components.
- `AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_threeMixedOrdinarySameSupportQuotientWitness`:
  concrete nonempty 3-component witness (one ordinary generated component + two same-support fallback
  components) over 16 variables, with pairwise key-disjointness.
- Supporting shape theorems `threeMixedOrdinarySameSupportQuotientWitness_shape` (executable witness facts)
  and the inductive `NonexhaustiveMixedQuotientKeyDisjointComponentList`.
- Axiom profiles: general theorem and witness use `[propext, Classical.choice, Quot.sound]`; one shape
  uses subset `[propext]`.
- `lean/CertifiedAffine/Audit.lean` updated with pinned `#print axioms` guards (no sorryAx drift).
- `README.md`, `INTEGRITY-CLAIMS.md`, `CITATION.cff`, `.zenodo.json` updated for v0.3.2.

### Quality
- `lake build` and `lake env lean lean/CertifiedAffine/Audit.lean` pass under pinned `leanprover/lean4:v4.13.0`.
- No `sorry`/`admit`; no new `Lean.ofReduceBool` on general theorems; prior non-claims boundary preserved.
- Scope unchanged: certified affine/GF(2) extraction only.

### Non-claims (binding)
This release does **not** claim or imply P = NP, P != NP, a general SAT algorithm, a general
CNF-to-XOR recognizer, any NP/circuit lower bound, or any result beyond the explicitly-scoped,
Lean-checked theorems for the named Tseitin-style families.

## v0.3.1 — 2026-06-19

### Added — nonexhaustive collision-free append bridge (same-support components under key disjointness)
- `AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_append_sameSupportComponents_of_keyDisjoint`:
  two generated same-support collision components compose through the no-search fallback splitter
  when their canonical support keys are disjoint.
- Concrete witness `AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_twoDisjointTwoCycleSameSupportWitness`:
  instantiates two disjoint two-charge components over supports `[0,1,2,3]` and `[4,5,6,7]`.
- Axiom profile `[propext, Classical.choice, Quot.sound]` for the general theorem;
  the shape theorem `twoDisjointTwoCycleSameSupportWitness_shape` is axiom-free.
- `lean/CertifiedAffine/Audit.lean` updated with pinned `#print axioms` guards for the new declarations.
- `INTEGRITY-CLAIMS.md` updated with the new entry.

### Quality
- Scope is unchanged: certified affine/GF(2) extraction for scoped Tseitin-style families only.

### Non-claims (binding)
This release does **not** claim or imply P = NP, P != NP, a general SAT algorithm, a general
CNF-to-XOR recognizer, or any result beyond the explicitly-scoped, Lean-checked theorems for the
named Tseitin-style families.

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
