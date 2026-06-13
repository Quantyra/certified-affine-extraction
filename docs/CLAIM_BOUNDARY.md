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
- A v0.2 working theorem surface for a declarative fixed-ambient
  `ParityEncoded.Class`: any CNF in the class is semantically equivalent, per
  assignment, to its listed GF(2) equations.
- A v0.2 semantic gluing rule for `ParityEncoded.Class`: appended
  parity-encoded CNFs instantiate the class even when their variables overlap.
  The existing support-disjoint `union` constructor remains available for
  frame-oriented extractor arguments.
- A v0.2 extractor-completeness scaffold: if canonical support grouping returns
  recognized groups for `F ++ G`, then the executable splitter is residual-free
  and its GF(2) output matches the requested target up to `List.Perm`.
- A v0.2 splitter cover theorem: `splitCanonicalSupportClauseGroups` preserves
  all ordinary clauses up to `List.Perm`, moving recognized groups into the
  compact core and unrecognized groups into residual CNF.
- A v0.2 residual-free split-composition theorem: residual-free support-group
  splits compose across appended support-group lists, so an already-complete
  left fragment and an already-complete right fragment can be reused without
  re-proving their recognizer internals.
- A v0.2 extractor-completeness append theorem: two `ExtractorCompleteOn`
  witnesses compose for `F ++ G` when the grouping pass frames the append as
  `groupClausesByCanonicalSupport F ++ groupClausesByCanonicalSupport G`.
- A v0.2 combined semantic/extractor append theorem:
  `SemanticExtractorCompleteOn` witnesses compose under the same grouping-frame
  premise, with the semantic half discharged by ordinary CNF and GF(2) append
  splitting.
- A v0.2 canonical support-grouping frame theorem: if every suffix clause has a
  canonical support key fresh for the already-computed prefix groups, then
  `groupClausesByCanonicalSupport (F ++ G)` is exactly
  `groupClausesByCanonicalSupport F ++ groupClausesByCanonicalSupport G`.
- A v0.2 operational bridge for that frame theorem: clause-key disjointness
  between `F` and `G` implies the fresh-key premise, so grouping commutes with
  append under `GroupFrame.CNFClauseKeysDisjoint F G`.
- A v0.2 permuted-fragment frame bridge: clause-key disjointness and the
  nonempty-support side condition transport across CNF clause permutations, and
  the grouping, exact splitter, `ExtractorCompleteOn`, and
  `SemanticExtractorCompleteOn` append frames now have `_perm` wrappers for the
  case where each fragment is independently permuted before append.  The
  recognizer-complete class has the matching
  `clausePermutedRecognizedClass_append_keyDisjoint_perm` wrapper.
- A v0.2 variable-support bridge: `ParityEncoded.DisjointSupport F G` implies
  append grouping when the right-hand CNF satisfies
  `GroupFrame.CNFClausesHaveNonemptySupport G`.
- A v0.2 exact baseline splitter-frame theorem: if `F` and `G` already split
  residual-free with known emitted block lists, then
  `splitArityFourParityCanonicalSupportGroups (F ++ G)` emits exactly the left
  block list followed by the right block list under canonical support-key
  disjointness, and also under ordinary variable-disjoint support with the
  nonempty-right-CNF side condition.
- A v0.2 caller-facing extractor frame theorem: residual-free
  `ExtractorCompleteOn` witnesses compose under canonical support-key
  disjointness, and under ordinary variable-disjoint support with the
  nonempty-right-CNF side condition.
- A v0.2 caller-facing combined frame theorem: `SemanticExtractorCompleteOn`
  witnesses compose under the same canonical support-key disjointness and
  ordinary variable-disjoint support side-condition packages.
- A v0.2 enhanced fallback split-composition theorem: residual-free
  `splitCanonicalSupportClauseGroupsWithTwoChargeFallback` support-group splits
  compose across appended support-group lists.
- A v0.2 exact enhanced fallback splitter-frame theorem: residual-free
  enhanced splits of `F` and `G` produce exactly the concatenated emitted block
  list for `F ++ G` under the same canonical support-key disjointness and
  ordinary variable-disjoint support side-condition packages.
- A v0.2 enhanced fallback recognized-group subsumption theorem: recognized
  canonical support groups are residual-free for the enhanced fallback splitter
  before any same-support fallback branch is used.
- A v0.2 caller-facing enhanced fallback frame theorem:
  `EnhancedExtractorCompleteOn` and `EnhancedSemanticExtractorCompleteOn`
  witnesses compose under grouping-frame, canonical support-key disjointness,
  and ordinary variable-disjoint support side-condition packages.
- A v0.2 enhanced group-recognition theorem: recognized canonical support
  groups with successful syntactic upgrades instantiate the combined
  `EnhancedSemanticExtractorCompleteOn` surface, including the singleton
  recognized-group atom case.
- A v0.2 enhanced support-disjoint group-recognition bridge: two CNF fragments
  whose support groups are already recognized, and whose supports frame the
  append, are residual-free for the enhanced fallback splitter.  With successful
  syntactic upgrades on the emitted blocks, the same source-level frame packages
  as `EnhancedSemanticExtractorCompleteOn`.
- A v0.2 same-key grouping theorem: any nonempty CNF whose clauses share one
  canonical support key is grouped by the executable support grouper into one
  support component.
- A v0.2 generated-parity grouping prerequisite: every clause generated by
  `clausesForVertex vars charge` has the canonical support key induced by
  `vars`, and any nonempty generated parity expansion therefore groups into
  exactly one canonical support component.
- A v0.2 generated-block side-condition theorem:
  `clausesForVertex vars charge` satisfies
  `GroupFrame.CNFClausesHaveNonemptySupport` whenever `vars != []`.
- A v0.2 grouping cover theorem: `groupClausesByCanonicalSupport` preserves the
  input CNF clauses up to `List.Perm`.
- A v0.2 atomic recognizer-to-class bridge: proof-carrying recognized parity
  blocks, syntactically recognized parity blocks, and canonical-fingerprint
  blocks with explicit permutation evidence or an accepted syntactic
  permutation signal instantiate the
  `ParityEncoded.Class` atom constructor.
- A v0.2 generated true-charge recognizer bridge: the public two-charge
  recognizer result for nonempty generated true-charge normal-form parity
  blocks is proved after discharging the false-first recognizer miss by a
  generated true/false canonical block-fingerprint separation.
- A v0.2 generated parity-atom extractor-completeness theorem: for either
  charge, a nonempty generated parity expansion in canonical support order is
  residual-free for the executable canonical splitter, and the emitted GF(2)
  output matches `[parityClauseForVertex vars charge]`.
- A v0.2 binary support-disjoint generated parity-atom
  extractor-completeness theorem: two generated parity expansions in canonical
  support order are residual-free for the executable canonical splitter when
  their supports are disjoint and the right-hand expansion has nonempty
  support, with emitted GF(2) output matching the two generated parity
  equations.
- A v0.2 support-disjoint induction-step bridge: any prefix whose support
  groups are already recognized can be extended by one generated normal-form
  parity expansion with disjoint support, preserving residual-free extractor
  completeness and appending the generated GF(2) equation to the prefix output.
- A v0.2 key-disjoint induction-step bridge: any prefix whose support groups
  are already recognized can be extended by one generated normal-form parity
  expansion whose canonical clause-support key is fresh for the prefix,
  preserving residual-free extractor completeness and appending the generated
  GF(2) equation to the prefix output.
- A v0.2 enhanced induction-step bridge: the same recognized-prefix-plus-one
  generated-atom step now holds for the production-shaped enhanced fallback
  splitter under both canonical-key freshness and ordinary support disjointness.
  The combined semantic/enhanced-executable variants require successful
  syntactic upgrades for the prefix blocks; the generated atom supplies its own
  upgrade through the canonical recognizer.
- A v0.2 finite support-disjoint generated-family theorem: any snoc-built
  finite family of nonempty generated normal-form parity expansions whose new
  block is support-disjoint from the accumulated prefix is residual-free for
  the executable canonical splitter, with emitted GF(2) output matching the
  generated equations up to `List.Perm`.
- A v0.2 finite key-disjoint generated-family theorem: any snoc-built finite
  family of generated normal-form parity expansions whose new block has a fresh
  canonical support key relative to the accumulated prefix is residual-free for
  the executable canonical splitter, with emitted GF(2) output matching the
  generated equations up to `List.Perm`.  This extractor theorem permits shared
  variables across different generated blocks when their full support keys are
  distinct.
- A v0.2 generated-spec class theorem: every folded generated parity-spec list
  instantiates `ParityEncoded.Class` through semantic append/gluing, without
  key-freshness or disjointness side conditions.  Generated key-disjoint
  families and their folded generated-spec-list interfaces retain matching
  side-conditioned class wrappers for the executable extractor lane.
- A v0.2 combined semantic/executable extraction predicate:
  `SemanticExtractorCompleteOn F S` packages per-assignment CNF/GF(2)
  equivalence together with residual-free executable extractor completeness,
  and `semanticExtractorCompleteOn_of_class` derives it from a declarative
  `ParityEncoded.Class` witness plus a separate `ExtractorCompleteOn` witness.
- A v0.2 combined generated-family theorem: generated key-disjoint families and
  their folded generated-spec-list interfaces satisfy
  `SemanticExtractorCompleteOn` for the accumulated CNF and GF(2) formulas.
- A v0.2 group-recognition class bridge: recognized canonical support groups
  instantiate `ParityEncoded.Class` directly once emitted blocks carry
  syntactic recognition signals, or pass executable `toSyntactic?` checks, and
  are append-disjoint.
- A v0.2 relaxed semantic-append recognition bridge: syntactically accepted
  canonical blocks, and recognized canonical support groups passing
  `toSyntactic?`, instantiate `ParityEncoded.Class` without any support-
  disjointness premise; semantic gluing is handled by `ParityEncoded.Class.append`.
- A v0.2 relaxed residual-free split bridge: residual-free executable splitter
  output whose emitted blocks carry syntactic signals, or pass `toSyntactic?`,
  instantiates both `ParityEncoded.Class` and `SemanticExtractorCompleteOn`
  without any block support-disjointness premise.
- A v0.2 relaxed group-recognition combined bridge: recognized canonical
  support groups passing `toSyntactic?` satisfy `SemanticExtractorCompleteOn`
  without any block support-disjointness premise.
- A v0.2 proof-carrying recognized-CNF certificate interface:
  `AtomicClassBridge.CertifiedRecognizedCNF` packages an arbitrary CNF together
  with support-grouping evidence, recognized-block evidence, syntactic upgrade
  checks, and GF(2)-target permutation evidence.  The certified CNF then
  instantiates `ParityEncoded.Class`, baseline `SemanticExtractorCompleteOn`,
  and enhanced `EnhancedSemanticExtractorCompleteOn`.  The baseline
  `ExtractorCompleteOn` and `SemanticExtractorCompleteOn` surfaces also
  transport through arbitrary whole-CNF clause permutation of the certified
  source CNF.
- A v0.2 clause-permuted single-block certificate:
  `AtomicClassBridge.ClausePermutedRecognizedBlock` packages one recognized
  parity component with its singleton support-grouping fact, executable
  recognizer result, and literal-level permutation proof against the inferred
  parity expansion.  This smaller witness derives the general
  `CertifiedRecognizedCNF` interface, `ParityEncoded.Class`, baseline
  `SemanticExtractorCompleteOn`, and enhanced `EnhancedSemanticExtractorCompleteOn`.
  The constructor
  `AtomicClassBridge.clausePermutedRecognizedBlock_of_singleRecognizedGroup_toSyntacticOk`
  derives that certificate from singleton executable-recognition facts plus a
  successful `toSyntactic?` check, because
  `AtomicClassBridge.canonicalFingerprintRecognizedBlock_perm_of_toSyntacticOk`
  recovers the required literal-level permutation proof.  Generated parity atoms
  in canonical support order now instantiate this same smaller certificate
  boundary through
  `AtomicClassBridge.clausePermutedRecognizedBlock_exists_clausesForVertex_normal`
  and the class/baseline/enhanced
  `_via_clausePermutedRecognizedBlock` corollaries.
- A v0.2 permuted generated-atom grouping/certificate bridge:
  `GroupFrame.groupClausesByCanonicalSupport_eq_single_of_perm_clausesForVertex`
  proves that every nonempty clause permutation of a generated parity expansion
  still forms one canonical support group.  The
  `AtomicClassBridge.*_of_perm_clausesForVertex_toSyntacticOk` wrappers use
  that fact to produce the clause-permuted recognized-block certificate,
  `ParityEncoded.Class`, baseline `SemanticExtractorCompleteOn`, enhanced
  `EnhancedExtractorCompleteOn`, and enhanced
  `EnhancedSemanticExtractorCompleteOn` for the permuted atom.  The executable
  recognizer result and successful `toSyntactic?` check remain explicit
  premises for this lower-level wrapper; stronger generated-atom wrappers use
  canonical fingerprint invariance to discharge those recognizer obligations.
- A v0.2 canonical fingerprint permutation-invariance theorem:
  `canonicalClauseFingerprint_eq_of_perm`,
  `canonicalBlockFingerprint_eq_of_perm`, and
  `canonicalParityBlockRecognitionSignal_of_perm` prove that canonical
  fingerprints are invariant under literal/clause permutation for full
  signed-literal clause content.  This is a generic sort/canonical-form result,
  not a generated-family specialization.
- A v0.2 support-key permutation-invariance theorem: `sortFinByVal_eq_of_perm`,
  `canonicalClauseSupportVars_eq_of_perm`, and
  `canonicalClauseSupportKey_eq_of_perm` prove that literal reordering does not
  change the support variables or support key assigned to a clause.  Support-key
  collisions can still merge clauses into the same group; this theorem only
  rules out order dependence inside the support-key canonicalizer.
- A v0.2 no-premise clause-permuted generated-atom recognizer bridge:
  `AtomicClassBridge.inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal`,
  the false/true public-recognizer variants, and the corresponding
  class/baseline/enhanced wrappers prove that nonempty clause permutations of
  generated atoms in canonical support order are recognized with the expected
  compact equation.  The caller no longer supplies the canonical fingerprint
  signal, and the true-charge false-first miss is discharged internally by
  transported true/false fingerprint separation.
- A v0.2 generated-atom recognizer-complete class hook:
  `AtomicClassBridge.clausePermutedRecognizedClass_of_perm_clausesForVertex_normal`
  lifts those nonempty clause-permuted generated atoms directly into
  `ClausePermutedRecognizedClass`, so the atom case of the recognizer-complete
  induction no longer requires a generated-order CNF.
- A v0.2 clause-permuted recognizer-complete class:
  `AtomicClassBridge.ClausePermutedRecognizedClass` is an induction-shaped
  fragment for arbitrary clause-permuted recognized blocks connected by
  canonical support-key-disjoint appends, with GF(2)-target permutation
  closure and whole-CNF clause permutation closure.  The class forgets to
  `ParityEncoded.Class` and proves both baseline `SemanticExtractorCompleteOn`
  and enhanced `EnhancedSemanticExtractorCompleteOn`.  It also exposes
  recognized executable support-group witnesses and transports the baseline and
  enhanced extractor surfaces through arbitrary whole-CNF clause permutation.
  Generated key-disjoint families and their key-disjoint/fresh-key spec-list
  wrappers now instantiate this class, so the generated-family lane factors
  through a more general recognizer completeness surface.
- A v0.2 support-disjoint group-recognition combined bridge: two CNF fragments
  whose support groups are recognized, whose emitted blocks pass
  `toSyntactic?`, and whose supports frame the append satisfy
  `SemanticExtractorCompleteOn` for the appended CNF and emitted GF(2) output.
  The relaxed `_append` variant keeps the source-level frame premises but drops
  internal append-disjointness requirements on the emitted block lists by using
  semantic append/gluing.
- A v0.2 enhanced support-disjoint recognized-fragment bridge: the same
  source-level support frame now feeds the production-shaped enhanced fallback
  splitter, proving residual-free enhanced extraction for already-recognized
  fragments and the combined enhanced semantic/executable package under
  successful syntactic upgrades.
- A v0.2 generated-spec-to-Tseitin-encoder bridge: folded generated parity
  specs built from an incident-list encoder are definitionally aligned with
  `tseitinClausesFromIncident` and `tseitinParityFormulaFromIncident`, and this
  alignment lifts to `TseitinCNFFormulaFromEncoding` and
  `TseitinParityFormulaFromEncoding`.
- A v0.2 folded generated-spec-list interface: finite lists of generated
  parity specs with the same snoc-order side conditions instantiate the
  support-disjoint family theorem and inherit residual-free executable
  extractor completeness.
- A v0.2 folded key-disjoint generated-spec-list interface: finite lists of
  generated parity specs with accumulated canonical support-key freshness
  instantiate the key-disjoint family theorem and inherit residual-free
  executable extractor completeness.
- A v0.2 spec-level canonical-key freshness interface: finite lists of generated
  parity specs whose new incident-support key is distinct from every earlier
  generated spec imply the clause-level key-disjoint spec-list condition and
  inherit residual-free executable extractor completeness.
- A v0.2 graph-encoding extractor reduction: any concrete graph encoding whose
  generated incident specs satisfy accumulated key-disjointness is
  residual-free for the executable canonical splitter, with emitted GF(2) output
  matching the existing direct parity formula.
- A v0.2 graph-encoding extractor reduction from spec-level canonical-key
  freshness: the same residual-free executable extractor conclusion follows
  when the generated incident specs satisfy the spec-level freshness certificate.
- A v0.2 positive-degree graph-encoding reduction: the same generated-spec
  freshness and residual-free extractor conclusions follow from fresh canonical
  incident-support keys plus `0 < degree G v` at every vertex, without requiring
  callers to construct explicit `c :: tail` CNF witnesses.
- A v0.2 graph-encoding class theorem: every concrete Tseitin graph encoding
  generated by the incident-list encoder instantiates `ParityEncoded.Class`
  against the existing direct `TseitinParityFormulaFromEncoding`.  The
  key-disjoint, fresh-key, and positive-degree variants remain as wrappers that
  align the class lane with side-conditioned extractor theorems.
- A v0.2 graph-encoding combined theorem: under the same generated-spec
  key-disjoint, spec-level freshness, or fresh-incident-key plus
  positive-degree side conditions, concrete Tseitin graph encodings satisfy
  `SemanticExtractorCompleteOn` against the existing direct
  `TseitinParityFormulaFromEncoding`.
- A v0.2 `circulant12` graph-family package: `encoding_circulant12_derived n`
  is a concrete `GraphEncodingData` for every `2 < n`, with proved
  undirectedness, endpoint range, no self loops, edge-count lower bound, and
  positive degree at every vertex.
- A v0.2 `circulant12` fresh-key theorem: the family-specific canonical
  incident-support keys are fresh in vertex-range order for every `2 < n`.
- A v0.2 unconditional `circulant12` extractor theorem: the executable
  canonical splitter is residual-free on `TseitinCNFFormulaFromEncoding
  (encoding_circulant12_derived n hn) charge` for every `2 < n` and every
  charge function.
- A v0.2 unconditional `circulant12` class theorem: the same formal encoding
  instantiates `ParityEncoded.Class` for every `2 < n` and every charge
  function.
- A v0.2 unconditional `circulant12` combined theorem: the same formal encoding
  satisfies `SemanticExtractorCompleteOn` for every `2 < n` and every charge
  function.
- A v0.2 unconditional `circulant12` direct-recognizer theorem: the same formal
  encoding satisfies `EnhancedSemanticExtractorCompleteOn` through successful
  executable syntactic upgrades for the recognized blocks, for every `2 < n`
  and every charge function.
- A v0.2 cycle-family extractor reduction: `TseitinCycleCNFFormula n hn` is
  residual-free for the executable canonical splitter once
  `generatedParitySpecsForCycle n hn` is proved to satisfy
  `GeneratedKeyDisjointSpecList`.
- A v0.2 cycle-family extractor reduction from spec-level canonical-key
  freshness: `TseitinCycleCNFFormula n hn` is residual-free for the executable
  canonical splitter once `generatedParitySpecsForCycle n hn` is proved to
  satisfy `GeneratedCanonicalKeyFreshSpecList`.
- A v0.2 cycle-family class theorem: `TseitinCycleCNFFormula n hn`
  instantiates `ParityEncoded.Class` for every derived cycle with `1 < n`,
  including the certified two-vertex boundary.
- A v0.2 nondegenerate cycle-family combined theorem:
  `TseitinCycleCNFFormula n hn` satisfies `SemanticExtractorCompleteOn` against
  `TseitinParityFormulaFromEncoding (encoding_cycle_derived n hn)
  cycleRootCharge` for every derived cycle with `2 < n`.
- A v0.2 derived-cycle nonempty-block bridge: every vertex incident-index list
  in `encoding_cycle_derived n hn` has arity four, and therefore every generated
  cycle vertex block supplies the `c :: tail` CNF witness required by generated
  spec-list `snoc` constructors.
- A v0.2 arity-independent nonempty-block bridge: every generated parity
  expansion over a nonempty variable list supplies the `c :: tail` CNF witness,
  and every positive-degree incident-generated vertex block has such a nonempty
  variable list.
- A v0.2 incident-spec snoc bridge: generated incident-spec lists commute with
  appending one vertex, and the spec-level canonical-key freshness certificate
  can be extended from per-vertex freshness, nonempty-block, and normal-order
  witnesses.
- A v0.2 incident-index normal-order bridge: every `incidentIndices G hm v`
  list is a filtered `allFin` list and therefore already satisfies the
  executable recognizer's canonical support-order side condition.  The
  derived-cycle family inherits this immediately.
- A v0.2 derived-cycle edge-index bridge: even and odd directed edge indices
  `2*u` and `2*u + 1` are proved to be the forward and reverse variables for
  the cycle edge between `u` and `(u + 1) % n`; those indices are present in
  vertex `u`'s canonical incident key and absent from every non-endpoint vertex
  key.
- A v0.2 two-cycle boundary theorem: in the `n = 2` derived cycle, the two
  vertex constraints have the same canonical incident-support key, so the
  current key-fresh generated-spec snoc lane cannot cover all `1 < n` cycles
  without a special case or a stronger nondegenerate-cycle hypothesis.
- A v0.2 uniform enhanced cycle theorem: every derived cycle with `1 < n`
  satisfies `EnhancedSemanticExtractorCompleteOn` against
  `TseitinParityFormulaFromEncoding (encoding_cycle_derived n hn)
  cycleRootCharge`.  The theorem uses the recognized-group path for `2 < n`
  and the certified same-support fallback for the `n = 2` boundary.
- A v0.2 generated-clause reverse membership theorem: every clause in
  `clausesForVertex vars charge` comes from a Boolean row of length
  `vars.length` whose parity disagrees with `charge`.
- A v0.2 block-fingerprint witness bridge: true/false generated
  block-fingerprint separation is proved by showing that the all-false
  assignment clause fingerprint is present in every true-charge generated block
  and absent from the corresponding false-charge block.
- A v0.2 list-level recognizer-to-class bridge: canonical-fingerprint block
  lists with per-block permutation certificates and append-disjoint supports
  instantiate `ParityEncoded.Class` over
  `canonicalFingerprintRecognizedBlocksCNF` and
  `canonicalFingerprintRecognizedBlocksGF2`.
- A v0.2 certificate-composition surface: permutation certificates and
  append-disjointness compose across appended canonical block lists, provided
  every left block is disjoint from the right list's covered CNF.
- A v0.2 singleton-certificate surface: singleton canonical block lists
  satisfy append-disjointness directly, and a successful singleton
  `toSyntactic?` check supplies the executable syntactic certificate for the
  atom case.
- A v0.2 finite generated-family syntactic-certificate theorem: key-disjoint
  generated families, their folded spec-list form, and the caller-facing
  canonical-key-fresh form return recognized support groups together with
  successful executable syntactic upgrades for every emitted canonical block
  and the expected compact GF(2) output up to permutation.
- A v0.2 finite generated-family recognizer-certificate theorem: that witness
  package feeds directly into the enhanced semantic/executable completeness
  surface through recognized support groups, executable syntactic upgrades, and
  GF(2) permutation evidence.  This records a recognizer-certificate route for
  generated CNFs, not merely a generator-side class/equivalence route.
- A v0.2 graph-encoding recognizer-certificate surface: concrete Tseitin graph
  encodings inherit the direct recognizer-certificate route under generated
  key-disjointness, canonical-key freshness, explicit nonempty generated-block
  witnesses, or positive-degree witnesses.
- A v0.2 cycle-family recognizer-certificate surface: nondegenerate derived
  cycles use the direct recognizer-certificate route, while the all-`1 < n`
  theorem combines that route with the certified two-charge same-support
  fallback for the two-cycle boundary.
- A v0.2 covered-disjointness bridge: ordinary support disjointness between the
  covered CNFs of two canonical block lists supplies the cross-disjointness
  premise needed by append-disjointness composition.
- A v0.2 syntactic-signal bridge: accepted syntactic permutation signals for
  canonical blocks supply the per-block permutation certificates required by
  the list-level bridge.
- A v0.2 executable certificate bridge: successful `toSyntactic?` checks over
  canonical-fingerprint blocks supply those syntactic-signal certificates.
- A v0.2 recognized-block cover theorem: when support groups are recognized,
  the emitted canonical blocks cover the source CNF up to `List.Perm`.
- A v0.2 disjointness-transport theorem: ordinary support disjointness
  transports across clause-list permutations, allowing source-level disjointness
  to transfer to emitted covered-block CNFs.
- A v0.2 residual-free split-to-class bridge: if
  `splitArityFourParityCanonicalSupportGroups F` returns exactly `blocks` with
  empty residual CNF, and those `blocks` carry syntactic recognition signals
  plus append-disjointness, then `F` instantiates `ParityEncoded.Class` with
  the emitted GF(2) equations.
- The same split-to-class bridge with the syntactic-signal premise discharged
  by successful executable `toSyntactic?` checks on all emitted blocks.
- A v0.2 residual-free split-to-combined bridge: the same certified splitter
  output yields `SemanticExtractorCompleteOn F
  (canonicalFingerprintRecognizedBlocksGF2 blocks)`, packaging both
  per-assignment CNF/GF(2) equivalence and residual-free extractor
  completeness for the splitter's own emitted GF(2) formula.
- A v0.2 group-recognition-to-combined bridge: recognized canonical support
  groups yield the same `SemanticExtractorCompleteOn` package once the emitted
  blocks carry syntactic recognition signals, or pass executable
  `toSyntactic?` checks, and satisfy append-disjointness.
- A v0.2 singleton group-recognition combined bridge: one recognized support
  component with a successful `toSyntactic?` check yields the combined theorem
  for its emitted GF(2) equation.
- A v0.2 single-support-group bridge: if a CNF groups as one canonical support
  component, that component is recognized as one canonical block, and the block
  passes `toSyntactic?`, then the CNF instantiates `ParityEncoded.Class` as a
  single emitted GF(2) equation.
- A v0.2 support-disjoint append-fragment bridge: if `F` and `G` are
  support-disjoint, `G` has no empty-support clauses, both sides group into
  recognized canonical blocks, all emitted blocks pass `toSyntactic?`, and both
  sides are internally append-disjoint, then `F ++ G` instantiates
  `ParityEncoded.Class` with the appended emitted GF(2) equations.
- A v0.2 relaxed support-disjoint append-fragment bridge: the same source-level
  support frame and grouping premises instantiate both `ParityEncoded.Class`
  and `SemanticExtractorCompleteOn` for `F ++ G` without requiring either
  emitted block list to be internally append-disjoint.

## Non-Claims

- No proof of P = NP.
- No proof of P != NP.
- No arbitrary SAT algorithm.
- No general CNF-to-XOR recognizer.
- No unconditional residual-free theorem for the full canonical fingerprint
  extractor.
- No extractor completeness theorem over arbitrary declarative
  `ParityEncoded.Class` witnesses yet.  The combined
  `SemanticExtractorCompleteOn` theorems are side-conditioned frame-composition,
  generated-family, concrete graph-encoding, nondegenerate-cycle, and
  `circulant12` claims.
- No matchgate, Pfaffian, Yang-Baxter, holographic, or GCT witness.
- No halting-style impossibility theorem.

## Open Obligation

The semantic generated-spec lane now covers every folded generated parity-spec
list, so every concrete graph encoding and every derived cycle with `1 < n`
instantiates `ParityEncoded.Class`.  The concrete cycle/Tseitin generated-spec
freshness certificate is still proved only for the nondegenerate derived cycle
range:
`GeneratedCanonicalKeyFreshSpecList _ (generatedParitySpecsForCycle n hn)` under
`2 < n`.  This discharges the executable cycle-family extractor theorem for
that range via `extractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate`.
The proof no longer reasons directly over generated CNF clauses: the cycle
vertex nonempty-block witness can now come either from the arity-four degree
theorem or from the arity-independent positive-degree bridge, the
incident-index normal-order side condition comes from the filtered-`allFin`
theorem, the endpoint membership/exclusion lemmas prove pairwise distinct
canonical incident-support keys, and the prefix induction packages those facts
into the folded spec-level freshness certificate.  The `n = 2` derived cycle
remains a certified boundary case for the executable lane: both vertex
constraints have the same canonical incident-support key, so the current
key-fresh snoc premise cannot hold there.  The executable boundary is now
certified directly as well: the current canonical support splitter emits zero
blocks on the direct two-cycle CNF, leaves all 16 clauses residual, and therefore
does not satisfy residual-free `ExtractorCompleteOn` for the direct
two-equation GF(2) target.  This is a current-recognizer limitation, not a
semantic-equivalence limitation, because the declarative generated-spec class
lane covers every derived cycle with `1 < n`.  A guided recovery pass is
certified, and a narrow unguided two-charge same-support probe now finds the
certified fallback split for this boundary.  That local probe is also wired
into a production-shaped fallback splitter after the existing one-block
recognizer.  Closing the boundary completely still requires generalizing that
local splitter beyond the two-charge case.  The fallback target is certified at
the decomposition interface: mapping the generated parity specs pointwise to
canonical recognized blocks covers exactly the generated CNF fold, compacts
exactly to the generated GF(2) fold, passes the syntactic-upgrade check, and
produces a residual-free `CanonicalFingerprintGF2Decomposition`.  At the
concrete `n = 2` boundary, `twoCycleSameSupportFallback_exists` supplies
exactly two such blocks covering the direct two-cycle CNF and compacting to the
direct two-equation GF(2) target, while
`twoCycleSameSupportFallbackDecomposition_*` records the corresponding
decomposition facts: two equations, zero residual clauses, and sixteen covered
expanded clauses.  The guided recovery pass validates exact CNF coverage for a
supplied generated-spec split, returns that fallback decomposition on the
direct two-cycle CNF, and succeeds on the actual one-group canonical support
component.  The permutation-insensitive guided lane now generalizes this
verification side beyond the two-charge boundary:
`groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_sameSupport`
and
`recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_eq_some_of_perm_generatedParitySpecs_sameSupport`
show that any nonempty clause permutation of a supplied generated-spec list
whose specs all use one canonical support groups as one canonical support
component and is accepted by the guided recovery for that supplied split.  The
corresponding class bridge,
`class_of_recoverSingleMergedSupportGroupFromGeneratedSpecsPerm`, gives a
local `ParityEncoded.Class` witness for any successful return.  This is still
not unguided recognition: the spec list is supplied as a premise, not inferred
from an arbitrary CNF.  The unguided two-charge probe infers the canonical
support from that component, tries both charge orders, proves residual-free
component coverage for any returned decomposition, proves that returned blocks
pass the executable syntactic upgrade, and succeeds on the same actual
one-group two-cycle component.  The exact-list unguided recovery is now
explicitly documented as order-sensitive: it fails on the reversed direct
two-cycle CNF.
The permutation-insensitive recovery proves coverage up to `List.Perm`,
accepts every nonempty clause permutation of the direct two-cycle component
with the same generated two-spec target, and carries the local
`ParityEncoded.Class` witness plus per-assignment semantic preservation for its
compact GF(2) core.
The graph-specific statement now factors through a generic local theorem,
`enhancedSemanticExtractorCompleteOn_of_perm_generatedParitySpecs_two_sameSupport`:
for any canonical support, any nonempty clause permutation of the generated
true/false parity expansions over that support, and an ordinary one-block
recognizer miss, the production enhanced fallback splitter emits the generated
two-equation GF(2) target with no residual clauses.
This is still a returned-output soundness result, not a success/completeness
theorem for arbitrary same-support components.
The enhanced fallback splitter covers the direct two-cycle CNF exactly,
compacts to the direct two-equation GF(2) target, emits two compact equations,
and leaves zero residual ordinary clauses.  The production enhanced fallback
splitter now uses the permutation-insensitive two-charge recovery, so the
reversed direct two-cycle CNF is also certified residual-free as a concrete
regression instance, with two compact equations, the same compact GF(2) target,
expanded coverage up to `List.Perm`, and a combined
`EnhancedSemanticExtractorCompleteOn` theorem.  That regression theorem is
subsumed by
`enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle_of_perm`,
which proves the same production-path combined theorem for every nonempty
clause permutation of the direct two-cycle CNF by showing that the permuted CNF
still groups as one support component, the ordinary one-block recognizer still
misses, and the permutation-insensitive fallback recovers the certified
two-charge split.  It also has a
generic clause-preservation theorem: at both the grouped and full-CNF splitter
interfaces, the enhanced splitter's expanded CNF is a permutation of the input
ordinary CNF.  This is a coverage invariant, not a residual-free completeness
claim for arbitrary same-support components.  When an enhanced fallback split
is residual-free and all emitted blocks pass the executable syntactic check,
the output now packages as `EnhancedExtractorCompleteOn` and
`EnhancedSemanticExtractorCompleteOn` for the compact core.  This enhanced
package is kept separate from the older `ExtractorCompleteOn` API because that
API is tied to the baseline splitter.  The enhanced fallback splitter now also
has the same residual-free group-list append frame shape as the baseline
splitter: residual-free enhanced support-group splits compose across appended
support-group lists, and `EnhancedExtractorCompleteOn` /
`EnhancedSemanticExtractorCompleteOn` witnesses compose when the grouping pass
frames `F ++ G` as the concatenation of the two fragment groupings.  The same
composition theorem has caller-facing wrappers for canonical support-key
disjointness and ordinary support disjointness with a nonempty-right-CNF side
condition.  The exact-output frame is now explicit for both baseline and
enhanced splitters: once the two fragment split results are known, the split of
`F ++ G` emits the literal concatenation of the two emitted block lists under
the same side-condition packages.  Recognized canonical support groups now also instantiate the
enhanced fallback splitter directly: the ordinary recognized-group path is
residual-free for the enhanced splitter before any same-support fallback branch
is attempted, and recognized groups with successful syntactic upgrades package
as `EnhancedSemanticExtractorCompleteOn`.  The
`CertifiedRecognizedCNF` wrapper exposes this as a reusable certificate
boundary for arbitrary CNFs with supplied grouping, recognition,
syntactic-upgrade, and GF(2)-target permutation evidence.  The same certificate
now survives arbitrary whole-CNF clause permutation for the baseline
`ExtractorCompleteOn` and `SemanticExtractorCompleteOn` surfaces.  The
`ClausePermutedRecognizedBlock` wrapper is the single-component specialization:
literal-level clause permutation evidence proves the executable syntactic
recognition signal and derives the recognized-CNF certificate instead of asking
callers to supply the full syntactic-upgrade witness.  Its singleton constructor
also works in the other direction needed by executable recognition: a
single-group grouping fact, inferred block, and successful `toSyntactic?` check
produce the clause-permuted certificate.  The generated parity atom corollaries
connect this certificate interface back to actual encoder output before any
family-level append reasoning.  This has now been widened from canonical support
order to arbitrary nonempty clause permutations of a generated parity expansion
for the grouping/certificate obligation: clause order no longer has to be proved
by hand.  The generic canonical-sort theorem now proves that canonical
fingerprint recognition is invariant under those clause permutations, so
generated parity atoms in canonical support order also get the executable
recognizer result, `toSyntactic?` success, and expected compact equation without
caller-supplied canonical-signal or false-miss premises.  The new
`ClausePermutedRecognizedClass` packages the corresponding induction principle:
recognized single-component witnesses compose under canonical
support-key-disjoint appends, whole-CNF clause permutation, and GF(2)-target
permutation, yielding both baseline and enhanced combined extractor surfaces.
The baseline and enhanced whole-CNF permutation wrappers expose those surfaces
for arbitrary interleavings of a class instance.
This is not a full hidden affine recognizer-completeness theorem; callers must
still provide the clause-permuted recognized-block witnesses and the append
frame conditions outside the generated-atom wrapper.  The generated-atom
wrapper now also lifts straight into `ClausePermutedRecognizedClass`, so the
remaining gate is not clause ordering but stronger declarative-class
recognition, bounded overlap, and same-support recovery.
More specifically,
any CNF that
groups as one support component,
fails the ordinary one-block recognizer, and succeeds under the two-charge
same-support recovery now satisfies
`EnhancedSemanticExtractorCompleteOn` for the recovered compact GF(2) core.
This is a conditional single-group fallback theorem, not arbitrary
same-support completeness.  The direct two-cycle boundary now has a combined
`EnhancedSemanticExtractorCompleteOn` theorem: the semantic half comes from the
declarative cycle class, while the executable half comes from the enhanced
splitter's residual-free output and compact GF(2) core.  Combined with the
nondegenerate recognized-group path, this gives a uniform
`EnhancedSemanticExtractorCompleteOn` theorem for every derived cycle with
`1 < n`.  The folded spec-list surface now covers
generated parity families under ordinary support-disjointness, clause-key
disjointness, and spec-level canonical-key freshness, and the generated-spec
folds are proved equal to the existing incident-list and graph-encoding
Tseitin encoders.  The
graph-encoding theorem
`extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh` now
gives a reusable sufficient condition: every generated vertex block must be
nonempty, and canonical incident-support keys must be fresh in vertex-range
order.  The companion theorem
`extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos`
replaces the explicit nonempty-block premise with positive degree at every
vertex.  Standard cycle/Tseitin vertex blocks share edge variables between
adjacent vertex constraints, so they leave the support-disjoint lane. They now
fit the semantic class lane unconditionally and fit the executable extractor
lane through canonical support-key freshness for `2 < n`.
The `circulant12` scaffold has now been promoted from degree/count facts to a
concrete `GraphEncodingData` family, a proved fresh incident-support-key
condition, an unconditional declarative class theorem, and an unconditional
residual-free extractor theorem for every `2 < n`.  The enhanced
direct-recognizer surface is also instantiated for this family: the recognized
blocks pass the executable syntactic upgrade, and the graph-family fresh-key
and positive-degree facts discharge the generic side conditions.  The canonical extractor
still must not be advertised as a uniform residual-free extractor over
arbitrary graph encodings.

The semantic soundness theorem for `ParityEncoded.Class` is deliberately not
the hard part: the union case follows from ordinary CNF and GF(2) append
splitting.  The splitter recursion is now factored into
`ExtractorCompleteness.extractorCompleteOn_of_appendGroupRecognition`.  The
grouping recursion is now factored into
`GroupFrame.groupClausesByCanonicalSupport_append_of_fresh` and the computed
freshness premise is bridged by
`GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint`.  The
clause-key side condition is now stable under independent CNF permutations via
`GroupFrame.cnfClauseKeysDisjoint_of_perm`, and the grouping, exact splitter,
`ExtractorCompleteOn`, and `SemanticExtractorCompleteOn` append frames have
matching `_perm` wrappers.  This covers permuted fragments that are still
appended as two fragments; `AtomicClassBridge` exposes the same subcase through
`clausePermutedRecognizedClass_append_keyDisjoint_perm`.  The baseline
residual-free and combined semantic/executable surfaces also now cover swapped
append order under the same clause-key-disjointness premise, using
`GroupFrame.cnfClauseKeysDisjoint_symm` plus GF(2)-target permutation transport;
`AtomicClassBridge.clausePermutedRecognizedClass_append_comm_keyDisjoint`
exposes that class-level wrapper.  Arbitrary whole-CNF interleaving is now
covered separately for recognized source support groups by
`GroupFrame.splitArityFourParityCanonicalSupportGroups_gf2_perm_of_perm`,
`GroupFrame.extractorCompleteOn_groupClausesByCanonicalSupport_of_perm`, and
`GroupFrame.semanticExtractorCompleteOn_groupClausesByCanonicalSupport_of_perm`.
The
ordinary variable-support bridge is
`GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport`, with an
explicit nonempty-support side condition; without that side condition, empty
clauses can share the empty key under ordinary variable disjointness.  Generated
clause-complete parity expansions now discharge that side condition through
`GroupFrame.cnfClausesHaveNonemptySupport_clausesForVertex` when their variable
list is nonempty.  The same frame conditions now lift from residual-free
`ExtractorCompleteOn` to the combined `SemanticExtractorCompleteOn` surface via
`ExtractorCompleteness.semanticExtractorCompleteOn_append_of_groupAppend`,
`GroupFrame.semanticExtractorCompleteOn_append_of_clauseKeysDisjoint`, and
`GroupFrame.semanticExtractorCompleteOn_append_of_disjointSupport`.  The
baseline splitter additionally has exact-output append-frame wrappers,
`GroupFrame.splitArityFourParityCanonicalSupportGroups_append_of_clauseKeysDisjoint`
and
`GroupFrame.splitArityFourParityCanonicalSupportGroups_append_of_disjointSupport`,
which preserve known emitted block order under the same side conditions.  The
grouping and splitting passes now each preserve their
ordinary CNF coverage up to `List.Perm`, via
`GroupFrame.canonicalSupportClauseGroupsCNF_groupClausesByCanonicalSupport_perm`
and
`ExtractorCompleteness.splitCanonicalSupportClauseGroups_expandedCNF_perm`.
The broader whole-CNF interleaving gate has its first audited key-set layer:
`GroupFrame.groupKeys_groupClausesByCanonicalSupport_perm_of_perm` proves that
arbitrary CNF permutation preserves the executable support grouper's emitted
canonical support-key list up to `List.Perm`.  The supporting lemmas show the
grouper emits exactly the keys present in the input CNF and emits each key at
most once.  The gate also now has an audited per-key content layer:
`GroupFrame.groupClausesForKey_groupClausesByCanonicalSupport_perm` proves that
each executable key component contains exactly the input clauses with that key,
up to `List.Perm`, and
`GroupFrame.groupClausesForKey_groupClausesByCanonicalSupport_perm_of_perm`
proves that arbitrary CNF permutation preserves that per-key grouped clause
content.  The key-set and per-key content layers now combine into an audited
component relation:
`GroupFrame.supportGroupsKeyMatchedCNFPerm_groupClausesByCanonicalSupport_of_perm`
proves that arbitrary CNF permutation maps each executable source support group
to a target support group with the same canonical support key and permuted
clause content.  The recognizer layer is partially audited:
`canonicalParityBlockRecognitionSignal_eq_of_block_perm` proves
fixed-spec canonical recognition is invariant under clause permutation, while
`GroupFrame.inferCanonicalParityBlock_eq_some_of_perm_of_supportVars_cons`
transports public recognizer hits across nonempty support-homogeneous block
permutations.  The executable grouper now supplies that side condition for its
own nonempty components:
`GroupFrame.supportGroupClausesHaveCanonicalSupportVars_of_mem_groupClausesByCanonicalSupport_cons`
proves group-level support-variable homogeneity, and
`GroupFrame.inferCanonicalParityBlock_eq_some_of_perm_of_groupClausesByCanonicalSupport_cons`
transports public recognizer hits across clause permutations of actual grouped
components.  The function-level lift is now audited for an explicit aligned
component relation:
`GroupFrame.groupsRecognized_transport_of_alignedGroupCNFPerm` transports
residual-free `GroupsRecognized` evidence across aligned nonempty support-group
list permutations, and
`GroupFrame.splitCanonicalSupportClauseGroups_transport_of_alignedGroupCNFPerm`
lifts that transport through the canonical splitter while preserving the compact
GF(2) output exactly.  The pure group-order half is also audited:
`GroupFrame.groupsRecognized_transport_of_group_perm` transports recognized
groups across support-group list permutations, and
`GroupFrame.splitCanonicalSupportClauseGroups_transport_of_group_perm` lifts
that order transport through the splitter with compact GF(2) output preserved up
to `List.Perm`.  The key-matched residual-free lift is audited:
`GroupFrame.groupsRecognized_transport_of_keyMatchedCNFPerm` transports
recognition evidence across a key-matched component relation, and
`GroupFrame.splitCanonicalSupportClauseGroups_residualFree_of_keyMatchedCNFPerm`
lifts that result through the splitter.  The key-matched output lift is now
audited as well:
`GroupFrame.exists_alignedSupportGroupCNFPermNonempty_of_keyMatched` reorders
key-matched target groups into source-key order with per-component clause
permutation witnesses, and
`GroupFrame.groupsRecognized_groupClausesByCanonicalSupport_gf2_perm_of_perm`
transports recognized output for arbitrary whole-CNF permutations with compact
GF(2) output preserved up to `List.Perm`.
`GroupFrame.splitArityFourParityCanonicalSupportGroups_gf2_perm_of_perm`
specializes this to the executable full-CNF splitter.  This closes the
splitter-output portion of whole-CNF interleaving.  The result now feeds into
the caller-facing recognized-group, proof-carrying certificate, and
`ClausePermutedRecognizedClass` extractor-completeness surfaces.
Recognized atomic blocks now connect to the
`ParityEncoded.Class` constructors through `AtomicClassBridge`, provided the
caller supplies literal-level permutation evidence or the stronger syntactic
recognition signal; recognized block lists also connect when those certificates
are paired with append-disjointness.  Those certificate predicates now compose
over appended block lists, and accepted syntactic permutation signals supply
the per-block permutation certificates.  Cross-disjointness can now be derived
from ordinary support disjointness between covered CNFs.  A residual-free
result from the executable splitter now instantiates `ParityEncoded.Class` when
the emitted blocks satisfy the syntactic-signal and append-disjointness
predicates; the syntactic-signal premise can now be discharged by successful
`toSyntactic?` checks on all emitted blocks.  The same residual-free split
result now instantiates the combined `SemanticExtractorCompleteOn` package for
the emitted compact GF(2) formula, so this lane no longer requires a separate
manual pairing of the class bridge and extractor-completeness witness.  The
same packaging is now available directly from recognized canonical support
groups, with a singleton wrapper for the one-component atom case.
Recognized group outputs now
cover their source CNFs up to permutation, and ordinary source-level
disjointness transfers across those permutations to the emitted covered CNFs.
Singleton canonical block lists now discharge their append-disjointness
obligation directly, so a one-component recognized group with a successful
`toSyntactic?` check instantiates the atom case without an extra certificate.
Together these yield a support-disjoint append-fragment bridge for `F ++ G`;
the relaxed append variant keeps the source-level grouping frame but no longer
requires internal append-disjointness of either emitted block list.
Generated parity blocks now also provide the single-support-group premise for
the atom bridge whenever the expansion is nonempty.  Generated parity
expansions now self-recognize under both the syntactic permutation recognizer
and the canonical fingerprint recognizer, and an accepted syntactic signal now
discharges the executable `toSyntactic?` upgrade check for a canonical block.
Support inference from the first clause of a nonempty generated parity
expansion now recovers the canonicalized generator support, and under the
explicit `VarsInCanonicalSupportOrder` normal form it recovers the exact
generator variable list.  Consequently, the public two-charge canonical
recognizer now returns a block and that block passes `toSyntactic?` for both
generated charges in normal form.  The true-charge false-first recognizer miss
is discharged by generated true/false canonical block-fingerprint separation,
with the separation proved through the all-false fingerprint witness and the
generated-clause reverse membership theorem.  These pieces now lift through the
append-recognition bridge to both a binary support-disjoint
extractor-completeness theorem for two generated normal-form parity expansions
and prefix-plus-one induction-step theorems for recognized generated prefixes.
They now also package into arbitrary finite generated-family
extractor-completeness theorems under both support-disjointness and accumulated
canonical support-key freshness, with folded generated-spec-list interfaces for
both side-condition packages.  Independently, all folded generated-spec lists
instantiate `ParityEncoded.Class` through the semantic append/gluing
constructor, and folded specs are proved to align with the existing
incident-list and graph-encoding Tseitin encoders.  Concrete graph encodings
therefore inherit unconditional declarative class membership, while
residual-free extraction still requires nonempty generated vertex blocks, or
positive vertex degree, plus fresh canonical incident-support keys.  The
`circulant12` family now has the encoding, positive-degree, and fresh-key side
conditions discharged, yielding unconditional declarative class and
residual-free extractor theorems for that family, plus the enhanced
direct-recognizer theorem with executable syntactic upgrades.  The cycle-family executable
extractor theorem is now discharged for the concrete
`generatedParitySpecsForCycle` spec-level canonical-key freshness certificate
under `2 < n`, while the declarative cycle class theorem holds for all `1 < n`.
Its CNF-nonempty constructor witness, filtered-incident normal order, cycle-edge
endpoint membership/exclusion facts, pairwise distinct incident-support keys,
and prefix freshness induction are now discharged uniformly.  The enhanced
splitter now also proves the combined semantic/enhanced-executable cycle
theorem uniformly for all `1 < n` by combining the `2 < n` recognized-group
lane with the certified same-support fallback at `n = 2`; the next lift is a
class-to-extractor completeness theorem or bounded-overlap/function-level frame
theorem for graph encodings, fresh-key analysis on graph families beyond cycles
and `circulant12`, plus generalization of the executable same-support recovery
theorem that now finds the already-certified fallback blocks and powers an
enhanced residual-free splitter for the `n = 2` boundary.
