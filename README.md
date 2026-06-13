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

## Working v0.2 Surface

- `ParityEncoded.Class.sound`: semantic soundness for a declarative
  fixed-ambient class of parity-encoded CNFs.  This does not yet claim extractor
  completeness for the canonical fingerprint splitter.
- `ParityEncoded.Class.append`: a semantic gluing constructor for appended
  parity-encoded CNFs.  Unlike the frame-oriented `union` constructor, this
  rule permits overlapping variables, matching ordinary Tseitin vertex blocks
  that share edge variables.
- `ExtractorCompleteness.extractorCompleteOn_of_appendGroupRecognition`: a
  function-level splitter lemma reducing union-fragment completeness to the
  canonical support grouping/frame premise.
- `ExtractorCompleteness.splitCanonicalSupportClauseGroups_expandedCNF_perm`:
  splitting canonical support groups preserves all ordinary clauses up to
  permutation, moving recognized groups into the core and unrecognized groups
  into residual CNF.
- `ExtractorCompleteness.splitCanonicalSupportClauseGroups_append_of_residual_free`:
  residual-free support-group splits compose across appended support-group
  lists, without re-opening the recognizer proofs for either side.
- `ExtractorCompleteness.extractorCompleteOn_append_of_groupAppend`: two
  residual-free `ExtractorCompleteOn` witnesses compose when the grouping pass
  frames `F ++ G` as the concatenation of the two fragment groupings.
- `ExtractorCompleteness.semanticExtractorCompleteOn_append_of_groupAppend`:
  the same frame premise composes the combined semantic plus residual-free
  extractor package, reusing ordinary CNF and GF(2) append splitting for the
  semantic half.
- `GroupFrame.groupClausesByCanonicalSupport_append_of_fresh`: a structural
  frame theorem showing that canonical support grouping commutes with append
  when the suffix clause-support keys are fresh for the prefix groups.
- `GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint`: a
  caller-facing bridge replacing computed-group freshness with operational
  clause-key disjointness between the two CNFs.
- `GroupFrame.cnfClauseKeysDisjoint_of_perm`,
  `GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint_perm`,
  the corresponding splitter/extractor/semantic `_perm` wrappers,
  `GroupFrame.extractorCompleteOn_append_comm_of_clauseKeysDisjoint`,
  `GroupFrame.semanticExtractorCompleteOn_append_comm_of_clauseKeysDisjoint`,
  and the matching `AtomicClassBridge` class wrappers:
  clause-key append frames are stable when each fragment is independently
  clause-permuted before append, and residual-free completeness also survives
  swapping the two append fragments while transporting the GF(2) target back to
  the caller's order.  This is a proved subcase of the broader whole-CNF
  interleaving gate.
- `GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport`: a
  variable-support bridge showing grouping commutes with append under
  `ParityEncoded.DisjointSupport`, provided the right-hand CNF has no
  empty-support clauses.
- `GroupFrame.splitArityFourParityCanonicalSupportGroups_append_of_clauseKeysDisjoint`
  and
  `GroupFrame.splitArityFourParityCanonicalSupportGroups_append_of_disjointSupport`:
  exact splitter-frame theorems.  If the two fragments already split
  residual-free with known block lists, splitting `F ++ G` emits exactly the
  left block list followed by the right block list, under the same
  clause-key-disjoint or ordinary support-disjoint side-condition packages.
- `GroupFrame.extractorCompleteOn_append_of_clauseKeysDisjoint` and
  `GroupFrame.extractorCompleteOn_append_of_disjointSupport`: caller-facing
  frame-composition theorems showing residual-free extractor completeness
  composes under canonical support-key disjointness, or ordinary support
  disjointness with the same nonempty-right-CNF side condition.
- `GroupFrame.semanticExtractorCompleteOn_append_of_clauseKeysDisjoint` and
  `GroupFrame.semanticExtractorCompleteOn_append_of_disjointSupport`:
  caller-facing frame-composition theorems for the combined
  `SemanticExtractorCompleteOn` surface under the same two side-condition
  packages.
- `GroupFrame.groupClausesByCanonicalSupport_cons_eq_single_of_same_key`: a
  same-key grouping theorem showing any nonempty CNF whose clauses share one
  canonical support key groups into one executable support component.
- `GroupFrame.cnfClausesHaveCanonicalSupportKey_clausesForVertex`: proves every
  clause generated by `clausesForVertex vars charge` has the canonical support
  key induced by `vars`.
- `GroupFrame.cnfClausesHaveCanonicalSupportVars_clausesForVertex`: proves every
  clause generated by `clausesForVertex vars charge` has the same canonicalized
  support-variable list.
- `GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons`:
  combines those facts to show a nonempty generated parity expansion groups as
  exactly one canonical support component.
- `GroupFrame.parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons`:
  proves that support inference from the first clause of a nonempty generated
  parity expansion recovers the canonicalized generator support.
- `GroupFrame.parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons_normal`:
  specializes that result to exact support recovery when the generator variable
  list is already in canonical support order.
- `GroupFrame.cnfClausesHaveNonemptySupport_clausesForVertex`: discharges that
  nonempty-support side condition for generated clause-complete parity
  expansions whose variable list is nonempty.
- `GroupFrame.canonicalSupportClauseGroupsCNF_groupClausesByCanonicalSupport_perm`:
  canonical support grouping preserves the input CNF clauses up to
  permutation.
- `GroupFrame.mem_groupKeys_groupClausesByCanonicalSupport_iff`,
  `GroupFrame.nodup_groupKeys_groupClausesByCanonicalSupport`, and
  `GroupFrame.groupKeys_groupClausesByCanonicalSupport_perm_of_perm`: the
  executable support grouper emits exactly the canonical support keys present
  in the input CNF, emits each key at most once, and preserves the grouped key
  list up to `List.Perm` under arbitrary whole-CNF permutation.  This is the
  key-set layer for the whole-CNF interleaving gate.
- `GroupFrame.groupClausesForKey_groupClausesByCanonicalSupport_perm` and
  `GroupFrame.groupClausesForKey_groupClausesByCanonicalSupport_perm_of_perm`:
  for each canonical support key, the executable groups contain exactly the
  input clauses with that key up to `List.Perm`, and arbitrary whole-CNF
  permutation preserves that per-key grouped clause content.  This closes the
  per-key content layer of the interleaving gate.
- `GroupFrame.supportGroupsKeyMatchedCNFPerm_groupClausesByCanonicalSupport_of_perm`:
  arbitrary whole-CNF permutation induces a key-matched component relation
  between executable support-group outputs: every source group has a target
  group with the same canonical support key and clause content preserved up to
  `List.Perm`.  This closes the key-matched component derivation.
- `GroupFrame.exists_alignedSupportGroupCNFPermNonempty_of_keyMatched`,
  `GroupFrame.groupsRecognized_groupClausesByCanonicalSupport_gf2_perm_of_perm`,
  and `GroupFrame.splitArityFourParityCanonicalSupportGroups_gf2_perm_of_perm`:
  arbitrary whole-CNF permutation now preserves residual-free recognition of the
  executable canonical splitter and preserves the emitted compact GF(2) output
  up to `List.Perm`, whenever the source support groups were fully recognized.
  This closes the splitter-output part of the whole-CNF interleaving gate.
- `GroupFrame.extractorCompleteOn_groupClausesByCanonicalSupport_of_perm` and
  `GroupFrame.semanticExtractorCompleteOn_groupClausesByCanonicalSupport_of_perm`:
  the whole-CNF interleaving result now lifts to the caller-facing residual-free
  extractor-completeness surface, and to the combined semantic/executable
  surface when the source CNF is already known semantically equivalent to the
  compact GF(2) target.
- `canonicalParityBlockRecognitionSignal_eq_of_block_perm`,
  `GroupFrame.inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_inferredSpec_eq`,
  and
  `GroupFrame.inferCanonicalParityBlock_eq_some_of_perm_of_supportVars_cons`:
  fixed-spec canonical recognition is invariant under clause permutation, and
  the inferred recognizer transports hits across nonempty support-homogeneous
  block permutations.  This closes the recognizer-transport step under an
  explicit support-stability side condition; it does not yet prove that every
  executable support group supplies that condition or that splitter output is
  invariant under arbitrary interleaving.
- `GroupFrame.supportGroupClausesHaveCanonicalSupportVars_of_mem_groupClausesByCanonicalSupport_cons`
  and
  `GroupFrame.inferCanonicalParityBlock_eq_some_of_perm_of_groupClausesByCanonicalSupport_cons`:
  nonempty executable support groups now supply the recognizer's support
  stability condition automatically, and public recognizer hits transport across
  clause permutations of those grouped components.  This closes the current
  first-clause support-inference issue for actual grouped blocks.
- `GroupFrame.groupsRecognized_transport_of_alignedGroupCNFPerm` and
  `GroupFrame.splitCanonicalSupportClauseGroups_transport_of_alignedGroupCNFPerm`:
  aligned nonempty support-group list permutations transport residual-free
  `GroupsRecognized` evidence through the canonical splitter, preserving the
  compact GF(2) output exactly and stored block CNFs up to per-component
  permutation.  This closes the list-level transport layer once aligned grouped
  components are supplied.
- `GroupFrame.groupsRecognized_transport_of_group_perm` and
  `GroupFrame.splitCanonicalSupportClauseGroups_transport_of_group_perm`:
  recognized support groups also transport across pure group-list permutations,
  with compact GF(2) output preserved up to `List.Perm`.  This closes the
  group-order part of whole-CNF interleaving; the key-matched alignment theorem
  upgrades the arbitrary whole-CNF permutation path to the same compact-output
  guarantee.
- `mem_clausesForVertex_imp_exists_bad_row`: every clause in a generated
  parity expansion comes from a Boolean row whose parity disagrees with the
  requested charge.
- `AtomicClassBridge.class_of_recognizedParityCNFBlock`: turns an existing
  proof-carrying recognized parity block into a `ParityEncoded.Class` atom.
- `AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlock_perm`: turns a
  canonical-fingerprint recognized atom into a `ParityEncoded.Class` atom when
  literal-level permutation evidence is supplied.
- `AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlock_syntacticSignal`:
  the same bridge when the stronger syntactic permutation recognizer accepts
  the canonical block/spec pair.
- `AtomicClassBridge.canonicalFingerprintRecognizedBlock_toSyntactic_isSome_of_syntacticSignal`:
  proves that an accepted syntactic signal discharges the executable
  `toSyntactic?` upgrade check for a canonical block.
- `AtomicClassBridge.parityBlockRecognitionSignal_clausesForVertex_self` and
  `AtomicClassBridge.canonicalParityBlockRecognitionSignal_clausesForVertex_self`:
  generated parity expansions self-recognize under both the syntactic
  permutation recognizer and canonical fingerprint recognizer.
- `AtomicClassBridge.mem_canonicalBlockFingerprint_iff`: characterizes
  membership in a sorted canonical block fingerprint by membership of a source
  clause with that canonical clause fingerprint.
- `AtomicClassBridge.mem_canonicalBlockFingerprint_append_iff`: distributes
  canonical block-fingerprint membership across ordinary CNF append.
- `AtomicClassBridge.mem_canonicalClauseFingerprint_iff`: characterizes
  membership in a sorted canonical clause fingerprint by membership of a source
  literal with that signed-literal atom.
- `AtomicClassBridge.evenLiteralAtom_not_mem_canonicalClauseFingerprint_allFalse`:
  proves that all-false assignment clauses contain no even signed-literal atoms.
- `AtomicClassBridge.exists_evenLiteralAtom_mem_canonicalClauseFingerprint_clauseForAssignment`:
  proves that any row containing a true bit contributes an even signed-literal
  atom to its forbidden assignment clause fingerprint.
- `TseitinCNFData.allAssignments_nodup`,
  `TseitinCNFData.allAssignments_count_replicate_false`, and
  `TseitinCNFData.boolList_eq_replicate_false_of_true_not_mem`:
  record row-enumeration uniqueness facts used to isolate the all-false source
  row without relying on executable search.
- `AtomicClassBridge.canonicalBlockFingerprint_ne_of_mem_not_mem`: separates
  two block fingerprints using a fingerprint present on one side and absent on
  the other.
- `AtomicClassBridge.allFalseClauseFingerprint_mem_canonicalBlockFingerprint_clausesForVertex_true`:
  proves that the all-false assignment clause fingerprint is present in every
  generated true-charge parity block.
- `AtomicClassBridge.row_eq_replicate_false_of_canonicalClauseFingerprint_eq_allFalse`
  and
  `AtomicClassBridge.clause_eq_allFalse_of_mem_clausesForVertex_true_and_fingerprint_eq`:
  prove that, inside a generated parity block, the all-false canonical
  fingerprint identifies the all-false row and its generated clause.
- `AtomicClassBridge.allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_true_eq_one`:
  strengthens the true-charge block witness from existence to exact
  multiplicity: a generated true-charge block contains exactly one all-false
  clause fingerprint.
- `AtomicClassBridge.allFalseClauseFingerprint_count_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges_eq_true_count`:
  sums that exact single-block contribution across a merged generated
  same-support component: the merged all-false fingerprint count equals the
  hidden true-charge multiplicity.
- `AtomicClassBridge.allFalseClauseFingerprint_count_targetFingerprint_eq_true_count_of_perm_supportCharges`:
  transports the exact merged count across clause permutations of the generated
  same-support component.
- `AtomicClassBridge.canonicalBlockFingerprint_clausesForVertex_true_false_ne_of_allFalseFingerprint_not_mem`:
  reduces generated true/false block-fingerprint separation to absence of that
  all-false fingerprint from the generated false-charge block.
- `AtomicClassBridge.allFalseClauseFingerprint_not_mem_canonicalBlockFingerprint_clausesForVertex_false`:
  discharges that absence theorem for generated false-charge blocks using the
  reverse membership theorem for generated parity clauses.
- `AtomicClassBridge.canonicalBlockFingerprint_clausesForVertex_true_false_ne`:
  proves generated true- and false-charge parity blocks have different
  canonical block fingerprints.
- `AtomicClassBridge.canonicalParityBlockRecognitionSignal_eq_false_of_fingerprint_ne`:
  turns a canonical block-fingerprint inequality into a false canonical
  recognizer signal.
- `AtomicClassBridge.canonicalParityBlockRecognitionSignal_clausesForVertex_true_false_eq_false_of_fingerprint_ne`:
  specializes that cut to generated true-charge blocks tested against the
  corresponding false-charge spec.
- `AtomicClassBridge.inferCanonicalParityBlockWithCharge_clausesForVertex_self_toSyntactic`:
  if support inference recovers the same variable list used to generate a
  parity expansion, the one-charge executable canonical recognizer returns a
  block and the block passes `toSyntactic?`.
- `AtomicClassBridge.inferCanonicalParityBlockWithCharge_clausesForVertex_normal_toSyntactic`:
  discharges that support-inference premise for nonempty generated parity
  expansions whose variable list is already in canonical support order.
- `AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_false_normal_toSyntactic`:
  lifts nonempty generated false-charge parity expansions in canonical support
  order through the public two-charge recognizer.
- `AtomicClassBridge.inferCanonicalParityBlockWithCharge_eq_none_of_signal_false`:
  turns an explicitly false inferred canonical fingerprint signal into a
  one-charge recognizer miss.
- `AtomicClassBridge.inferCanonicalParityBlockWithCharge_clausesForVertex_true_false_eq_none_of_signal_false`:
  reduces the generated true-charge block's false-first miss to the canonical
  signal for the corresponding false-charge spec being false.
- `AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_falseMiss`:
  reduces the corresponding true-charge public-recognizer case to the exact
  obligation that the recognizer's false-charge attempt misses.
- `AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_falseSignal`:
  gives the same public true-charge recognizer result from the sharper
  canonical false-signal obligation.
- `AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_fingerprint_ne`:
  sharpens the generated true-charge recognizer obligation again to inequality
  of the true- and false-charge canonical block fingerprints.
- `AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic`:
  discharges that final fingerprint obligation, so nonempty generated
  true-charge parity expansions in canonical support order now pass the public
  two-charge recognizer and its `toSyntactic?` upgrade.
- `AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic`:
  unifies the generated true- and false-charge recognizer cases and records
  that the emitted compact GF(2) equation is exactly
  `parityClauseForVertex vars charge`.
- `AtomicClassBridge.extractorCompleteOn_clausesForVertex_normal`: proves the
  executable canonical splitter is residual-free and GF(2)-complete on one
  nonempty generated parity expansion in canonical support order.
- `AtomicClassBridge.extractorCompleteOn_disjoint_clausesForVertex_append_normal`:
  proves the executable canonical splitter is residual-free and GF(2)-complete
  on two generated parity expansions when their supports are disjoint and the
  right-hand block has nonempty support.
- `AtomicClassBridge.canonicalFingerprintRecognizedBlocksGF2_append`: records
  that the compact GF(2) output of appended recognized-block lists is ordinary
  list append.
- `AtomicClassBridge.extractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized`:
  provides the support-disjoint induction step: a recognized prefix can be
  extended by one generated normal-form parity expansion while preserving
  residual-free extractor completeness and appending the generated GF(2)
  equation.
- `AtomicClassBridge.extractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint`:
  provides the weaker executable induction step: a recognized prefix can be
  extended by one generated normal-form parity expansion when the new block's
  canonical clause-support key is fresh for the prefix.
- `AtomicClassBridge.enhancedExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint`
  and
  `AtomicClassBridge.enhancedExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized`:
  the same prefix-plus-one induction step for the production-shaped enhanced
  fallback splitter, with both canonical-key-fresh and support-disjoint entry
  points.
- `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint`
  and
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized`:
  the combined semantic/enhanced-executable induction step when the recognized
  prefix blocks pass the executable syntactic upgrade; the generated appended
  atom supplies its own syntactic upgrade through the canonical recognizer.
- `AtomicClassBridge.GeneratedSupportDisjointFamily`: a snoc-order finite
  generated-family class for nonempty normal-form parity expansions whose new
  block is support-disjoint from the accumulated prefix at every step.
- `AtomicClassBridge.groupsRecognized_exists_of_generatedSupportDisjointFamily`:
  proves that every generated support-disjoint family has a recognized
  canonical support-group decomposition and the expected compact GF(2) output
  up to `List.Perm`.
- `AtomicClassBridge.extractorCompleteOn_of_generatedSupportDisjointFamily`:
  proves the executable canonical splitter is residual-free and GF(2)-complete
  for every generated support-disjoint family in that class.
- `AtomicClassBridge.GeneratedKeyDisjointFamily`: a snoc-order finite
  generated-family class whose new block has a fresh canonical support key
  relative to the accumulated prefix.  This allows overlapping variables when
  the full generated parity supports are distinct.
- `AtomicClassBridge.extractorCompleteOn_of_generatedKeyDisjointFamily`: proves
  the executable canonical splitter is residual-free and GF(2)-complete for
  every generated key-disjoint family in that class.
- `AtomicClassBridge.class_of_generatedKeyDisjointFamily` and
  `AtomicClassBridge.class_of_generatedKeyDisjointSpecList`: turn generated
  key-disjoint family certificates into declarative `ParityEncoded.Class`
  witnesses.  The key-disjoint premise remains necessary for the executable
  extractor lane, but semantic class membership itself composes through the new
  append/gluing constructor.
- `ExtractorCompleteness.SemanticExtractorCompleteOn` and
  `ExtractorCompleteness.semanticExtractorCompleteOn_of_class`: package
  per-assignment CNF/GF(2) equivalence together with residual-free executable
  extractor completeness.  The bridge requires both a declarative class
  witness and a separate extractor-completeness witness, so it does not claim
  extractor completeness for arbitrary `ParityEncoded.Class` witnesses.
- `AtomicClassBridge.semanticExtractorCompleteOn_of_generatedKeyDisjointFamily`
  and
  `AtomicClassBridge.semanticExtractorCompleteOn_of_generatedKeyDisjointSpecList`:
  prove the combined semantic/executable extraction claim for generated
  key-disjoint families and folded generated-spec lists.
- `AtomicClassBridge.generatedParitySpecsCNF_fromIncident` and
  `AtomicClassBridge.generatedParitySpecsGF2_fromIncident`: prove that folded
  generated parity specs are exactly the existing incident-list Tseitin CNF and
  direct GF(2) encoders.
- `AtomicClassBridge.generatedParitySpecsGF2_eq_map` and
  `AtomicClassBridge.class_of_generatedParitySpecs`: show that folded generated
  parity specs form a declarative `ParityEncoded.Class` with no key-freshness
  or disjointness side condition.  Those side conditions belong to the
  executable residual-free extractor lane.
- `AtomicClassBridge.generatedParitySpecsFromIncident_append_singleton`: records
  the snoc shape needed to induct over generated incident-spec vertex lists.
- `AtomicClassBridge.generatedParitySpecsCNF_fromEncoding` and
  `AtomicClassBridge.generatedParitySpecsGF2_fromEncoding`: lift that alignment
  to concrete graph encodings.
- `AtomicClassBridge.generatedParitySpecsForCycle`: names the generated-spec
  list for the derived directed cycle family.
- `AtomicClassBridge.clausesForVertex_exists_cons_of_vars_ne_empty` and
  `AtomicClassBridge.incidentClausesForVertex_exists_cons_of_degree_pos`:
  replace arity-specific nonempty-block bookkeeping with a reusable theorem:
  any generated parity expansion over a nonempty variable list, and therefore
  any incident-generated vertex block with positive degree, supplies the
  `c :: tail` CNF witness required by generated-spec `snoc` certificates.
- `AtomicClassBridge.cycleIncidentIndices_length_eq_four` and
  `AtomicClassBridge.cycleClausesForVertex_exists_cons`: prove that every
  derived-cycle vertex incident-index list has arity four and therefore supplies
  the nonempty CNF-block witness required by generated-spec `snoc`
  certificates.
- `AtomicClassBridge.allFin_filter_varsInCanonicalSupportOrder`,
  `AtomicClassBridge.incidentIndices_varsInCanonicalSupportOrder`, and
  `AtomicClassBridge.cycleIncidentIndices_varsInCanonicalSupportOrder`: prove
  that filtered `allFin` incident-index lists are already in the canonical
  support order expected by the executable recognizer.
- `AtomicClassBridge.cycleEdgeAt_even_eq`,
  `AtomicClassBridge.cycleEdgeAt_odd_eq`,
  `AtomicClassBridge.cycleCanonicalIncidentSupportKey_mem_even`, and
  `AtomicClassBridge.cycleCanonicalIncidentSupportKey_mem_odd`: identify the
  exact directed edge variables at indices `2*u` and `2*u + 1` in the derived
  cycle and prove those indices occur in vertex `u`'s canonical incident key.
- `AtomicClassBridge.cycleCanonicalIncidentSupportKey_not_mem_even_of_not_endpoint`
  and
  `AtomicClassBridge.cycleCanonicalIncidentSupportKey_not_mem_odd_of_not_endpoint`:
  prove the corresponding endpoint-only exclusion facts, so an edge index is
  absent from every non-endpoint vertex key.
- `AtomicClassBridge.cycleCanonicalIncidentSupportKeys_ne_of_ne`: proves that
  any two distinct vertices in a derived cycle with `2 < n` have distinct
  canonical incident-support keys.
- `AtomicClassBridge.twoCycleCanonicalIncidentSupportKeys_eq` and
  `AtomicClassBridge.twoCycleSecondVertexFreshnessStep_false`: document the
  exact `n = 2` boundary where the current key-fresh generated-spec lane cannot
  apply, because both two-cycle vertex constraints have the same canonical
  incident-support key.
- `AtomicClassBridge.twoCycleCanonicalSplitterBlocks_length`,
  `AtomicClassBridge.twoCycleCanonicalSplitterResidualCNF_eq`, and
  `AtomicClassBridge.twoCycleCanonicalSplitter_not_residualFree_for_directGF2`:
  certify the executable side of that boundary.  On the direct two-cycle CNF,
  the current canonical support splitter emits zero recognized blocks, leaves
  all 16 clauses residual, and therefore cannot satisfy residual-free
  `ExtractorCompleteOn` for the direct two-equation GF(2) target, even though
  the semantic `ParityEncoded.Class` lane covers the family for all `1 < n`.
- `AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_CNF_eq`,
  `AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_GF2_eq`, and
  `AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_toSyntacticOk`:
  define the specification-side same-support fallback target.  Any generated
  parity-spec list maps pointwise to canonical recognized blocks that cover
  exactly the generated ordinary CNF fold, compact exactly to the generated
  GF(2) fold, and pass the executable syntactic upgrade check.
- `AtomicClassBridge.twoCycleSameSupportFallback_exists`: instantiates that
  fallback target at the certified `n = 2` boundary.  There are exactly two
  canonical recognized blocks covering the direct two-cycle CNF and compacting
  to the direct two-equation GF(2) target.  The baseline canonical splitter
  residualizes the merged support component; the enhanced two-charge fallback
  splitter below is the production-shaped repair for this boundary.
- `AtomicClassBridge.generatedParitySpecsFallbackDecomposition_*` and
  `AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_*`: lift the
  fallback target into the same residual-carrying decomposition structure used
  by the production canonical splitter.  The generic generated-spec
  decomposition is residual-free, its expanded CNF and compact GF(2) core are
  exactly the generated folds, and the concrete two-cycle instance has two
  equations, zero residual clauses, and sixteen covered expanded clauses.
- `AtomicClassBridge.recoverSameSupportGeneratedParitySpecs?` and
  `AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecs?`:
  introduce a guided executable same-support recovery pass.  It accepts a
  merged CNF component plus a proposed generated-spec split only when the
  generated ordinary CNF fold exactly covers that component; any returned
  decomposition is proved to cover the input component, have empty residual,
  compact to the generated GF(2) fold, and emit blocks that pass the executable
  syntactic-upgrade check.
- `AtomicClassBridge.cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_sameSupport`,
  `AtomicClassBridge.groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_sameSupport`,
  `AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecsPerm?`,
  `AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_eq_some_of_perm_generatedParitySpecs_sameSupport`,
  and
  `AtomicClassBridge.class_of_recoverSingleMergedSupportGroupFromGeneratedSpecsPerm`:
  generalize the guided same-support lane beyond the two-charge boundary.  For
  any supplied generated-spec list whose specs all use one canonical support,
  every nonempty clause permutation of its generated CNF groups as one
  canonical support component, the permutation-insensitive guided recovery
  succeeds on that grouped component, and any successful return carries a local
  `ParityEncoded.Class` witness.  This proves the verification/grouping half
  for arbitrary supplied same-support decompositions; it still does not infer
  the spec list from an arbitrary CNF.
- `AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm?`,
  `AtomicClassBridge.parityCandidateCanonicalSupportFromBlock_eq_of_perm_generatedParitySpecs_sameSupport`,
  `AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_eq_some_of_perm_supportCharges`,
  `AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_perm_supportCharges`,
  and
  `AtomicClassBridge.class_of_recoverSingleMergedSupportGroupFromChargesPerm`:
  remove the support variables from the guided same-support input.  Given a
  correct charge list, the recovery pass infers the canonical support from the
  merged component, validates the generated CNF up to clause permutation, and
  returns a local `ParityEncoded.Class` witness.  The remaining discovery
  problem is now the charge list and its multiplicities.
- `AtomicClassBridge.chargeListsUpTo`,
  `AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm?`,
  `AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges`,
  `AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges`,
  and
  `AtomicClassBridge.class_of_recoverSingleMergedSupportGroupFromChargeSearchPerm`:
  introduce a bounded charge-search lane.  Instead of supplying the exact
  charge list, callers supply a maximum number of charges; the recovery pass
  searches every Boolean charge list up to that bound, infers the support from
  the component, and proves success whenever the true charge list is within the
  bound.
- `AtomicClassBridge.generatedParitySpecsForSupportCharges_length_le_cnf_length_of_vars_ne_empty`,
  `AtomicClassBridge.charges_length_le_of_perm_generatedParitySpecsForSupportCharges`,
  `AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_componentBound`,
  `AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_componentBound`,
  and
  `AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_exists_of_perm_supportCharges_componentBound`:
  prove that, for a nonempty support generated same-support component, the
  component's own clause count is a safe charge-search bound.  This still is
  not arbitrary same-support recognition: the search no longer needs an
  external bound in this generated lane, but it still does not infer the charge
  multiplicities directly from an arbitrary component.  The production-shaped
  fallback branch now keeps the legacy two-charge fast path, then tries direct
  arity-three/four count-derived recovery, then tries the inferred support-size
  direct branch for any nonempty generated support.  The deterministic
  `AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_eq_nonexhaustive_of_perm_supportCharges`
  theorem proves that these non-enumerative branches exhaust the production path
  for nonempty generated same-support components; exhaustive component-bound
  charge search remains only the last resort outside those generated hypotheses.
  A successful production fallback now also lifts to the declarative semantic
  class via
  `AtomicClassBridge.class_of_recoverSameSupportGroupWithChargeSearchFallback`
  and to per-assignment CNF/GF(2) preservation via
  `AtomicClassBridge.semanticPreservation_of_recoverSameSupportGroupWithChargeSearchFallback`.
  The generated component theorem now bundles those facts directly:
  `AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_exists_class_of_perm_supportCharges_componentBound`
  returns a production fallback result with a `ParityEncoded.Class` witness, and
  `AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_exists_semanticPreservation_of_perm_supportCharges_componentBound`
  returns one with assignment-level semantic preservation.
- `AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_iff_forall_mem`,
  `AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_iff_eraseDups`,
  `AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_iff_charge_presence`,
  and
  `AtomicClassBridge.not_gf2Sat_generatedParitySpecsForSupportCharges_of_mem_false_true`:
  separate same-support charge semantics from syntactic multiplicity.  The
  generated GF(2) formula depends only on which Boolean charges appear, duplicate
  charges are semantically redundant, and a same-support generated GF(2) formula
  containing both charges is unsatisfiable.  The remaining multiplicity problem
  is therefore exact CNF coverage, not added GF(2) semantic strength.
- `AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_rhs_eq`,
  `AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_rhs_count_true`,
  `AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_rhs_count_false`,
  `AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_eq`,
  `AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_count_true`,
  `AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_count_false`,
  `AtomicClassBridge.allFalseClauseFingerprint_signal_clausesForVertex_eq_charge`,
  `AtomicClassBridge.generatedParitySpecsCNF_forSupportCharges_cons`,
  `AtomicClassBridge.allFalseClauseFingerprint_mem_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges_iff_true_mem`,
  `AtomicClassBridge.allFalseClauseFingerprint_mem_targetFingerprint_iff_true_mem_of_perm_supportCharges`,
  `AtomicClassBridge.allFalseClauseFingerprint_count_true_le_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges`,
  `AtomicClassBridge.allFalseClauseFingerprint_count_true_le_targetFingerprint_of_perm_supportCharges`,
  `AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_allFalseFingerprint_signals_eq`,
  and the matching
  `AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_coreGF2_*`
  and
  `AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_block_charges_*`
  plus
  `AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_allFalseFingerprint_*`
  theorems: both the canonical recognized-block list and the compact generated
  GF(2) core preserve the exact charge list and its true/false multiplicities
  once a same-support split has been supplied or recovered.  The block layer
  also exposes the true-charge positions through the all-false clause
  fingerprint, a CNF-side witness rather than a GF(2) semantic fact.  Before
  the split is known, the merged same-support CNF already exposes true-charge
  presence through that fingerprint, and this presence signal transports across
  clause permutation.  The merged fingerprint count now exactly equals
  true-charge multiplicity for generated same-support components, and that
  exact count transports across clause permutation.  The all-false row and
  clause uniqueness bridge proves that the all-false fingerprint has a unique
  generated source inside a true-charge block, the single-block count theorem
  proves that each true-charge block contributes exactly one such fingerprint,
  and the merged-count theorem sums those contributions across the component.
  This removes the local counting ambiguity needed for direct count
  reconstruction.  The direct recovery theorem surface is now factored through
  a block-size-generic statement: once a caller certifies that every generated
  block in the same-support component has positive CNF length `k`, component
  length and all-false fingerprint count determine a canonical charge
  representative without exhaustive charge enumeration.  The base generator now
  proves the uniform nonempty block-size formula
  `clausesForVertex_length_eq_pow_pred_of_vars_ne_empty`, namely
  `2^(vars.length - 1)` clauses for support arity `vars.length`.  The
  production splitter now wires that formula through an inferred support-size
  direct branch after the older arity-three/four branch and before exhaustive
  charge-list enumeration.
  `AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_directTargetCharges_supportSize_iff_of_perm_supportCharges`
  records the semantic consequence: the count-derived compact GF(2) target is
  assignment-equivalent to the hidden generated charge source.
  `AtomicClassBridge.recoverSameSupportGroupWithDirectInferredBlockSizeFallback_eq_some_gf2Equiv_of_perm_supportCharges_supportSize`
  packages that hidden-source equivalence with success of the inferred
  support-size direct branch, still before bounded charge-list search.
  `AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_certifiedDirectInferred_gf2Equiv_of_perm_supportCharges_of_twoCharge_none_of_directCharge_none`
  lifts that result to the production fallback in the no-fast-branch case:
  when the two-charge path and older arity-three/four direct path both miss, the
  returned inferred decomposition carries coverage, empty residual, exact target
  classification, and hidden-source GF(2) equivalence.
  This pins the open problem to discovering the exact split from CNF; neither
  the residual-free block target nor the compact GF(2) target loses
  multiplicity data once that split is supplied or recovered.
- `TseitinCNFData.allAssignments_length`,
  `TseitinCNFData.allAssignments_countP_parity_eq_succ`,
  `TseitinCNFData.clausesForVertex_length_eq_countP_bad`,
  `TseitinCNFData.clausesForVertex_length_of_length_succ`,
  `TseitinCNFData.clausesForVertex_length_eq_pow_pred_of_vars_ne_empty`,
  `AtomicClassBridge.generatedParitySpecsForSupportCharges_cnf_length_eq_mul_of_block_length`,
  `AtomicClassBridge.target_length_eq_charge_count_mul_block_length_of_perm_generatedParitySpecsForSupportCharges`,
  `AtomicClassBridge.charges_length_eq_target_length_div_block_length_of_perm_generatedParitySpecsForSupportCharges`,
  `AtomicClassBridge.target_length_mod_block_length_eq_zero_of_perm_generatedParitySpecsForSupportCharges`,
  `AtomicClassBridge.generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_three`,
  `AtomicClassBridge.generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_four`,
  `AtomicClassBridge.target_length_eq_charge_count_mul_four_of_perm_generatedParitySpecsForSupportCharges`,
  and
  `AtomicClassBridge.target_length_eq_charge_count_mul_eight_of_perm_generatedParitySpecsForSupportCharges`:
  give exact generated-block and same-support generated-component length
  accounting.  The base `clausesForVertex` theorem derives the per-block length
  from any nonempty generated support; the component-level generic theorem
  handles any supplied positive block length `k`.  The main arity-three and
  arity-four lanes specialize it to component length `charge_count * 4` and
  `charge_count * 8`, with the same transport across clause permutation.  This
  lets component size determine the total generated charge count once the
  generated block size is known or derived.  The quotient/divisibility
  corollaries
  `AtomicClassBridge.charges_length_eq_target_length_div_block_length_of_perm_generatedParitySpecsForSupportCharges`,
  `AtomicClassBridge.target_length_mod_block_length_eq_zero_of_perm_generatedParitySpecsForSupportCharges`,
  `AtomicClassBridge.charges_length_eq_target_length_div_four_of_perm_generatedParitySpecsForSupportCharges`,
  `AtomicClassBridge.charges_length_eq_target_length_div_eight_of_perm_generatedParitySpecsForSupportCharges`,
  `AtomicClassBridge.target_length_mod_four_eq_zero_of_perm_generatedParitySpecsForSupportCharges`,
  and
  `AtomicClassBridge.target_length_mod_eight_eq_zero_of_perm_generatedParitySpecsForSupportCharges`
  turn that accounting into exact arity-specific charge-count formulas, and the
  `AtomicClassBridge.*_arityThreeExactBound` /
  `AtomicClassBridge.*_arityFourExactBound` recovery theorems use
  `target.length / 4` or `target.length / 8` as certified search bounds.  This
  still does not identify the charge values or per-charge multiplicities inside
  an arbitrary component.
- `AtomicClassBridge.canonicalSupportChargesFromCounts_perm`,
  `AtomicClassBridge.directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_of_block_length`,
  `AtomicClassBridge.directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_arityThree`,
  `AtomicClassBridge.directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_arityFour`,
  `AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_of_block_length`,
  `AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_directTargetCharges_of_block_length`,
  `AtomicClassBridge.recoverSameSupportGroupWithDirectBlockSizeFallback_sound`,
  `AtomicClassBridge.recoverSameSupportGroupWithDirectBlockSizeFallback_toSyntacticOk`,
  `AtomicClassBridge.recoverSameSupportGroupWithDirectBlockSizeFallback_eq_some_of_directTargetCharges_of_block_length`,
  `AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_arityThree`,
  `AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_arityFour`,
  `AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_directTargetCharges_arityThree`,
  and
  `AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_directTargetCharges_arityFour`,
  plus
  `AtomicClassBridge.recoverSameSupportGroupWithDirectInferredBlockSizeFallback_eq_some_of_directTargetCharges_supportSize`:
  build the canonical charge representative directly from
  `target.length / blockSize` and the all-false fingerprint count.  In the
  block-size-generic form, that representative is proved
  permutation-equivalent to the hidden charge list whenever callers supply or
  derive the positive per-block length proof; the inferred support-size branch
  derives that proof from the uniform generated block-size theorem for every
  nonempty generated support.  The existing charge-guided recovery then succeeds
  without `chargeListsUpTo` enumeration.  The block-size-parameterized fallback
  hook packages the same returned-output soundness, syntactic-upgrade, and
  success theorem at the production-shaped same-support interface for any
  certified positive block size.  This is still generated-component recovery,
  not arbitrary CNF or general 3-SAT recognition.
- `AtomicClassBridge.twoCycleSameSupportDirectRecovery_eq_some`,
  `AtomicClassBridge.twoCycleCanonicalSupportGroups_length`, and
  `AtomicClassBridge.twoCycleSameSupportMergedSupportRecovery_isSome`: certify
  that the guided recovery returns the fallback decomposition on the direct
  two-cycle CNF, that the actual canonical support grouping has one merged
  support group, and that guided recovery succeeds on that merged group.
- `AtomicClassBridge.recoverTwoChargeSameSupportGroup?`,
  `AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm?`,
  `AtomicClassBridge.sameSupportTwoChargeCandidateSpecs_eq_of_perm_generatedParitySpecs_two_sameSupport`,
  `AtomicClassBridge.groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_two_sameSupport`,
  `AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_eq_some_of_perm_generatedParitySpecs_two_sameSupport`,
  `AtomicClassBridge.recoverSingleMergedSupportGroupTwoCharge?`,
  `AtomicClassBridge.sameSupportTwoChargeCandidateSpecs_twoCycle_eq_generated`,
  `AtomicClassBridge.sameSupportTwoChargeCandidateSpecs_eq_generated_of_perm_twoCycle`,
  `AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_eq_some_of_perm_twoCycle`,
  `AtomicClassBridge.groupClausesByCanonicalSupport_eq_single_of_perm_twoCycle`,
  `AtomicClassBridge.inferCanonicalParityBlock_eq_none_of_perm_twoCycle`,
  `AtomicClassBridge.twoCycleSameSupportUnguidedDirectRecovery_eq_some`, and
  `AtomicClassBridge.twoCycleSameSupportUnguidedMergedSupportRecovery_isSome`:
  add the first unguided same-support recovery shape.  The recognizer infers the
  canonical support from the merged component, tries the two parity charges in
  both orders, proves any returned decomposition covers the component with empty
  residual, emits syntactically upgradable blocks, and succeeds on the actual
  `n = 2` one-group boundary.  The permutation-insensitive variant proves
  coverage up to `List.Perm` and succeeds for every nonempty clause permutation
  of the direct two-cycle component; the exact-list variant is kept as a
  diagnostic surface.  The returned local two-charge decomposition now also
  carries a `ParityEncoded.Class` witness and per-assignment semantic
  preservation for its compact GF(2) core.  The strengthened
  `AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_sound_coreGF2`
  theorem records not only coverage and zero residual clauses, but also that
  the emitted compact core is exactly one of the two generated two-charge
  candidate GF(2) targets.  The remaining gap is generalizing this local
  splitter beyond the two-charge same-support case.
- `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_perm_generatedParitySpecs_two_sameSupport`:
  extracts the two-cycle-independent core of that repair.  For any canonical
  support `vars`, any nonempty clause permutation of the generated true/false
  parity expansions over `vars`, and any ordinary one-block recognizer miss,
  the production enhanced fallback splitter emits the generated two-equation
  GF(2) target with no residual clauses.  This removes the graph-specific
  two-cycle dependency from the local theorem, while still leaving
  arbitrary same-support recovery open.
- `AtomicClassBridge.splitCanonicalSupportClauseGroupsWithTwoChargeFallback`,
  `AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback`,
  and `AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_*`:
  package local same-support recovery as a production-shaped fallback splitter.
  The same-support branch first tries the legacy two-charge recovery, then the
  direct arity-three/four count-derived branch, then an inferred support-size
  direct branch for nonempty generated supports.  For nonempty generated
  same-support components, the new non-exhaustive production theorem proves the
  bounded charge-search branch is unreachable; for arbitrary components, the
  exhaustive component-length search remains the final fallback.
  The production branch now also has an exact-core target audit:
  `ProductionSameSupportFallbackCoreGF2Target` enumerates the compact GF(2)
  targets that can be emitted, and
  `recoverSameSupportGroupWithChargeSearchFallback_sound_coreGF2` proves every
  successful production fallback lands in that target set while preserving
  coverage and empty residual.
  For nonempty generated same-support inputs,
  `recoverSameSupportGroupWithChargeSearchFallback_exists_coreTarget_gf2Equiv_of_perm_supportCharges_componentBound`
  additionally connects the returned compact core back to the hidden generated
  GF(2) source: the emitted core is assignment-equivalent to the source
  same-support charge system, while still carrying the exact production target
  witness.
  `recoverSameSupportGroupWithChargeSearchFallback_exists_certifiedCoreTarget_gf2Equiv_of_perm_supportCharges_componentBound`
  packages the same generated-source bridge with recovery success, coverage up
  to clause permutation, empty residual, and the exact production target witness
  in one returned certificate.
  The block-size-parameterized direct hook remains available for callers that
  want to certify a positive generated block size explicitly.
  On the direct two-cycle boundary it covers the CNF exactly, compacts
  to the direct two-equation GF(2) target, emits two compact equations, and
  leaves zero residual clauses.  The exact-list unguided recovery is proved to
  fail on the reversed direct two-cycle CNF, while the permutation-insensitive
  recovery and production enhanced splitter are proved to accept that reversed
  boundary with zero residual clauses and the same compact GF(2) target.
  Generically, the enhanced group-level and full-CNF splitters preserve every
  ordinary clause up to permutation: recognized one-block groups move into the
  core, successful same-support fallback groups move into the core as
  residual-free local decompositions, and all other groups remain residual.
  The local production fallback branch itself now carries a
  `ParityEncoded.Class` witness and per-assignment semantic preservation for
  every successful return.  A
  residual-free enhanced fallback split whose
  emitted blocks pass the executable syntactic check now yields a
  dedicated `EnhancedExtractorCompleteOn` / `EnhancedSemanticExtractorCompleteOn`
  package for its compact core.  The wrapper is intentionally scoped to the
  existing one-block recognizer plus the same-support fallback branch; it
  remains separate from the baseline `ExtractorCompleteOn` API and is not a
  completeness theorem for arbitrary same-support components or an efficiency
  claim.
- `AtomicClassBridge.splitCanonicalSupportClauseGroupsWithTwoChargeFallback_append_of_residual_free`:
  residual-free enhanced fallback support-group splits compose across appended
  support-group lists, so the fallback splitter now has the same group-list
  frame shape as the baseline splitter.
- `AtomicClassBridge.splitCanonicalSupportClauseGroupsWithTwoChargeFallback_of_groupsRecognized`
  and `AtomicClassBridge.enhancedExtractorCompleteOn_of_groupRecognition`:
  recognized canonical support groups are residual-free for the enhanced
  fallback splitter as well.  This records that the enhanced production-shaped
  splitter subsumes the baseline recognized-group lane before invoking any
  same-support fallback branch.
- `AtomicClassBridge.enhancedExtractorCompleteOn_append_of_groupAppend` and
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_of_groupAppend`:
  residual-free enhanced fallback witnesses compose for `F ++ G` when the
  grouping pass frames the append as the concatenation of the two fragment
  groupings.
- `AtomicClassBridge.enhancedExtractorCompleteOn_append_of_clauseKeysDisjoint`,
  `AtomicClassBridge.enhancedExtractorCompleteOn_append_of_disjointSupport`,
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_of_clauseKeysDisjoint`,
  and
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_of_disjointSupport`:
  caller-facing enhanced frame wrappers under canonical support-key
  disjointness, or ordinary support disjointness with the nonempty-right-CNF
  side condition.
- `AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_append_of_clauseKeysDisjoint`
  and
  `AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_append_of_disjointSupport`:
  exact enhanced-splitter frame theorems with the same side-condition packages:
  residual-free enhanced splits of `F` and `G` become the literal concatenated
  block output for `F ++ G`.
- `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append`
  and
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_perm`
  and
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_singleGroupRecognition_toSyntacticOk`:
  recognized support groups, and the singleton recognized-group atom case, now
  instantiate the combined semantic/enhanced-executable surface when their
  emitted blocks pass the executable syntactic upgrade.  The permutation-aware
  bridge targets any GF(2) formula matching the emitted compact equations up to
  `List.Perm`.
- `AtomicClassBridge.enhancedExtractorCompleteOn_of_disjoint_appendGroupRecognition`
  and
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk_append`:
  support-disjoint CNF fragments whose canonical support groups are already
  recognized are residual-free for the enhanced fallback splitter, and package
  as the combined semantic/enhanced-executable surface when emitted blocks pass
  the executable syntactic upgrade.
- `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_singleGroupTwoChargeFallback`:
  lifts the local two-charge fallback into the enhanced splitter API for any
  CNF that groups as one support component, fails the ordinary one-block
  recognizer, and succeeds under the two-charge same-support recovery.  This is
  the generic form of the direct two-cycle boundary repair, still conditional
  on fallback success.  The production splitter now also has the broader
  direct count-derived and same-support charge-search branches after this
  two-charge path; the theorem name is retained for the two-charge success
  condition it packages.
- `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle`:
  packages the direct two-cycle boundary as a combined
  `EnhancedSemanticExtractorCompleteOn` theorem.  The proof deliberately pairs
  declarative cycle semantics with the enhanced splitter's residual-free
  executable output, so it does not require a proof-carrying block-list
  provenance lemma for the semantic half.
- `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle_reversed`:
  packages the reversed direct two-cycle boundary with the same combined
  `EnhancedSemanticExtractorCompleteOn` target, closing the concrete
  clause-order regression for the enhanced production splitter.
- `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle_of_perm`:
  generalizes that production-path boundary repair to every nonempty clause
  permutation of the direct two-cycle CNF.  The theorem proves that the
  permuted CNF still forms one support group, the ordinary one-block recognizer
  still misses it, the permutation-insensitive fallback recovers the certified
  two-charge split, and the enhanced splitter emits the same compact GF(2)
  target with no residual clauses.
- `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula`:
  proves the combined semantic/enhanced-executable extraction theorem for
  every derived cycle with `1 < n`.  Nondegenerate cycles use the ordinary
  recognized-group lane inside the enhanced splitter; the two-vertex boundary
  uses the certified same-support fallback.
- `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_toSyntacticOk`
  and
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate_toSyntacticOk`:
  expose the same cycle-family surface through the direct
  recognizer-certificate route in the nondegenerate range, with the certified
  two-charge fallback still handling the two-cycle boundary.
- `AtomicClassBridge.GeneratedParitySpec` and
  `AtomicClassBridge.GeneratedSupportDisjointSpecList`: an ergonomic folded
  spec-list interface for finite generated parity families, carrying the same
  nonempty, normal-form, and accumulated support-disjoint side conditions.
- `AtomicClassBridge.generatedSupportDisjointFamily_of_specList`: converts the
  folded spec-list interface into the lower-level
  `GeneratedSupportDisjointFamily` theorem package.
- `AtomicClassBridge.extractorCompleteOn_of_generatedSupportDisjointSpecList`:
  proves residual-free executable extractor completeness directly for folded
  generated spec lists satisfying those snoc side conditions.
- `AtomicClassBridge.GeneratedKeyDisjointSpecList` and
  `AtomicClassBridge.extractorCompleteOn_of_generatedKeyDisjointSpecList`:
  provide the corresponding folded spec-list interface and residual-free
  executable extractor theorem under accumulated canonical support-key
  freshness.
- `AtomicClassBridge.GeneratedCanonicalKeyFreshSpecList` and
  `AtomicClassBridge.generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList`:
  reduce the clause-level key-disjoint generated-spec condition to a
  spec-level freshness certificate: each newly generated parity spec must have
  a canonical incident-support key distinct from all earlier generated specs.
- `AtomicClassBridge.generatedCanonicalKeyFreshSpecList_snoc_of_exists` and
  `AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromIncident_append_singleton`:
  package the proof-building step for generated incident specs, so graph-family
  induction can extend the freshness certificate from per-vertex freshness,
  nonempty-block, and normal-order witnesses.
- `AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromIncident_range_prefix`,
  `AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh`,
  `AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh_degree_pos`,
  and
  `AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh`:
  lift that induction to any concrete graph encoding whose generated vertex
  blocks are nonempty and whose canonical incident-support keys are fresh in
  vertex-range order.
- `AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos`:
  strengthens the graph-encoding reduction by replacing the explicit
  nonempty-block witness premise with the checkable condition that every vertex
  in the encoding has positive degree.
- `AtomicClassBridge.class_of_tseitinCNFFormulaFromEncoding`: proves every
  concrete Tseitin graph encoding is in the declarative parity-encoded class,
  without any key-freshness or positive-degree premise.  This is semantic class
  membership only, not residual-free extractor completeness.
- `AtomicClassBridge.class_of_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList`
  and
  `AtomicClassBridge.class_of_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos`:
  retain the side-conditioned declarative `ParityEncoded.Class` wrappers that
  align with the executable extractor lanes.
- `TseitinModel.encoding_circulant12_derived`,
  `TseitinModel.circulant12_degree_eq_eight`, and
  `TseitinModel.circulant12_degree_pos`: package the jump-one/jump-two
  circulant graph as a concrete `GraphEncodingData` family for every `2 < n`,
  with every vertex incident to eight directed edge variables.
- `AtomicClassBridge.circulant12CanonicalIncidentSupportKeys_ne_of_ne` and
  `AtomicClassBridge.circulant12IncidentSupportKeys_fresh`: prove the
  family-specific fresh incident-key condition for every `2 < n`, using the
  forward-one edge slot `4*u` and the forward-two edge slot `4*u + 2` as
  separating witnesses.
- `AtomicClassBridge.extractorCompleteOn_TseitinCirculant12CNFFormula`: proves
  residual-free executable extractor completeness for the formal
  `circulant12` encoding for every `2 < n` and every charge function.
- `AtomicClassBridge.class_of_TseitinCirculant12CNFFormula`: proves the same
  formal `circulant12` encoding is in the declarative parity-encoded class for
  every `2 < n` and every charge function.
- `AtomicClassBridge.semanticExtractorCompleteOn_TseitinCirculant12CNFFormula`:
  combines those two `circulant12` lanes into one audited semantic plus
  residual-free executable extraction theorem.
- `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCirculant12CNFFormula_toSyntacticOk`:
  exposes the same `circulant12` graph-family surface through the direct
  recognizer-certificate route, with the family fresh-key proof and
  positive-degree theorem discharging the generic graph side conditions.
- `AtomicClassBridge.generatedCanonicalKeyFreshSpecList_forCycle_prefix` and
  `AtomicClassBridge.generatedCanonicalKeyFreshSpecList_forCycle`: package the
  nondegenerate derived cycle family into the spec-level canonical-key freshness
  certificate for every `n` with `2 < n`.
- `AtomicClassBridge.extractorCompleteOn_of_generatedCanonicalKeyFreshSpecList`:
  proves residual-free executable extractor completeness directly from that
  spec-level canonical-key freshness certificate.
- `AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList`:
  proves that any concrete graph encoding whose generated incident specs satisfy
  accumulated key-disjointness is residual-free for the executable canonical
  splitter, with output matching `TseitinParityFormulaFromEncoding`.
- `AtomicClassBridge.extractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList`:
  specializes that reduction to `TseitinCycleCNFFormula n hn` under the
  lower-level key-disjoint generated-spec certificate.
- `AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList`:
  gives the same graph-encoding extractor reduction from the spec-level
  canonical-key freshness certificate.
- `AtomicClassBridge.extractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList`:
  specializes that reduction to `TseitinCycleCNFFormula n hn` under the cleaner
  cycle family `GeneratedCanonicalKeyFreshSpecList` certificate.
- `AtomicClassBridge.extractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate`:
  proves residual-free executable extractor completeness for every derived
  cycle with `2 < n`.
- `AtomicClassBridge.class_of_TseitinCycleCNFFormula`: proves every derived
  cycle with `1 < n`, including the certified two-vertex boundary, is in the
  declarative parity-encoded class.
- `AtomicClassBridge.class_of_TseitinCycleCNFFormula_nonDegenerate`: proves
  the same class statement through the nondegenerate fresh-key certificate.
- `AtomicClassBridge.semanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate`:
  combines those nondegenerate-cycle lanes into one audited semantic plus
  residual-free executable extraction theorem.
- `AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlocks_permCertified`:
  a list-level bridge showing append-disjoint canonical blocks with per-block
  permutation certificates form a `ParityEncoded.Class` over the extractor's
  concatenated CNF and GF(2) outputs.
- `AtomicClassBridge.CanonicalBlocksAppendDisjoint.append` and
  `AtomicClassBridge.CanonicalBlocksPermCertified.append`: certificate
  composition lemmas for appended canonical block lists.
- `AtomicClassBridge.CanonicalBlocksAppendDisjoint.singleton` and
  `AtomicClassBridge.CanonicalBlocksToSyntacticOk.singleton`: singleton
  certificate lemmas for the atom case of the executable canonical splitter.
- `AtomicClassBridge.CanonicalBlocksAppendDisjoint.append_of_disjointCovered`:
  derives append-disjointness composition from ordinary support disjointness
  between the two covered CNFs.
- `AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals`:
  derives the list-level class bridge from accepted syntactic permutation
  signals plus append-disjointness.
- `AtomicClassBridge.CanonicalBlocksSyntacticSignals.of_toSyntacticOk`: turns
  successful executable `toSyntactic?` checks over canonical blocks into the
  syntactic-signal certificate expected by the class bridge.
- `AtomicClassBridge.groupsRecognizedWithSyntacticOk_exists_of_generatedKeyDisjointFamily`,
  `AtomicClassBridge.groupsRecognizedWithSyntacticOk_exists_of_generatedKeyDisjointSpecList`,
  and
  `AtomicClassBridge.groupsRecognizedWithSyntacticOk_exists_of_generatedCanonicalKeyFreshSpecList`:
  finite generated families with fresh canonical support keys now return a
  single witness package containing recognized support groups, successful
  executable syntactic upgrades for every emitted canonical block, and compact
  GF(2) output matching the generated target up to permutation.
- `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointFamily_toSyntacticOk`,
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointSpecList_toSyntacticOk`,
  and
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk`:
  the generated-family witness package now feeds directly into the enhanced
  semantic/executable completeness surface through recognized support groups
  and executable syntactic upgrades, rather than routing only through the older
  generator-side class theorem.
- `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList_toSyntacticOk`,
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk`,
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_toSyntacticOk`,
  and
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos_toSyntacticOk`:
  concrete graph encodings inherit the same recognizer-certificate route under
  generated key-disjointness, canonical-key freshness, explicit nonempty block
  witnesses, or positive-degree witnesses.
- `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh_toSyntacticOk`
  and
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCirculant12CNFFormula_toSyntacticOk`:
  the non-cycle `circulant12` family now instantiates that direct
  recognizer-certificate route unconditionally for every `2 < n` and every
  charge function.
- `AtomicClassBridge.canonicalFingerprintRecognizedBlocksCNF_perm_of_groupsRecognized`:
  recognized support groups emit canonical blocks whose covered CNF is a
  permutation of the original source CNF.
- `AtomicClassBridge.disjointSupport_of_perm`: support-disjointness transports
  across clause-list permutations, allowing covered-block CNFs to inherit
  original source disjointness.
- `AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals`:
  a residual-free executable split yields a `ParityEncoded.Class` witness for
  the original CNF when the emitted blocks carry syntactic recognition signals
  and append-disjointness.
- `AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk`:
  the same split-to-class bridge with the syntactic-signal premise discharged
  by successful executable `toSyntactic?` checks on the emitted blocks.
- `AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals_append`
  and
  `AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append`:
  residual-free executable splitter output instantiates `ParityEncoded.Class`
  through semantic append/gluing without requiring emitted blocks to be
  support-disjoint.
- `AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append`:
  syntactically accepted canonical blocks instantiate `ParityEncoded.Class`
  through semantic append/gluing without a support-disjointness premise.
- `AtomicClassBridge.class_of_groupRecognition_syntacticSignals` and
  `AtomicClassBridge.class_of_groupRecognition_toSyntacticOk`: recognized
  canonical support groups instantiate `ParityEncoded.Class` directly once the
  emitted blocks carry syntactic recognition signals, or pass executable
  `toSyntactic?` checks, and are append-disjoint.
- `AtomicClassBridge.class_of_groupRecognition_toSyntacticOk_append`: the
  relaxed group-recognition class bridge using semantic append/gluing, so
  overlapping recognized parity blocks do not require a false disjointness
  certificate.
- `AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals`
  and
  `AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk`:
  lift residual-free executable splitter output directly to the combined
  `SemanticExtractorCompleteOn` surface when emitted blocks carry syntactic
  signals, or pass executable `toSyntactic?` checks, and are append-disjoint.
- `AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals_append`
  and
  `AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append`:
  lift residual-free executable splitter output to the combined
  `SemanticExtractorCompleteOn` surface through semantic append/gluing, with no
  block support-disjointness premise.
- `AtomicClassBridge.semanticExtractorCompleteOn_of_groupRecognition_syntacticSignals`
  and
  `AtomicClassBridge.semanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk`:
  lift recognized canonical support groups directly to the same combined
  surface, discharging the empty-residual split through the group-recognition
  theorem.
- `AtomicClassBridge.semanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append`:
  the relaxed combined group-recognition bridge, requiring recognized groups
  and successful `toSyntactic?` checks but no block support-disjointness.
- `AtomicClassBridge.CertifiedRecognizedCNF` plus
  `AtomicClassBridge.class_of_certifiedRecognizedCNF`,
  `AtomicClassBridge.semanticExtractorCompleteOn_of_certifiedRecognizedCNF`,
  `AtomicClassBridge.extractorCompleteOn_of_certifiedRecognizedCNF_perm`,
  `AtomicClassBridge.semanticExtractorCompleteOn_of_certifiedRecognizedCNF_perm`,
  and
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_certifiedRecognizedCNF`:
  a proof-carrying certificate interface for arbitrary CNFs whose executable
  support groups are already recognized, whose emitted blocks pass
  `toSyntactic?`, and whose emitted GF(2) equations match the caller's target
  up to permutation.  The baseline extractor and combined semantic/executable
  surfaces now remain valid after arbitrary whole-CNF clause permutation of the
  certified source CNF.
- `AtomicClassBridge.ClausePermutedRecognizedBlock` plus
  `AtomicClassBridge.clausePermutedRecognizedBlock_of_singleRecognizedGroup_toSyntacticOk`,
  `AtomicClassBridge.class_of_clausePermutedRecognizedBlock`,
  `AtomicClassBridge.extractorCompleteOn_of_clausePermutedRecognizedBlock`,
  `AtomicClassBridge.semanticExtractorCompleteOn_of_clausePermutedRecognizedBlock`,
  `AtomicClassBridge.enhancedExtractorCompleteOn_of_clausePermutedRecognizedBlock`,
  and
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedBlock`:
  a smaller single-block certificate for a clause-permuted recognized parity
  component.  Literal-level permutation evidence discharges the executable
  syntactic upgrade and derives the general `CertifiedRecognizedCNF` interface;
  successful `toSyntactic?` checks now recover that permutation certificate from
  singleton executable-recognition facts.
- `GroupFrame.groupClausesByCanonicalSupport_eq_single_of_perm_clausesForVertex`
  plus
  `AtomicClassBridge.clausePermutedRecognizedBlock_of_perm_clausesForVertex_toSyntacticOk`
  and its class, baseline semantic/executable, enhanced extractor, and enhanced
  semantic/executable wrappers: arbitrary nonempty clause permutations of a
  generated parity expansion now supply the singleton support-grouping fact
  automatically.  The executable recognizer result and successful
  `toSyntactic?` check remain explicit premises for this lower-level wrapper;
  the stronger generated-atom wrappers below discharge those recognizer
  obligations through canonical fingerprint invariance.
- `canonicalClauseFingerprint_eq_of_perm`,
  `canonicalBlockFingerprint_eq_of_perm`, and
  `canonicalParityBlockRecognitionSignal_of_perm`: the canonical fingerprint
  sorter is now proved permutation-invariant for full signed-literal clause
  content.  This closes the previous low-level canonicalization gate without
  specializing to generated examples.
- `sortFinByVal_eq_of_perm`,
  `canonicalClauseSupportVars_eq_of_perm`, and
  `canonicalClauseSupportKey_eq_of_perm`: the support-key canonicalizer is also
  invariant under literal permutation.  This separates the known support-key
  grouping collisions from the full-content fingerprint canonical form.
- `GroupFrame.parityCandidateCanonicalSupportFromBlock_eq_of_perm_clausesForVertex_normal`,
  `AtomicClassBridge.parityBlockRecognitionSignal_of_perm_clausesForVertex`,
  `AtomicClassBridge.inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal_of_signal`,
  `AtomicClassBridge.inferCanonicalParityBlock_false_of_perm_clausesForVertex_normal_of_signal`,
  and
  `AtomicClassBridge.inferCanonicalParityBlock_true_of_perm_clausesForVertex_normal_of_signal_of_falseMiss`:
  arbitrary nonempty clause permutations of generated parity expansions in
  canonical support order now recover the generated support, pass the syntactic
  permutation signal, and derive the one-charge/public executable recognizer
  result once the canonical fingerprint signal is supplied.  Because the public
  recognizer tries false before true, the true-charge wrapper also carries the
  explicit false-first miss.
- `AtomicClassBridge.clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal_of_signal`
  and its class, baseline semantic/executable, and enhanced semantic/executable
  wrappers, plus the corresponding
  `_true_normal_of_signal_of_falseMiss` wrappers: the single-block
  clause-permuted generated-atom certificate no longer needs an explicit
  recognizer result or `toSyntactic?` premise in these older theorem shapes.
  Their explicit proof obligation is exactly the canonical fingerprint signal,
  not semantic parity reasoning or support grouping.
- `AtomicClassBridge.inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal`,
  `AtomicClassBridge.inferCanonicalParityBlock_false_of_perm_clausesForVertex_normal`,
  `AtomicClassBridge.inferCanonicalParityBlock_true_of_perm_clausesForVertex_normal`,
  and the no-signal/no-false-miss class, baseline, and enhanced wrappers for
  false- and true-charge permuted generated atoms: the canonical fingerprint
  signal and the public recognizer's false-first miss are now discharged
  internally for generated atoms in canonical support order.  The remaining
  v0.2 frontier is arbitrary declarative-class completeness and stronger
  overlap/general graph recovery, not local canonical fingerprint invariance.
- `AtomicClassBridge.ClausePermutedRecognizedClass` plus
  `AtomicClassBridge.clausePermutedRecognizedClass_of_cnf_perm`,
  `AtomicClassBridge.class_of_clausePermutedRecognizedClass`,
  `AtomicClassBridge.groupsRecognized_exists_of_clausePermutedRecognizedClass`,
  `AtomicClassBridge.extractorCompleteOn_of_clausePermutedRecognizedClass`,
  `AtomicClassBridge.semanticExtractorCompleteOn_of_clausePermutedRecognizedClass`,
  `AtomicClassBridge.extractorCompleteOn_of_clausePermutedRecognizedClass_perm`,
  `AtomicClassBridge.semanticExtractorCompleteOn_of_clausePermutedRecognizedClass_perm`,
  `AtomicClassBridge.enhancedExtractorCompleteOn_of_clausePermutedRecognizedClass`,
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedClass`,
  `AtomicClassBridge.enhancedExtractorCompleteOn_of_clausePermutedRecognizedClass_perm`,
  and
  `AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedClass_perm`:
  an induction-shaped recognizer-complete fragment for arbitrary
  clause-permuted recognized blocks joined by canonical support-key-disjoint
  appends, with both whole-CNF clause permutation closure and GF(2)-target
  permutation closure.  The class also carries recognized executable
  support-group witnesses, and both its baseline and enhanced
  semantic/executable extractor surfaces transport through arbitrary whole-CNF
  clause permutation.
- `AtomicClassBridge.clausePermutedRecognizedClass_of_perm_clausesForVertex_normal`:
  arbitrary nonempty clause permutations of generated parity atoms in canonical
  support order now enter that recognizer-complete class directly, with the
  expected compact GF(2) equation.  The whole-CNF interleaving gate now has
  support-key, per-key grouped-content, key-matched component, residual-free
  splitter, compact GF(2) output, and caller-facing `ExtractorCompleteOn` /
  `SemanticExtractorCompleteOn` preservation theorems for recognized source
  groups.
- `AtomicClassBridge.clausePermutedRecognizedBlock_exists_clausesForVertex_normal`
  plus the class, baseline semantic/executable, and enhanced
  semantic/executable `_via_clausePermutedRecognizedBlock` corollaries: generated
  parity atoms in canonical support order now instantiate the same smaller
  certificate boundary.
- `AtomicClassBridge.clausePermutedRecognizedClass_of_generatedKeyDisjointFamily`
  and its key-disjoint/fresh-key generated spec-list wrappers: the existing
  generated-family lane now factors through the more general
  clause-permuted-recognized class.
- `AtomicClassBridge.semanticExtractorCompleteOn_of_singleGroupRecognition_toSyntacticOk`:
  packages the atom case as a combined semantic/executable theorem for one
  recognized canonical support group.
- `AtomicClassBridge.class_of_singleGroupRecognition_toSyntacticOk`: a
  single-support-group bridge turning one recognized canonical support group
  with a successful `toSyntactic?` check into a `ParityEncoded.Class` atom.
- `AtomicClassBridge.class_of_disjoint_appendGroupRecognition_toSyntacticOk`:
  a support-disjoint append fragment: if both sides group into recognized
  canonical blocks, the right side has no empty-support clauses, emitted blocks
  pass `toSyntactic?`, and each side is internally append-disjoint, then
  `F ++ G` instantiates `ParityEncoded.Class`.
- `AtomicClassBridge.class_of_disjoint_appendGroupRecognition_toSyntacticOk_append`:
  the relaxed support-disjoint append fragment for class membership.  It keeps
  the source-level grouping frame premises but uses semantic append/gluing for
  the emitted blocks, so the emitted block lists do not need internal
  append-disjointness.
- `AtomicClassBridge.semanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk`:
  the same support-disjoint append fragment lifted to the combined
  semantic/executable extractor-completeness surface.
- `AtomicClassBridge.semanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk_append`:
  the same relaxed support-disjoint append fragment lifted to the combined
  `SemanticExtractorCompleteOn` surface, again without internal emitted-block
  append-disjointness.

Supporting documentation:

- `docs/CLAIM_BOUNDARY.md`
- `docs/AXIOM_AUDIT.md`
- `docs/FRAME_PROPERTY_PROBE.md`
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
canonical fingerprint extractor now has support-grouping frame theorems through
ordinary variable-disjoint support with an explicit nonempty-support side
condition and through the weaker canonical clause-support-key freshness
condition, clause-cover theorems for grouping and splitting, and a conditional
bridge from residual-free executable splits to `ParityEncoded.Class` when the
emitted canonical blocks pass `toSyntactic?` and append-disjointness checks.
That same certified-split lane now packages directly as
`SemanticExtractorCompleteOn` for the splitter's own emitted GF(2) formula,
so a residual-free split plus syntactic block certificates is enough to obtain
both per-assignment equivalence and executable residual-free completeness.
Recognized canonical support groups now have the same combined package without
first materializing the split theorem by hand, including a singleton atom-case
wrapper for one recognized support component.  The named
`CertifiedRecognizedCNF` certificate interface packages that same boundary for
arbitrary CNFs with supplied grouping, recognition, syntactic-upgrade, and
GF(2)-target permutation evidence.  That certificate now transports through
arbitrary whole-CNF clause permutation for the baseline `ExtractorCompleteOn`
and `SemanticExtractorCompleteOn` surfaces.  The
`ClausePermutedRecognizedBlock` interface narrows the single-block case further:
a grouping fact, executable recognizer result, and literal-level clause
permutation proof now derive the recognized-CNF certificate and both combined
extractor surfaces.  The singleton constructor
`clausePermutedRecognizedBlock_of_singleRecognizedGroup_toSyntacticOk` reduces
that proof burden again by deriving the permutation proof from the executable
`toSyntactic?` check.  Generated parity atoms in canonical support order now
route through this interface directly, yielding class membership and both
baseline and enhanced combined extractor surfaces via the
`_via_clausePermutedRecognizedBlock` corollaries.  More generally, any nonempty
clause permutation of a generated parity expansion now gets the singleton
support-grouping obligation discharged by
`groupClausesByCanonicalSupport_eq_single_of_perm_clausesForVertex`; the
support-candidate inference and syntactic permutation signal are also derived
for canonical-order generated atoms.  The custom sorted fingerprint is now
proved permutation-invariant for full signed-literal clause content, so the
public recognizer and the single-block certificate/extractor wrappers follow
for false- and true-charge permuted generated atoms without caller-supplied
canonical signal or false-miss premises.  This moves the remaining obligation
up to class/function-level extractor completeness and frame reasoning, not
local canonicalization.
The `ClausePermutedRecognizedClass` theorem package is the first
induction-shaped recognizer-complete fragment beyond generated spec lists: it
composes arbitrary clause-permuted recognized blocks across canonical
support-key-disjoint appends and is closed under both arbitrary whole-CNF
clause permutation and GF(2)-target permutation, yielding
`ParityEncoded.Class`, baseline `SemanticExtractorCompleteOn`, and enhanced
`EnhancedSemanticExtractorCompleteOn`.  Generated key-disjoint families and
their fresh-key spec-list wrappers now factor through this class.
The baseline and enhanced permutation wrappers expose those extractor surfaces
across arbitrary interleavings of a class instance.
Residual-free extractor completeness itself now has a function-level append
composition theorem: already-complete fragments can be reused when the grouping
pass frames the append, with caller-facing wrappers for clause-key disjointness
and ordinary support disjointness. The same frame conditions now compose the
combined `SemanticExtractorCompleteOn` package, so the semantic and executable
lanes can be carried together once each fragment is already certified.  The
baseline and enhanced splitters now also have exact-output frame theorems:
under the same side conditions, the emitted block list for `F ++ G` is exactly
the left emitted block list followed by the right emitted block list.
The declarative class itself now has an overlapping append/gluing constructor.
Generated spec lists and every concrete graph encoding now instantiate that
class unconditionally on the semantic lane; derived cycles therefore have class
membership for all `1 < n`, including the certified two-vertex boundary. The
executable extractor lane remains stricter: it has residual-free completeness
for finite generated normal-form parity families under either support
disjointness or canonical support-key disjointness, including folded
generated-spec-list interfaces.
`SemanticExtractorCompleteOn` now packages these two lanes for side-conditioned
generated families, concrete graph encodings, nondegenerate cycles, and
`circulant12`; it deliberately does not assert extractor completeness for
arbitrary `ParityEncoded.Class` witnesses.
Folded generated specs are now proved equal to the existing incident-list and
graph-encoding Tseitin CNF/GF(2) encoders.  Concrete graph encodings now have
unconditional declarative class membership, and a residual-free extractor
theorem when canonical incident-support keys are fresh in vertex-range order
and either every generated vertex block is explicitly nonempty or, more
checkably, every vertex has positive degree.  The cycle-family executable
extractor theorem is discharged for the nondegenerate derived cycle range
`2 < n`; the `n = 2` boundary is covered semantically and now has guided plus
narrow unguided two-charge same-support executable recovery.  A
specification-side fallback target is certified for that boundary
at the decomposition interface: two canonical recognized blocks cover the
direct two-cycle CNF, compact to the direct two-equation GF(2) target, emit two
equations, leave zero residual clauses, and cover sixteen expanded clauses,
while the baseline canonical splitter is certified to miss them.  The guided
recovery validates exact CNF coverage for a supplied generated-spec split,
returns the fallback decomposition on the direct CNF, and succeeds on the
actual one-group canonical support component.  The unguided two-charge probe
infers the component support, tries both charge orders, proves residual-free
component coverage for any success, and succeeds on the same one-group
two-cycle component.  Its permutation-insensitive variant succeeds for every
nonempty clause permutation of that direct component, with the reversed
component as the concrete regression theorem.  A production-shaped fallback
splitter now wires that permutation-insensitive local probe after the existing
one-block recognizer, followed by direct arity-three/four count-derived
recovery, inferred support-size direct recovery, and then bounded exhaustive
search outside the generated lane.  On the direct two-cycle boundary it covers
the CNF exactly, compacts to the direct two-equation GF(2) target, emits two
equations, and leaves no residual clauses.  It also closes the reversed direct two-cycle
boundary with the same compact target and a combined
`EnhancedSemanticExtractorCompleteOn` theorem; this is now subsumed by a
production-path theorem for every nonempty clause permutation of that direct
two-cycle CNF.  Residual-free
enhanced fallback witnesses now compose under the same grouping-frame,
clause-key-disjoint, and ordinary support-disjoint side-condition packages as
the baseline splitter, so the fallback API is no longer only a single-instance
boundary repair.  The `circulant12`
family is
now packaged as a concrete graph encoding with its fresh incident-key obligation
discharged and the direct recognizer-certificate enhanced surface instantiated.
Standard cycle/Tseitin vertex blocks have proved normal incident-list order but
share edge variables, so semantic class membership uses overlapping gluing
while the key-disjoint lane remains the executable extractor path toward graph
encoders. The cycle edge-index lookup and endpoint-only
support-key lemmas are now proved for the derived directed cycle family, and
those facts are packaged into distinct canonical incident-support keys and the
spec-level freshness certificate for every `2 < n`.  The `n = 2` derived cycle
is also known not to satisfy the current key-fresh snoc premise, but the
enhanced splitter now closes that boundary with the certified same-support
fallback, yielding a uniform `EnhancedSemanticExtractorCompleteOn` theorem for
all derived cycles with `1 < n`. The support-key, per-key content, key-matched
component, residual-free splitter, compact GF(2) output, and caller-facing
`ExtractorCompleteOn` / `SemanticExtractorCompleteOn` layers of arbitrary
whole-CNF interleaving are now audited for recognized source groups; executable
support groups now provide the support-stability condition needed by the current
first-clause recognizer; and recognizer hits now transport across clause
permutations of actual grouped components. The `ClausePermutedRecognizedClass`
surface now has constructor-level whole-CNF clause permutation closure, carries
the corresponding executable support-group witness, and transports its baseline
and enhanced extractor-completeness claims through arbitrary whole-CNF clause
permutation.
The remaining obligations are to prove arbitrary
declarative-class completeness, a bounded-overlap/function-level frame theorem,
or a generalized executable same-support recovery theorem before advertising a
uniform residual-free extractor over arbitrary graph encodings,
and to test the fresh-key lane on graph families beyond cycles and
`circulant12`.

## AI Assistance Disclosure

Development used AI coding assistance.  Human authors are responsible for the
claims, release decisions, and final artifact review.
