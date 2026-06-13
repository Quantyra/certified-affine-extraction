# Frame Property Probe

This note records the v0.2.0 pre-proof probe for the canonical fingerprint
splitter.

## Purpose

The semantic compositionality fact is intentionally not the gate here. If a CNF
fragment `F` is equivalent per assignment to a GF(2) system `S`, then the same
statement composes over `F ++ G` by conjunction rewriting. That is useful as a
small lemma, but it is not where the extractor can fail.

The relevant pre-proof question is function-level stability:

```lean
extract (F ++ G)
```

should not change the recognized blocks that live entirely on `support F` when
`F` and `G` have disjoint support, except for output ordering.

## Executable Probe

The probe lives in `CertifiedAffine.FrameProbe` and checks deterministic
disjoint-support cases for the current canonical splitter:

```lean
theorem generatedSuitePass_eq_true : generatedSuitePass = true := by
  native_decide
```

The suite currently generates 32 cases with:

- left blocks on offsets `0` and `8`;
- frame blocks on offsets `4` and `12`;
- varying parity charges;
- literal-reordering and clause-ordering variants.

The comparison ignores block order but compares block content using the charge,
sorted variables, and canonical block fingerprint.

## Result

The generated suite passes. No empirical kill criterion fired: on these
disjoint-support cases, framing did not change the recognized left-side block
content up to permutation.

The global-permutation suite also passes. It checks 128 deterministic
multi-block generated cases, comparing extracted block content before and after
whole-CNF clause/literal permutation:

```lean
theorem globalPermutationSuitePass_eq_true :
    globalPermutationSuitePass = true := by
  native_decide
```

This supports the next proof target: a whole-CNF permutation/frame theorem for
the recognizer-complete class. It is still probe evidence, not an audited
`Audit.lean` claim.

The separate collision-heavy canonicalization precondition also passed before
the proof work: permuting literal-order variants, same-support/different-sign
clauses, and arity-four generated parity blocks did not change their canonical
fingerprints:

```lean
theorem supportCollisionCanonicalizationSuitePass_eq_true :
    supportCollisionCanonicalizationSuitePass = true := by
  native_decide
```

That empirical check is now backed by the audited generic theorems
`canonicalClauseFingerprint_eq_of_perm`, `canonicalBlockFingerprint_eq_of_perm`,
and `canonicalParityBlockRecognitionSignal_of_perm`.  The related audited
support-key theorems `canonicalClauseSupportVars_eq_of_perm` and
`canonicalClauseSupportKey_eq_of_perm` show that literal order does not affect
support-key assignment, even though support-key collisions are expected inside
one parity block.

## Non-Claims

This is not an audited theorem and is not part of `Audit.lean`. It is an
executable regression probe that informs whether the current extractor is worth
formalizing further.

The fixed-ambient `ParityEncoded.Class` and its semantic soundness theorem now
exist, and the class has an overlapping append/gluing constructor for generated
Tseitin-style parity blocks.  The side-conditioned generated-family and graph
lanes now also have `SemanticExtractorCompleteOn` wrappers that package the
semantic and residual-free extractor facts together.  The remaining proof gate
is still function-level, but one layer is now formal: residual-free
`ExtractorCompleteOn` witnesses compose whenever the grouping pass frames
`F ++ G` as the append of the two fragment groupings, with wrappers for
clause-key disjointness and ordinary support disjointness.  The clause-key frame
now also has audited `_perm` wrappers for independently clause-permuted
fragments, so per-fragment clause order is no longer part of the exact append
frame's trusted boundary; the recognizer-complete class exposes the same
subcase through `clausePermutedRecognizedClass_append_keyDisjoint_perm`.
Clause-key disjointness is now symmetric, and the baseline
`ExtractorCompleteOn`, `SemanticExtractorCompleteOn`, and
`ClausePermutedRecognizedClass` surfaces also have swapped-append wrappers that
emit the CNF as `G ++ F` while transporting the GF(2) target back to `S ++ T`.
The arbitrary whole-CNF interleaving lane now has its first audited key-set
theorem: `GroupFrame.groupKeys_groupClausesByCanonicalSupport_perm_of_perm`
proves that permuting the entire CNF preserves the grouped canonical support-key
list up to `List.Perm`, with supporting membership and no-duplicate lemmas.  It
also has an audited per-key content theorem:
`GroupFrame.groupClausesForKey_groupClausesByCanonicalSupport_perm_of_perm`
proves that permuting the entire CNF preserves each key's grouped clause
content up to `List.Perm`.  Those key/content layers now combine into
`GroupFrame.supportGroupsKeyMatchedCNFPerm_groupClausesByCanonicalSupport_of_perm`:
arbitrary whole-CNF permutation gives every source support group a target group
with the same canonical support key and permuted clause content.  The recognizer
layer now has an audited side-conditioned transport theorem: public recognizer
hits transport across permutations of nonempty support-homogeneous blocks.  The
executable grouper now supplies that side condition for its own nonempty
components, and public recognizer hits transport across clause permutations of
actual grouped components.  The splitter-output lift is now audited for explicit
aligned component lists: `GroupFrame.groupsRecognized_transport_of_alignedGroupCNFPerm`
and
`GroupFrame.splitCanonicalSupportClauseGroups_transport_of_alignedGroupCNFPerm`
transport residual-free recognized-group evidence through the canonical splitter
and preserve compact GF(2) output exactly.  The pure group-order case is also
audited: `GroupFrame.groupsRecognized_transport_of_group_perm` and
`GroupFrame.splitCanonicalSupportClauseGroups_transport_of_group_perm` transport
recognized groups across support-group list permutations with compact GF(2)
output preserved up to `List.Perm`.  The key-matched lift is now audited as
well:
`GroupFrame.groupsRecognized_transport_of_keyMatchedCNFPerm`,
`GroupFrame.splitCanonicalSupportClauseGroups_residualFree_of_keyMatchedCNFPerm`,
and `GroupFrame.splitArityFourParityCanonicalSupportGroups_residualFree_of_perm`
prove that arbitrary whole-CNF permutation preserves residual-freeness whenever
the source support groups were fully recognized.
`GroupFrame.exists_alignedSupportGroupCNFPermNonempty_of_keyMatched` then
bridges unordered key-matched components into source-key aligned component
lists, and
`GroupFrame.splitArityFourParityCanonicalSupportGroups_gf2_perm_of_perm` proves
the corresponding full-splitter compact GF(2) output preservation up to
`List.Perm`.  This now lifts to the caller-facing `ExtractorCompleteOn` and
`SemanticExtractorCompleteOn` surfaces through
`GroupFrame.extractorCompleteOn_groupClausesByCanonicalSupport_of_perm` and
`GroupFrame.semanticExtractorCompleteOn_groupClausesByCanonicalSupport_of_perm`.
The same whole-CNF permutation result is exposed through the proof-carrying
`CertifiedRecognizedCNF` certificate interface by
`AtomicClassBridge.extractorCompleteOn_of_certifiedRecognizedCNF_perm` and
`AtomicClassBridge.semanticExtractorCompleteOn_of_certifiedRecognizedCNF_perm`.
It is also exposed through the induction-shaped
`ClausePermutedRecognizedClass` surface by
`AtomicClassBridge.clausePermutedRecognizedClass_of_cnf_perm`,
`AtomicClassBridge.groupsRecognized_exists_of_clausePermutedRecognizedClass`,
`AtomicClassBridge.extractorCompleteOn_of_clausePermutedRecognizedClass_perm`,
and
`AtomicClassBridge.semanticExtractorCompleteOn_of_clausePermutedRecognizedClass_perm`,
with matching enhanced two-charge fallback wrappers.
The enhanced two-charge fallback itself now uses permutation-insensitive
same-support recovery: the exact-list recovery is certified to fail on the
reversed direct two-cycle CNF, while the permutation-insensitive recovery is
certified to accept every nonempty clause permutation of the direct two-cycle
component.  The same local repair is now factored as the generic
`enhancedSemanticExtractorCompleteOn_of_perm_generatedParitySpecs_two_sameSupport`
theorem for any generated true/false pair over one canonical support, assuming
the ordinary one-block recognizer misses.  The production enhanced splitter is
certified residual-free on the
reversed boundary and preserves the input up to `List.Perm`; the stronger
`enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle_of_perm`
theorem lifts that production result to every nonempty clause permutation of
the direct two-cycle CNF with the same compact GF(2) target.
The guided same-support lane now has a broader support-grouping fact:
`groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_sameSupport`
and
`recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_eq_some_of_perm_generatedParitySpecs_sameSupport`
cover any supplied generated-spec list whose specs share one canonical
support, up to clause permutation.  This narrows the remaining blocker to
unguided discovery of that split, rather than verification of a supplied
same-support split.
The charge-guided support-inference lane removes the support variables from
that supplied split:
`parityCandidateCanonicalSupportFromBlock_eq_of_perm_generatedParitySpecs_sameSupport`
recovers the generator support from any nonempty same-support generated
component, and
`recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_perm_supportCharges`
accepts the component when the supplied charge list is correct.  The blocker is
therefore now charge-list and multiplicity discovery, not support inference for
this generated same-support lane.
The bounded charge-search lane now searches all Boolean charge lists up to a
supplied maximum:
`recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges`
and
`recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges`
prove success whenever the true charge list is inside that bound, while the
corresponding soundness and class bridges keep any returned decomposition on
the audited semantic path.  The component-bound theorem pair
`recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_componentBound`
and
`recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_componentBound`
now instantiates that search with the component's own clause count for
nonempty-support generated same-support components.  The remaining blocker is
deriving the charge multiplicities from arbitrary components, not supplying a
safe bound in this generated lane.  The semantic charge-presence lemmas
`gf2Sat_generatedParitySpecsForSupportCharges_iff_forall_mem`,
`gf2Sat_generatedParitySpecsForSupportCharges_iff_eraseDups`,
`gf2Sat_generatedParitySpecsForSupportCharges_iff_charge_presence`, and
`not_gf2Sat_generatedParitySpecsForSupportCharges_of_mem_false_true` further
pin down that blocker: duplicate same-support charges do not change GF(2)
semantics, while both charges together make the generated same-support GF(2)
formula unsatisfiable.  What remains is exact component coverage and
multiplicity reconstruction, not discovering new same-support semantic cases.
The compact target itself preserves exact multiplicity once a generated split is
available: `generatedParitySpecsGF2_forSupportCharges_rhs_eq` recovers the RHS
charge list from the generated GF(2) core, its true/false count corollaries
preserve per-charge multiplicities, and the matching
`generatedParitySpecsFallbackDecomposition_forSupportCharges_coreGF2_*` theorems
lift that fact to the residual-free decomposition interface.
The exact length lane now proves arity-three and arity-four generated
same-support component accounting:
`generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_three`,
`generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_four`,
`target_length_eq_charge_count_mul_four_of_perm_generatedParitySpecsForSupportCharges`,
and
`target_length_eq_charge_count_mul_eight_of_perm_generatedParitySpecsForSupportCharges`
show that component length is `charge_count * 4` for arity three and
`charge_count * 8` for arity four, transported across clause permutation.  This
lets component size determine total generated charge count in those lanes.  The
quotient/divisibility corollaries
`charges_length_eq_target_length_div_four_of_perm_generatedParitySpecsForSupportCharges`,
`charges_length_eq_target_length_div_eight_of_perm_generatedParitySpecsForSupportCharges`,
`target_length_mod_four_eq_zero_of_perm_generatedParitySpecsForSupportCharges`,
and
`target_length_mod_eight_eq_zero_of_perm_generatedParitySpecsForSupportCharges`
then justify arity-specific exact recovery bounds, and the
`recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_arityThreeExactBound`,
`recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_arityThreeExactBound`,
`recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_arityFourExactBound`,
and
`recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_arityFourExactBound`
wrappers use `target.length / 4` or `target.length / 8` as the executable
search bound.  This still does not recover charge identity or per-charge
multiplicity inside an arbitrary same-support component.
The remaining theorem-forming obligations are arbitrary declarative-class
completeness, stronger bounded-overlap/function-level framing, and generalized
same-support recovery; they are no longer this class-level permutation lift.

If a future probe or proof attempt finds content divergence under disjoint
framing, the intended fallback is to refactor extraction into support-component
grouping followed by local block recognition.
