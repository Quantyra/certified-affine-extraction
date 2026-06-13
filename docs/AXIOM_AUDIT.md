# Axiom Audit

The release audit surface is `lean/CertifiedAffine/Audit.lean`.

Run:

```bash
lake env lean lean/CertifiedAffine/Audit.lean
```

Current guarded declarations:

| Declaration | Axioms reported |
| --- | --- |
| `CertifiedAffine.TseitinCNFData.allFin_map_get` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.edgeAt_allFin_map_eq_edges` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.incidentIndices_length_eq_degree` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinModel.circulant12_edges_n_le_length` | `propext` |
| `CertifiedAffine.TseitinModel.circulant12_edges_undirected` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinModel.circulant12_edges_endpoints_in_range` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinModel.cycle_succ_mod_ne_self` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinModel.circulant12_succ_two_mod_ne_self` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinModel.circulant12_edges_no_self_loops` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinModel.encoding_circulant12_derived` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinModel.circulant12_degree_eq_eight` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinModel.circulant12_degree_pos` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.TseitinCycleGF2NormalizationSurface_correctnessInvariant` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.TseitinCycleCNFFormula_length` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.TseitinParityFormulaFromEncoding_length` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.TseitinCycleGF2NormalizationSurface_resourceCounts` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.mem_clausesForVertex_imp_exists_bad_row` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.NatListLexLEProp` | none |
| `CertifiedAffine.TseitinCNFData.natListLexLE_eq_decide_prop` | `propext` |
| `CertifiedAffine.TseitinCNFData.sortByBool_decide_eq_of_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.sortNatFingerprintAtoms_eq_of_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.sortClauseFingerprints_eq_of_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.sortFinByVal_eq_of_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.canonicalClauseSupportVars_eq_of_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.canonicalClauseSupportKey_eq_of_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.canonicalClauseFingerprint_eq_of_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.canonicalBlockFingerprint_eq_of_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.canonicalParityBlockRecognitionSignal_eq_of_block_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.canonicalParityBlockRecognitionSignal_of_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.ParityEncoded.Class.sound` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_of_appendGroupRecognition` | `propext` |
| `CertifiedAffine.TseitinCNFData.ExtractorCompleteness.splitCanonicalSupportClauseGroups_expandedCNF_perm` | `propext` |
| `CertifiedAffine.TseitinCNFData.ExtractorCompleteness.canonicalFingerprintRecognizedBlocksGF2_append` | `propext` |
| `CertifiedAffine.TseitinCNFData.ExtractorCompleteness.splitCanonicalSupportClauseGroups_append_of_residual_free` | `propext` |
| `CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_append_of_groupAppend` | `propext` |
| `CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_append_of_groupAppend` | `propext` |
| `CertifiedAffine.TseitinCNFData.ExtractorCompleteness.SemanticExtractorCompleteOn` | none |
| `CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_of_class` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_gf2_perm` | none |
| `CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_gf2_perm` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_append_of_fresh` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_append_of_clauseKeysDisjoint` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_append_of_clauseKeysDisjoint_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_append_of_disjointSupport` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_append_of_clauseKeysDisjoint` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_append_of_clauseKeysDisjoint_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_append_comm_of_clauseKeysDisjoint` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_append_of_disjointSupport` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_append_of_clauseKeysDisjoint` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_append_of_clauseKeysDisjoint_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_append_comm_of_clauseKeysDisjoint` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_append_of_disjointSupport` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.fold_insert_same_key_single` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_cons_eq_single_of_same_key` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportKey_of_perm` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.cnfClauseKeysDisjoint_of_perm_left` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.cnfClauseKeysDisjoint_of_perm_right` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.cnfClauseKeysDisjoint_of_perm` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.cnfClauseKeysDisjoint_symm` | none |
| `CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveNonemptySupport_of_perm` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.clauseSupport_clauseForAssignment_of_length` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.canonicalClauseSupportKey_clauseForAssignment_of_length` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.canonicalClauseSupportVars_clauseForAssignment_of_length` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportKey_foldl_clausesForVertex` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportKey_clausesForVertex` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportVars_clausesForVertex` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_eq_single_of_perm_clausesForVertex` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons_normal` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.parityCandidateCanonicalSupportFromBlock_eq_of_perm_clausesForVertex_normal` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveNonemptySupport_clausesForVertex` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.canonicalSupportClauseGroupsCNF_groupClausesByCanonicalSupport_perm` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.mem_groupKeys_groupClausesByCanonicalSupport_of_mem` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.mem_groupKeys_groupClausesByCanonicalSupport_iff` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.nodup_groupKeys_groupClausesByCanonicalSupport` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupKeys_groupClausesByCanonicalSupport_perm_of_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_insertClauseByCanonicalSupport_perm` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_fold_insert_perm` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_groupClausesByCanonicalSupport_perm` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_groupClausesByCanonicalSupport_perm_of_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_eq_nil_of_not_mem_groupKeys` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_perm_of_mem_group_nodup` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.exists_group_of_mem_groupKeys` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.SupportGroupsKeyMatchedCNFPerm` | none |
| `CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsKeyMatchedCNFPerm_groupClausesByCanonicalSupport_of_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.SupportGroupsHaveNonemptyCNF` | none |
| `CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveNonemptyCNF_insertClauseByCanonicalSupport` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveNonemptyCNF_fold_insert` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveNonemptyCNF_groupClausesByCanonicalSupport` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupCNF_exists_cons_of_mem_groupClausesByCanonicalSupport` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.cnf_exists_cons_of_perm_cons` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.exists_alignedSupportGroupCNFPermNonempty_of_keyMatched` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_exists_block_of_mem` | none |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_transport_of_keyMatchedCNFPerm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_residualFree_of_keyMatchedCNFPerm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_groupClausesByCanonicalSupport_of_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_groupClausesByCanonicalSupport_gf2_perm_of_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_residualFree_groupClausesByCanonicalSupport_of_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_gf2_perm_groupClausesByCanonicalSupport_of_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_residualFree_of_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_gf2_perm_of_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_groupClausesByCanonicalSupport_of_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_groupClausesByCanonicalSupport_of_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.finList_eq_of_map_val_eq` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.canonicalClauseSupportVars_eq_of_key_eq` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveOwnCanonicalSupportKey_insertClauseByCanonicalSupport` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveOwnCanonicalSupportKey_fold_insert` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveOwnCanonicalSupportKey_groupClausesByCanonicalSupport` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupClausesHaveCanonicalSupportKey_of_mem_groupClausesByCanonicalSupport` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportVars_of_perm` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupClausesHaveCanonicalSupportVars_of_mem_groupClausesByCanonicalSupport_cons` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.parityCandidateCanonicalSupportFromBlock_eq_of_supportVars_cons` | none |
| `CertifiedAffine.TseitinCNFData.GroupFrame.inferredCanonicalParityBlockSpec_eq_of_supportVars_cons` | none |
| `CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlockWithCharge_eq_none_of_perm_of_inferredSpec_eq` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_inferredSpec_eq` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_supportVars_cons` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlock_eq_some_of_perm_of_supportVars_cons` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_groupClausesByCanonicalSupport_cons` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlock_eq_some_of_perm_of_groupClausesByCanonicalSupport_cons` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.SupportGroupsFromGrouper` | none |
| `CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsFromGrouper_self` | none |
| `CertifiedAffine.TseitinCNFData.GroupFrame.AlignedSupportGroupCNFPermNonempty` | none |
| `CertifiedAffine.TseitinCNFData.GroupFrame.RecognizedBlockTransport` | none |
| `CertifiedAffine.TseitinCNFData.GroupFrame.RecognizedBlocksTransport` | none |
| `CertifiedAffine.TseitinCNFData.GroupFrame.recognizedBlockTransport_compactGF2_eq` | none |
| `CertifiedAffine.TseitinCNFData.GroupFrame.canonicalFingerprintRecognizedBlocksGF2_eq_of_recognizedBlocksTransport` | none |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_transport_of_alignedGroupCNFPerm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_transport_of_alignedGroupCNFPerm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_transport_of_group_perm` | `propext` |
| `CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_transport_of_group_perm` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recognizedParityCNFBlock` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_syntacticRecognizedBlock` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlock_perm` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlock_syntacticSignal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlock_toSyntactic_isSome_of_syntacticSignal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.parityBlockRecognitionSignal_clausesForVertex_self` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.parityBlockRecognitionSignal_of_perm_clausesForVertex` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalParityBlockRecognitionSignal_clausesForVertex_self` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_canonicalBlockFingerprint_iff` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalClauseFingerprint_mem_canonicalBlockFingerprint_of_mem` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_canonicalClauseFingerprint_iff` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.literal_sign_true_of_mem_clauseForAssignment_replicate_false` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.evenLiteralAtom_not_mem_canonicalClauseFingerprint_allFalse` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.true_mem_of_parity_true` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.exists_evenLiteralAtom_mem_canonicalClauseFingerprint_clauseForAssignment` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFingerprint_ne_of_mem_not_mem` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.parity_replicate_false` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_mem_canonicalBlockFingerprint_clausesForVertex_true` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFingerprint_clausesForVertex_true_false_ne_of_allFalseFingerprint_not_mem` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_not_mem_canonicalBlockFingerprint_clausesForVertex_false` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFingerprint_clausesForVertex_true_false_ne` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalParityBlockRecognitionSignal_eq_false_of_fingerprint_ne` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalParityBlockRecognitionSignal_clausesForVertex_true_false_eq_false_of_fingerprint_ne` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_clausesForVertex_self_toSyntactic` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_clausesForVertex_normal_toSyntactic` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal_of_signal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_false_normal_toSyntactic` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_false_of_perm_clausesForVertex_normal_of_signal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_eq_none_of_signal_false` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_clausesForVertex_true_false_eq_none_of_signal_false` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_falseMiss` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_true_of_perm_clausesForVertex_normal_of_signal_of_falseMiss` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalParityBlockRecognitionSignal_perm_clausesForVertex_true_false_eq_false` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_false_of_perm_clausesForVertex_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_true_of_perm_clausesForVertex_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_falseSignal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_fingerprint_ne` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_clausesForVertex_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_disjoint_clausesForVertex_append_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlocksGF2_append` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedSupportDisjointFamily` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_generatedSupportDisjointFamily` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedSupportDisjointFamily` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedKeyDisjointFamily` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_generatedKeyDisjointFamily` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedKeyDisjointFamily` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_generatedKeyDisjointFamily` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedParitySpec` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_append_singleton` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_append_singleton` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.foldl_append_singleton_eq_append_map` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.foldl_append_eq_append_bind` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_eq_bind` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_eq_map` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_sameSupport` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.firstSome?_eq_some_imp_exists_mem` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.firstSome?_exists_some_of_mem_eq_some` | `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_chargeListsUpTo_of_length_le` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_two_sameSupport` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_sameSupport` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_generatedParitySpecs` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_generatedParitySpecsCNF_imp_exists_spec` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clauseKeysDisjoint_generatedParitySpecsCNF_of_freshCanonicalSupportKeys` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_fromIncident` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_fromIncident` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFromIncident_append_singleton` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_fromEncoding` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_fromEncoding` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForCycle` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausesForVertex_exists_cons_of_length_four` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausesForVertex_exists_cons_of_vars_ne_empty` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.incidentClausesForVertex_exists_cons_of_degree_pos` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleIncidentIndices_length_eq_four` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleClausesForVertex_exists_cons` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFin_pairwise_val_lt` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFin_filter_varsInCanonicalSupportOrder` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.incidentIndices_varsInCanonicalSupportOrder` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleIncidentIndices_varsInCanonicalSupportOrder` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_canonicalSupportKeyForVars_iff` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.incidentIndex_mem_of_incident` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.incident_of_mem_incidentIndex` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleGraph_m_eq_two_mul` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleEvenEdgeIndex_lt` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleOddEdgeIndex_lt` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleEdgeAt_even_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleEdgeAt_odd_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKey_mem_even` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKey_mem_odd` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKey_not_mem_even_of_not_endpoint` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKey_not_mem_odd_of_not_endpoint` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKeys_ne_of_not_endpoint` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKeys_ne_of_right_not_endpoint` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycle_successor_mod_ne_self` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycle_successor_successor_mod_ne_self` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKeys_ne_of_successor` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKeys_ne_of_ne` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.circulant12CanonicalIncidentSupportKeys_ne_of_ne` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalIncidentSupportKeys_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSecondVertexFreshnessStep_false` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterBlocks_length` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterResidualCNF_length` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterCoreCNF_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterExpandedCNF_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterResidualCNF_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitter_not_residualFree_for_directGF2` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedSupportDisjointSpecList` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedSupportDisjointFamily_of_specList` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_generatedSupportDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedSupportDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedKeyDisjointSpecList` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedKeyDisjointFamily_of_specList` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_generatedKeyDisjointFamily` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_generatedKeyDisjointSpecList` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_tseitinCNFFormulaFromEncoding` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedCanonicalKeyFreshSpecList` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_snoc_of_exists` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromIncident_append_singleton` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromIncident_range_prefix` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh_degree_pos` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_forCycle_prefix` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_forCycle` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.circulant12IncidentSupportKeys_fresh` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCirculant12CNFFormula` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCirculant12CNFFormula` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_TseitinCirculant12CNFFormula` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_TseitinCycleCNFFormula` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_TseitinCycleCNFFormula_nonDegenerate` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlocks_permCertified` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlocksCNF_append` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.disjointSupport_append_right` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.cnfSupport_mem_of_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.disjointSupport_of_perm` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksPermCertified.append` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksAppendDisjoint.nil` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksAppendDisjoint.singleton` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksAppendDisjoint.append` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.disjointSupport_of_clause_subset_left` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.blockCNF_subset_canonicalFingerprintRecognizedBlocksCNF` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksDisjointFromCNF_of_disjointCovered` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksAppendDisjoint.append_of_disjointCovered` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksPermCertified.of_syntacticSignals` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksToSyntacticOk.append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksToSyntacticOk.singleton` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognizedWithSyntacticOk_exists_of_generatedKeyDisjointFamily` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognizedWithSyntacticOk_exists_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognizedWithSyntacticOk_exists_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksSyntacticSignals.of_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_CNF_eq` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_GF2_eq` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFromGeneratedParitySpec_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackBlocks_length` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackBlocks_CNF_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackBlocks_GF2_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackBlocks_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallback_exists` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_hasEmptyResidual` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_coreCNF_eq` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_expandedCNF_eq` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_coreGF2_eq` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_coreEquationCount` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_residualClauseCount` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_expandedClauseCount` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_hasEmptyResidual` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_expandedCNF_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_coreGF2_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_coreEquationCount` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_residualClauseCount` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_coreExpandedClauseCount` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_expandedClauseCount` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecs_eq_some_of_cnf_eq` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecs_sound` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecs_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecs_sound` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecs_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_sound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_sound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_sound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_sound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_sound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportDirectRecovery_eq_some` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSupportGroups_length` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportMergedSupportRecovery_isSome` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroup_sound` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroup_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecsPerm_eq_some_of_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecsPerm_sound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecsPerm_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_sound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.sameSupportTwoChargeCandidateSpecs_eq_of_perm_generatedParitySpecs_two_sameSupport` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_two_sameSupport` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_eq_some_of_perm_generatedParitySpecs_two_sameSupport` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_sameSupport` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.parityCandidateCanonicalSupportFromBlock_eq_of_perm_generatedParitySpecs_sameSupport` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_eq_some_of_perm_generatedParitySpecs_sameSupport` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_eq_some_of_perm_supportCharges` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_perm_supportCharges` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupTwoCharge_sound` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupTwoCharge_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGeneratedParitySpecs` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGeneratedParitySpecsPerm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverTwoChargeSameSupportGroup` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverTwoChargeSameSupportGroupPerm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSingleMergedSupportGroupTwoCharge` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSingleMergedSupportGroupFromGeneratedSpecsPerm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGeneratedParityChargesPerm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSingleMergedSupportGroupFromChargesPerm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGeneratedParityChargeSearchPerm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSingleMergedSupportGroupFromChargeSearchPerm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_recoverTwoChargeSameSupportGroup` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_recoverTwoChargeSameSupportGroupPerm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.sameSupportTwoChargeCandidateSpecs_twoCycle_eq_generated` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCNF_clausesHaveCandidateSupportVars` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.sameSupportTwoChargeCandidateSpecs_eq_generated_of_perm_twoCycle` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_eq_some_of_perm_twoCycle` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_twoCycle_eq_none` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupClausesByCanonicalSupport_eq_single_of_perm_twoCycle` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_eq_none_of_perm_twoCycle` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportUnguidedDirectRecovery_eq_some` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportUnguidedMergedSupportRecovery_isSome` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportUnguidedDirectRecovery_reverse_isSome_false` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportUnguidedPermDirectRecovery_reverse_isSome` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitCanonicalSupportClauseGroupsWithTwoChargeFallback_expandedCNF_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_expandedCNF_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_syntacticSignals_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.EnhancedExtractorCompleteOn` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.EnhancedSemanticExtractorCompleteOn` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitCanonicalSupportClauseGroupsWithTwoChargeFallback_append_of_residual_free` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_append_of_clauseKeysDisjoint` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_append_of_disjointSupport` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitCanonicalSupportClauseGroupsWithTwoChargeFallback_of_groupsRecognized` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_groupRecognition` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_of_groupAppend` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_of_clauseKeysDisjoint` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_of_disjointSupport` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_class` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_of_groupAppend` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_of_clauseKeysDisjoint` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_of_disjointSupport` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_singleGroupTwoChargeFallback` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_perm_generatedParitySpecs_two_sameSupport` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle_reversed` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle_of_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointFamily_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointSpecList_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCirculant12CNFFormula_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_expandedCNF_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_coreGF2_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_hasEmptyResidual` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_coreEquationCount` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_residualClauseCount` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_expandedCNF_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_coreGF2_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_hasEmptyResidual` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_coreEquationCount` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_residualClauseCount` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlocksCNF_perm_of_groupsRecognized` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_groupRecognition_syntacticSignals` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_groupRecognition_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_groupRecognition_toSyntacticOk_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_groupRecognition_syntacticSignals` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_singleGroupRecognition_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_groupRecognition_syntacticSignals_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_certifiedRecognizedCNF` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_certifiedRecognizedCNF` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_certifiedRecognizedCNF` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_certifiedRecognizedCNF_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_certifiedRecognizedCNF_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_certifiedRecognizedCNF` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_certifiedRecognizedCNF` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlock_perm_of_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.ClausePermutedRecognizedBlock.toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_of_singleRecognizedGroup_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_of_perm_clausesForVertex_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal_of_signal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_false_normal_of_signal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_perm_clausesForVertex_false_normal_of_signal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_false_normal_of_signal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal_of_signal_of_falseMiss` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_true_normal_of_signal_of_falseMiss` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_perm_clausesForVertex_true_normal_of_signal_of_falseMiss` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_true_normal_of_signal_of_falseMiss` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_false_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_perm_clausesForVertex_false_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_false_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_true_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_perm_clausesForVertex_true_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_true_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.certifiedRecognizedCNF_of_clausePermutedRecognizedBlock` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_clausePermutedRecognizedBlock` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_clausePermutedRecognizedBlock` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_clausePermutedRecognizedBlock` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_clausePermutedRecognizedBlock` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedBlock` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_append_keyDisjoint_perm` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_append_comm_keyDisjoint` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_cnf_perm` | none |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_clausePermutedRecognizedClass` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_clausePermutedRecognizedClass` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_empty` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_clausePermutedRecognizedClass` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_clausePermutedRecognizedClass` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_clausePermutedRecognizedClass_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_clausePermutedRecognizedClass_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_empty` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_clausePermutedRecognizedClass` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedClass` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_clausePermutedRecognizedClass_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedClass_perm` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_perm_clausesForVertex_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_clausesForVertex_normal` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_clausesForVertex_normal_via_clausePermutedRecognizedBlock` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_clausesForVertex_normal_via_clausePermutedRecognizedBlock` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_clausesForVertex_normal_via_clausePermutedRecognizedBlock` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_generatedKeyDisjointFamily` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_generatedKeyDisjointSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_generatedCanonicalKeyFreshSpecList` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.length_le_bind_length_of_forall_exists_cons` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_length_le_cnf_length_of_vars_ne_empty` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.charges_length_le_of_perm_generatedParitySpecsForSupportCharges` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_componentBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_componentBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_eq_map` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_iff_forall_mem` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_iff_eraseDups` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_iff_charge_presence` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.not_gf2Sat_generatedParitySpecsForSupportCharges_of_mem_false_true` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_cnf_length_eq_mul_of_block_length` | `propext` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_three` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_four` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_eq_charge_count_mul_four_of_perm_generatedParitySpecsForSupportCharges` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_eq_charge_count_mul_eight_of_perm_generatedParitySpecsForSupportCharges` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.charges_length_eq_target_length_div_four_of_perm_generatedParitySpecsForSupportCharges` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_mod_four_eq_zero_of_perm_generatedParitySpecsForSupportCharges` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.charges_length_eq_target_length_div_eight_of_perm_generatedParitySpecsForSupportCharges` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_mod_eight_eq_zero_of_perm_generatedParitySpecsForSupportCharges` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_arityThreeExactBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_arityThreeExactBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_arityFourExactBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_arityFourExactBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_disjoint_appendGroupRecognition` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_singleGroupRecognition_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_singleGroupRecognition_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_disjoint_appendGroupRecognition_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_disjoint_appendGroupRecognition_toSyntacticOk_append` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk_append` | `propext`, `Classical.choice`, `Quot.sound` |

`Lean.ofReduceBool` is not in the guarded theorem path.  Older finite
canonical-extractor smoke tests may still rely on computed witnesses; those are
not the exported clean theorem path.
