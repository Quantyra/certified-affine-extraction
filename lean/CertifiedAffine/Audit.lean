import CertifiedAffine.TseitinCNFData
import CertifiedAffine.ParityEncoded
import CertifiedAffine.ExtractorCompleteness
import CertifiedAffine.ExtractorCompletenessInstances
import CertifiedAffine.ExtractorCompletenessUniform
import CertifiedAffine.GroupFrame
import CertifiedAffine.CanonicalSort
import CertifiedAffine.AtomicClassBridge

/-!
# CertifiedAffine Audit Surface

This module is intended for publication/release CI.  It guards the current
exported uniform direct-cycle GF(2) theorem path against accidental trust-base
drift.  The older finite canonical-extractor path is still documented as an
internal trust boundary and is not included in this clean audit surface yet.
-/

/-- info: 'CertifiedAffine.TseitinCNFData.allFin_map_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.allFin_map_get

/-- info: 'CertifiedAffine.TseitinCNFData.edgeAt_allFin_map_eq_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.edgeAt_allFin_map_eq_edges

/-- info: 'CertifiedAffine.TseitinCNFData.incidentIndices_length_eq_degree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.incidentIndices_length_eq_degree

/-- info: 'CertifiedAffine.TseitinModel.circulant12_edges_n_le_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinModel.circulant12_edges_n_le_length

/-- info: 'CertifiedAffine.TseitinModel.circulant12_edges_undirected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinModel.circulant12_edges_undirected

/-- info: 'CertifiedAffine.TseitinModel.circulant12_edges_endpoints_in_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinModel.circulant12_edges_endpoints_in_range

/-- info: 'CertifiedAffine.TseitinModel.cycle_succ_mod_ne_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinModel.cycle_succ_mod_ne_self

/-- info: 'CertifiedAffine.TseitinModel.circulant12_succ_two_mod_ne_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinModel.circulant12_succ_two_mod_ne_self

/-- info: 'CertifiedAffine.TseitinModel.circulant12_edges_no_self_loops' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinModel.circulant12_edges_no_self_loops

/-- info: 'CertifiedAffine.TseitinModel.encoding_circulant12_derived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinModel.encoding_circulant12_derived

/-- info: 'CertifiedAffine.TseitinModel.circulant12_degree_eq_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinModel.circulant12_degree_eq_eight

/-- info: 'CertifiedAffine.TseitinModel.circulant12_degree_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinModel.circulant12_degree_pos

/-- info: 'CertifiedAffine.TseitinCNFData.TseitinCycleGF2NormalizationSurface_correctnessInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.TseitinCycleGF2NormalizationSurface_correctnessInvariant

/-- info: 'CertifiedAffine.TseitinCNFData.TseitinCycleCNFFormula_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.TseitinCycleCNFFormula_length

/-- info: 'CertifiedAffine.TseitinCNFData.TseitinParityFormulaFromEncoding_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.TseitinParityFormulaFromEncoding_length

/-- info: 'CertifiedAffine.TseitinCNFData.TseitinCycleGF2NormalizationSurface_resourceCounts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.TseitinCycleGF2NormalizationSurface_resourceCounts

/-- info: 'CertifiedAffine.TseitinCNFData.allAssignments_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.allAssignments_nodup

/-- info: 'CertifiedAffine.TseitinCNFData.allAssignments_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.allAssignments_length

/-- info: 'CertifiedAffine.TseitinCNFData.allAssignments_countP_parity_eq_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.allAssignments_countP_parity_eq_succ

/-- info: 'CertifiedAffine.TseitinCNFData.allAssignments_count_replicate_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.allAssignments_count_replicate_false

/-- info: 'CertifiedAffine.TseitinCNFData.boolList_eq_replicate_false_of_true_not_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.boolList_eq_replicate_false_of_true_not_mem

/-- info: 'CertifiedAffine.TseitinCNFData.clausesForVertex_length_eq_countP_bad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.clausesForVertex_length_eq_countP_bad

/-- info: 'CertifiedAffine.TseitinCNFData.clausesForVertex_length_of_length_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.clausesForVertex_length_of_length_succ

/-- info: 'CertifiedAffine.TseitinCNFData.clausesForVertex_length_eq_pow_pred_of_vars_ne_empty' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.clausesForVertex_length_eq_pow_pred_of_vars_ne_empty

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySupportBlockSize_eq_pow_pred_of_vars_ne_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySupportBlockSize_eq_pow_pred_of_vars_ne_empty

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySupportBlockSize_pos_of_vars_ne_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySupportBlockSize_pos_of_vars_ne_empty

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausesForVertex_length_eq_generatedParitySupportBlockSize' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausesForVertex_length_eq_generatedParitySupportBlockSize

/-- info: 'CertifiedAffine.TseitinCNFData.mem_clausesForVertex_imp_exists_bad_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.mem_clausesForVertex_imp_exists_bad_row

/-- info: 'CertifiedAffine.TseitinCNFData.NatListLexLEProp' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.NatListLexLEProp

/-- info: 'CertifiedAffine.TseitinCNFData.natListLexLE_eq_decide_prop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.natListLexLE_eq_decide_prop

/-- info: 'CertifiedAffine.TseitinCNFData.sortByBool_decide_eq_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.sortByBool_decide_eq_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.sortNatFingerprintAtoms_eq_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.sortNatFingerprintAtoms_eq_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.sortClauseFingerprints_eq_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.sortClauseFingerprints_eq_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.sortFinByVal_eq_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.sortFinByVal_eq_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.canonicalClauseSupportVars_eq_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.canonicalClauseSupportVars_eq_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.canonicalClauseSupportKey_eq_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.canonicalClauseSupportKey_eq_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.canonicalClauseFingerprint_eq_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.canonicalClauseFingerprint_eq_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.canonicalBlockFingerprint_eq_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.canonicalBlockFingerprint_eq_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.canonicalParityBlockRecognitionSignal_eq_of_block_perm' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.canonicalParityBlockRecognitionSignal_eq_of_block_perm

/-- info: 'CertifiedAffine.TseitinCNFData.canonicalParityBlockRecognitionSignal_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.canonicalParityBlockRecognitionSignal_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.ParityEncoded.Class.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ParityEncoded.Class.sound

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_of_appendGroupRecognition' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_of_appendGroupRecognition

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.splitCanonicalSupportClauseGroups_expandedCNF_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.splitCanonicalSupportClauseGroups_expandedCNF_perm

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.canonicalFingerprintRecognizedBlocksGF2_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.canonicalFingerprintRecognizedBlocksGF2_append

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.splitCanonicalSupportClauseGroups_append_of_residual_free' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.splitCanonicalSupportClauseGroups_append_of_residual_free

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_append_of_groupAppend' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_append_of_groupAppend

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_append_of_groupAppend' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_append_of_groupAppend

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.SemanticExtractorCompleteOn' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.SemanticExtractorCompleteOn

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_of_class' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_of_class

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_gf2_perm' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_gf2_perm

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_gf2_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_gf2_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_append_of_fresh' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_append_of_fresh

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint_perm' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_append_of_clauseKeysDisjoint_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_append_of_disjointSupport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_append_of_clauseKeysDisjoint' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_append_of_clauseKeysDisjoint

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_append_of_clauseKeysDisjoint_perm' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_append_of_clauseKeysDisjoint_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_append_of_disjointSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_append_of_disjointSupport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_append_of_clauseKeysDisjoint' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_append_of_clauseKeysDisjoint

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_append_of_clauseKeysDisjoint_perm' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_append_of_clauseKeysDisjoint_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_append_comm_of_clauseKeysDisjoint' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_append_comm_of_clauseKeysDisjoint

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_append_of_disjointSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_append_of_disjointSupport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_append_of_clauseKeysDisjoint' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_append_of_clauseKeysDisjoint

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_append_of_clauseKeysDisjoint_perm' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_append_of_clauseKeysDisjoint_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_append_comm_of_clauseKeysDisjoint' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_append_comm_of_clauseKeysDisjoint

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_append_of_disjointSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_append_of_disjointSupport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.fold_insert_same_key_single' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.fold_insert_same_key_single

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_cons_eq_single_of_same_key' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_cons_eq_single_of_same_key

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportKey_of_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportKey_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.cnfClauseKeysDisjoint_of_perm_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.cnfClauseKeysDisjoint_of_perm_left

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.cnfClauseKeysDisjoint_of_perm_right' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.cnfClauseKeysDisjoint_of_perm_right

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.cnfClauseKeysDisjoint_of_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.cnfClauseKeysDisjoint_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.cnfClauseKeysDisjoint_symm' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.cnfClauseKeysDisjoint_symm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveNonemptySupport_of_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveNonemptySupport_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.clauseSupport_clauseForAssignment_of_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.clauseSupport_clauseForAssignment_of_length

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.canonicalClauseSupportKey_clauseForAssignment_of_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.canonicalClauseSupportKey_clauseForAssignment_of_length

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.canonicalClauseSupportVars_clauseForAssignment_of_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.canonicalClauseSupportVars_clauseForAssignment_of_length

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportKey_foldl_clausesForVertex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportKey_foldl_clausesForVertex

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportKey_clausesForVertex' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportKey_clausesForVertex

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportVars_clausesForVertex' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportVars_clausesForVertex

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_clausesForVertex_eq_single_of_cons

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_eq_single_of_perm_clausesForVertex' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesByCanonicalSupport_eq_single_of_perm_clausesForVertex

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons_normal' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.parityCandidateCanonicalSupportFromBlock_clausesForVertex_eq_of_cons_normal

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.parityCandidateCanonicalSupportFromBlock_eq_of_perm_clausesForVertex_normal' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.parityCandidateCanonicalSupportFromBlock_eq_of_perm_clausesForVertex_normal

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveNonemptySupport_clausesForVertex' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveNonemptySupport_clausesForVertex

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.canonicalSupportClauseGroupsCNF_groupClausesByCanonicalSupport_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.canonicalSupportClauseGroupsCNF_groupClausesByCanonicalSupport_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.mem_groupKeys_groupClausesByCanonicalSupport_of_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.mem_groupKeys_groupClausesByCanonicalSupport_of_mem

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.mem_groupKeys_groupClausesByCanonicalSupport_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.mem_groupKeys_groupClausesByCanonicalSupport_iff

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.nodup_groupKeys_groupClausesByCanonicalSupport' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.nodup_groupKeys_groupClausesByCanonicalSupport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupKeys_groupClausesByCanonicalSupport_perm_of_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupKeys_groupClausesByCanonicalSupport_perm_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_insertClauseByCanonicalSupport_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_insertClauseByCanonicalSupport_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_fold_insert_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_fold_insert_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_groupClausesByCanonicalSupport_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_groupClausesByCanonicalSupport_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_groupClausesByCanonicalSupport_perm_of_perm' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_groupClausesByCanonicalSupport_perm_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_eq_nil_of_not_mem_groupKeys' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_eq_nil_of_not_mem_groupKeys

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_perm_of_mem_group_nodup' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupClausesForKey_perm_of_mem_group_nodup

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.exists_group_of_mem_groupKeys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.exists_group_of_mem_groupKeys

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.SupportGroupsKeyMatchedCNFPerm' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.SupportGroupsKeyMatchedCNFPerm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsKeyMatchedCNFPerm_groupClausesByCanonicalSupport_of_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsKeyMatchedCNFPerm_groupClausesByCanonicalSupport_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.SupportGroupsHaveNonemptyCNF' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.SupportGroupsHaveNonemptyCNF

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveNonemptyCNF_insertClauseByCanonicalSupport' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveNonemptyCNF_insertClauseByCanonicalSupport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveNonemptyCNF_fold_insert' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveNonemptyCNF_fold_insert

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveNonemptyCNF_groupClausesByCanonicalSupport' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveNonemptyCNF_groupClausesByCanonicalSupport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupCNF_exists_cons_of_mem_groupClausesByCanonicalSupport' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupCNF_exists_cons_of_mem_groupClausesByCanonicalSupport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.cnf_exists_cons_of_perm_cons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.cnf_exists_cons_of_perm_cons

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.exists_alignedSupportGroupCNFPermNonempty_of_keyMatched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.exists_alignedSupportGroupCNFPermNonempty_of_keyMatched

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_exists_block_of_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_exists_block_of_mem

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_transport_of_keyMatchedCNFPerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_transport_of_keyMatchedCNFPerm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_residualFree_of_keyMatchedCNFPerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_residualFree_of_keyMatchedCNFPerm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_groupClausesByCanonicalSupport_of_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_groupClausesByCanonicalSupport_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_groupClausesByCanonicalSupport_gf2_perm_of_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_groupClausesByCanonicalSupport_gf2_perm_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_residualFree_groupClausesByCanonicalSupport_of_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_residualFree_groupClausesByCanonicalSupport_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_gf2_perm_groupClausesByCanonicalSupport_of_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_gf2_perm_groupClausesByCanonicalSupport_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_residualFree_of_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_residualFree_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_gf2_perm_of_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.splitArityFourParityCanonicalSupportGroups_gf2_perm_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_groupClausesByCanonicalSupport_of_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.extractorCompleteOn_groupClausesByCanonicalSupport_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_groupClausesByCanonicalSupport_of_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.semanticExtractorCompleteOn_groupClausesByCanonicalSupport_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.finList_eq_of_map_val_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.finList_eq_of_map_val_eq

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.canonicalClauseSupportVars_eq_of_key_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.canonicalClauseSupportVars_eq_of_key_eq

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveOwnCanonicalSupportKey_insertClauseByCanonicalSupport' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveOwnCanonicalSupportKey_insertClauseByCanonicalSupport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveOwnCanonicalSupportKey_fold_insert' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveOwnCanonicalSupportKey_fold_insert

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveOwnCanonicalSupportKey_groupClausesByCanonicalSupport' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsHaveOwnCanonicalSupportKey_groupClausesByCanonicalSupport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupClausesHaveCanonicalSupportKey_of_mem_groupClausesByCanonicalSupport' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupClausesHaveCanonicalSupportKey_of_mem_groupClausesByCanonicalSupport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportVars_of_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.cnfClausesHaveCanonicalSupportVars_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupClausesHaveCanonicalSupportVars_of_mem_groupClausesByCanonicalSupport_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupClausesHaveCanonicalSupportVars_of_mem_groupClausesByCanonicalSupport_cons

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.parityCandidateCanonicalSupportFromBlock_eq_of_supportVars_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.parityCandidateCanonicalSupportFromBlock_eq_of_supportVars_cons

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.inferredCanonicalParityBlockSpec_eq_of_supportVars_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.inferredCanonicalParityBlockSpec_eq_of_supportVars_cons

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlockWithCharge_eq_none_of_perm_of_inferredSpec_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlockWithCharge_eq_none_of_perm_of_inferredSpec_eq

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_inferredSpec_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_inferredSpec_eq

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_supportVars_cons' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_supportVars_cons

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlock_eq_some_of_perm_of_supportVars_cons' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlock_eq_some_of_perm_of_supportVars_cons

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_groupClausesByCanonicalSupport_cons' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlockWithCharge_eq_some_of_perm_of_groupClausesByCanonicalSupport_cons

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlock_eq_some_of_perm_of_groupClausesByCanonicalSupport_cons' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.inferCanonicalParityBlock_eq_some_of_perm_of_groupClausesByCanonicalSupport_cons

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.SupportGroupsFromGrouper' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.SupportGroupsFromGrouper

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsFromGrouper_self' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.supportGroupsFromGrouper_self

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.AlignedSupportGroupCNFPermNonempty' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.AlignedSupportGroupCNFPermNonempty

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.RecognizedBlockTransport' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.RecognizedBlockTransport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.RecognizedBlocksTransport' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.RecognizedBlocksTransport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.recognizedBlockTransport_compactGF2_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.recognizedBlockTransport_compactGF2_eq

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.canonicalFingerprintRecognizedBlocksGF2_eq_of_recognizedBlocksTransport' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.canonicalFingerprintRecognizedBlocksGF2_eq_of_recognizedBlocksTransport

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_transport_of_alignedGroupCNFPerm' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_transport_of_alignedGroupCNFPerm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_transport_of_alignedGroupCNFPerm' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_transport_of_alignedGroupCNFPerm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_transport_of_group_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.groupsRecognized_transport_of_group_perm

/-- info: 'CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_transport_of_group_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.GroupFrame.splitCanonicalSupportClauseGroups_transport_of_group_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recognizedParityCNFBlock' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recognizedParityCNFBlock

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_syntacticRecognizedBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_syntacticRecognizedBlock

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlock_perm' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlock_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlock_syntacticSignal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlock_syntacticSignal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlock_toSyntactic_isSome_of_syntacticSignal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlock_toSyntactic_isSome_of_syntacticSignal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.parityBlockRecognitionSignal_clausesForVertex_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.parityBlockRecognitionSignal_clausesForVertex_self

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.parityBlockRecognitionSignal_of_perm_clausesForVertex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.parityBlockRecognitionSignal_of_perm_clausesForVertex

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalParityBlockRecognitionSignal_clausesForVertex_self' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalParityBlockRecognitionSignal_clausesForVertex_self

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_canonicalBlockFingerprint_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_canonicalBlockFingerprint_iff

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.sortClauseFingerprints_count_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.sortClauseFingerprints_count_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_canonicalBlockFingerprint_append_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_canonicalBlockFingerprint_append_iff

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFingerprint_count_append' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFingerprint_count_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalClauseFingerprint_mem_canonicalBlockFingerprint_of_mem' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalClauseFingerprint_mem_canonicalBlockFingerprint_of_mem

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_canonicalClauseFingerprint_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_canonicalClauseFingerprint_iff

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.literal_sign_true_of_mem_clauseForAssignment_replicate_false' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.literal_sign_true_of_mem_clauseForAssignment_replicate_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.evenLiteralAtom_not_mem_canonicalClauseFingerprint_allFalse' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.evenLiteralAtom_not_mem_canonicalClauseFingerprint_allFalse

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.true_mem_of_parity_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.true_mem_of_parity_true

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.exists_evenLiteralAtom_mem_canonicalClauseFingerprint_clauseForAssignment' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.exists_evenLiteralAtom_mem_canonicalClauseFingerprint_clauseForAssignment

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFingerprint_ne_of_mem_not_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFingerprint_ne_of_mem_not_mem

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.parity_replicate_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.parity_replicate_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_mem_canonicalBlockFingerprint_clausesForVertex_true' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_mem_canonicalBlockFingerprint_clausesForVertex_true

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFingerprint_clausesForVertex_true_false_ne_of_allFalseFingerprint_not_mem' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFingerprint_clausesForVertex_true_false_ne_of_allFalseFingerprint_not_mem

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_not_mem_canonicalBlockFingerprint_clausesForVertex_false' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_not_mem_canonicalBlockFingerprint_clausesForVertex_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFingerprint_clausesForVertex_true_false_ne' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFingerprint_clausesForVertex_true_false_ne

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalParityBlockRecognitionSignal_eq_false_of_fingerprint_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalParityBlockRecognitionSignal_eq_false_of_fingerprint_ne

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalParityBlockRecognitionSignal_clausesForVertex_true_false_eq_false_of_fingerprint_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalParityBlockRecognitionSignal_clausesForVertex_true_false_eq_false_of_fingerprint_ne

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_clausesForVertex_self_toSyntactic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_clausesForVertex_self_toSyntactic

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_clausesForVertex_normal_toSyntactic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_clausesForVertex_normal_toSyntactic

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal_of_signal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal_of_signal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_false_normal_toSyntactic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_false_normal_toSyntactic

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_false_of_perm_clausesForVertex_normal_of_signal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_false_of_perm_clausesForVertex_normal_of_signal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_eq_none_of_signal_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_eq_none_of_signal_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_clausesForVertex_true_false_eq_none_of_signal_false' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_clausesForVertex_true_false_eq_none_of_signal_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_falseMiss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_falseMiss

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_true_of_perm_clausesForVertex_normal_of_signal_of_falseMiss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_true_of_perm_clausesForVertex_normal_of_signal_of_falseMiss

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlockWithCharge_of_perm_clausesForVertex_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalParityBlockRecognitionSignal_perm_clausesForVertex_true_false_eq_false' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalParityBlockRecognitionSignal_perm_clausesForVertex_true_false_eq_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_false_of_perm_clausesForVertex_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_false_of_perm_clausesForVertex_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_true_of_perm_clausesForVertex_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_true_of_perm_clausesForVertex_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_falseSignal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_falseSignal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_fingerprint_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic_of_fingerprint_ne

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_true_normal_toSyntactic

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_clausesForVertex_normal_toSyntactic

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_clausesForVertex_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_clausesForVertex_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_disjoint_clausesForVertex_append_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_disjoint_clausesForVertex_append_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlocksGF2_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlocksGF2_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized_keyDisjoint

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_clausesForVertex_normal_of_groupsRecognized

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedSupportDisjointFamily' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedSupportDisjointFamily

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_generatedSupportDisjointFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_generatedSupportDisjointFamily

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedSupportDisjointFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedSupportDisjointFamily

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedKeyDisjointFamily' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedKeyDisjointFamily

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_generatedKeyDisjointFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_generatedKeyDisjointFamily

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedKeyDisjointFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedKeyDisjointFamily

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_generatedKeyDisjointFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_generatedKeyDisjointFamily

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedParitySpec' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedParitySpec

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_append_singleton' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_append_singleton

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_append_singleton' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_append_singleton

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.foldl_append_singleton_eq_append_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.foldl_append_singleton_eq_append_map

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.foldl_append_eq_append_bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.foldl_append_eq_append_bind

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_eq_bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_eq_bind

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_eq_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_eq_map

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_sameSupport' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_sameSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.firstSome?_eq_some_imp_exists_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.firstSome?_eq_some_imp_exists_mem

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.firstSome?_exists_some_of_mem_eq_some' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.firstSome?_exists_some_of_mem_eq_some

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_chargeListsUpTo_of_length_le' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_chargeListsUpTo_of_length_le

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_two_sameSupport' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_two_sameSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_sameSupport' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cnfClausesHaveCanonicalSupportVars_generatedParitySpecs_sameSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_generatedParitySpecs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_generatedParitySpecs

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_generatedParitySpecsCNF_imp_exists_spec' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_generatedParitySpecsCNF_imp_exists_spec

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clauseKeysDisjoint_generatedParitySpecsCNF_of_freshCanonicalSupportKeys' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clauseKeysDisjoint_generatedParitySpecsCNF_of_freshCanonicalSupportKeys

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_fromIncident' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_fromIncident

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_fromIncident' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_fromIncident

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFromIncident_append_singleton' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFromIncident_append_singleton

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_fromEncoding' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_fromEncoding

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_fromEncoding' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_fromEncoding

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForCycle

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausesForVertex_exists_cons_of_length_four' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausesForVertex_exists_cons_of_length_four

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausesForVertex_exists_cons_of_vars_ne_empty' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausesForVertex_exists_cons_of_vars_ne_empty

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.incidentClausesForVertex_exists_cons_of_degree_pos' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.incidentClausesForVertex_exists_cons_of_degree_pos

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleIncidentIndices_length_eq_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleIncidentIndices_length_eq_four

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleClausesForVertex_exists_cons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleClausesForVertex_exists_cons

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFin_pairwise_val_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFin_pairwise_val_lt

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFin_filter_varsInCanonicalSupportOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFin_filter_varsInCanonicalSupportOrder

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.incidentIndices_varsInCanonicalSupportOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.incidentIndices_varsInCanonicalSupportOrder

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleIncidentIndices_varsInCanonicalSupportOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleIncidentIndices_varsInCanonicalSupportOrder

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_canonicalSupportKeyForVars_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.mem_canonicalSupportKeyForVars_iff

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.incidentIndex_mem_of_incident' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.incidentIndex_mem_of_incident

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.incident_of_mem_incidentIndex' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.incident_of_mem_incidentIndex

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleGraph_m_eq_two_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleGraph_m_eq_two_mul

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleEvenEdgeIndex_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleEvenEdgeIndex_lt

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleOddEdgeIndex_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleOddEdgeIndex_lt

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleEdgeAt_even_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleEdgeAt_even_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleEdgeAt_odd_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleEdgeAt_odd_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKey_mem_even' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKey_mem_even

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKey_mem_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKey_mem_odd

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKey_not_mem_even_of_not_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKey_not_mem_even_of_not_endpoint

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKey_not_mem_odd_of_not_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKey_not_mem_odd_of_not_endpoint

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKeys_ne_of_not_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKeys_ne_of_not_endpoint

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKeys_ne_of_right_not_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKeys_ne_of_right_not_endpoint

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycle_successor_mod_ne_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycle_successor_mod_ne_self

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycle_successor_successor_mod_ne_self' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycle_successor_successor_mod_ne_self

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKeys_ne_of_successor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKeys_ne_of_successor

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKeys_ne_of_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cycleCanonicalIncidentSupportKeys_ne_of_ne

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.circulant12CanonicalIncidentSupportKeys_ne_of_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.circulant12CanonicalIncidentSupportKeys_ne_of_ne

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalIncidentSupportKeys_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalIncidentSupportKeys_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSecondVertexFreshnessStep_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSecondVertexFreshnessStep_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterBlocks_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterBlocks_length

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterResidualCNF_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterResidualCNF_length

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterCoreCNF_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterCoreCNF_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterExpandedCNF_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterExpandedCNF_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterResidualCNF_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitterResidualCNF_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitter_not_residualFree_for_directGF2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSplitter_not_residualFree_for_directGF2

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedSupportDisjointSpecList' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedSupportDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedSupportDisjointFamily_of_specList' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedSupportDisjointFamily_of_specList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_generatedSupportDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_generatedSupportDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedSupportDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedSupportDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedKeyDisjointSpecList' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedKeyDisjointFamily_of_specList' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedKeyDisjointFamily_of_specList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_generatedKeyDisjointFamily' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_generatedKeyDisjointFamily

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_tseitinCNFFormulaFromEncoding' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_tseitinCNFFormulaFromEncoding

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedCanonicalKeyFreshSpecList' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.GeneratedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_snoc_of_exists' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_snoc_of_exists

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromIncident_append_singleton' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromIncident_append_singleton

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromIncident_range_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromIncident_range_prefix

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh_degree_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_fromEncoding_of_incidentKeyFresh_degree_pos

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_forCycle_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_forCycle_prefix

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_forCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedCanonicalKeyFreshSpecList_forCycle

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedKeyDisjointSpecList_of_canonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.circulant12IncidentSupportKeys_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.circulant12IncidentSupportKeys_fresh

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCirculant12CNFFormula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCirculant12CNFFormula

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCirculant12CNFFormula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCirculant12CNFFormula

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_TseitinCirculant12CNFFormula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_TseitinCirculant12CNFFormula

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_TseitinCycleCNFFormula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_TseitinCycleCNFFormula

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_TseitinCycleCNFFormula_nonDegenerate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_TseitinCycleCNFFormula_nonDegenerate

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlocks_permCertified' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlocks_permCertified

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlocksCNF_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlocksCNF_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.disjointSupport_append_right' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.disjointSupport_append_right

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.cnfSupport_mem_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.cnfSupport_mem_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.disjointSupport_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.disjointSupport_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksPermCertified.append' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksPermCertified.append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksAppendDisjoint.nil' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksAppendDisjoint.nil

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksAppendDisjoint.singleton' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksAppendDisjoint.singleton

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksAppendDisjoint.append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksAppendDisjoint.append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.disjointSupport_of_clause_subset_left' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.disjointSupport_of_clause_subset_left

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.blockCNF_subset_canonicalFingerprintRecognizedBlocksCNF' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.blockCNF_subset_canonicalFingerprintRecognizedBlocksCNF

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksDisjointFromCNF_of_disjointCovered' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksDisjointFromCNF_of_disjointCovered

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksAppendDisjoint.append_of_disjointCovered' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksAppendDisjoint.append_of_disjointCovered

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksPermCertified.of_syntacticSignals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksPermCertified.of_syntacticSignals

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksToSyntacticOk.append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksToSyntacticOk.append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksToSyntacticOk.singleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksToSyntacticOk.singleton

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognizedWithSyntacticOk_exists_of_generatedKeyDisjointFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognizedWithSyntacticOk_exists_of_generatedKeyDisjointFamily

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognizedWithSyntacticOk_exists_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognizedWithSyntacticOk_exists_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognizedWithSyntacticOk_exists_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognizedWithSyntacticOk_exists_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksSyntacticSignals.of_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.CanonicalBlocksSyntacticSignals.of_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_CNF_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_CNF_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_GF2_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_GF2_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFromGeneratedParitySpec_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlockFromGeneratedParitySpec_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackBlocks_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackBlocks_length

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackBlocks_CNF_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackBlocks_CNF_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackBlocks_GF2_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackBlocks_GF2_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackBlocks_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackBlocks_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallback_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallback_exists

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_hasEmptyResidual' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_hasEmptyResidual

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_coreCNF_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_coreCNF_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_expandedCNF_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_expandedCNF_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_coreGF2_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_coreGF2_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_coreEquationCount' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_coreEquationCount

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_residualClauseCount' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_residualClauseCount

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_expandedClauseCount' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_expandedClauseCount

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_hasEmptyResidual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_hasEmptyResidual

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_expandedCNF_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_expandedCNF_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_coreGF2_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_coreGF2_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_coreEquationCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_coreEquationCount

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_residualClauseCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_residualClauseCount

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_coreExpandedClauseCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_coreExpandedClauseCount

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_expandedClauseCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportFallbackDecomposition_expandedClauseCount

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecs_eq_some_of_cnf_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecs_eq_some_of_cnf_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecs_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecs_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecs_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecs_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecs_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecs_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecs_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecs_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.ProductionSameSupportFallbackCoreGF2Target' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.ProductionSameSupportFallbackCoreGF2Target

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_sound_coreGF2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_sound_coreGF2

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectChargeFallback_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectChargeFallback_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectChargeFallback_sound_coreGF2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectChargeFallback_sound_coreGF2

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectChargeFallback_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectChargeFallback_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectBlockSizeFallback_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectBlockSizeFallback_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectBlockSizeFallback_sound_coreGF2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectBlockSizeFallback_sound_coreGF2

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectBlockSizeFallback_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectBlockSizeFallback_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectInferredBlockSizeFallback_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectInferredBlockSizeFallback_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectInferredBlockSizeFallback_sound_coreGF2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectInferredBlockSizeFallback_sound_coreGF2

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectInferredBlockSizeFallback_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectInferredBlockSizeFallback_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportDirectRecovery_eq_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportDirectRecovery_eq_some

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSupportGroups_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCanonicalSupportGroups_length

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportMergedSupportRecovery_isSome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportMergedSupportRecovery_isSome

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroup_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroup_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroup_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroup_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroup_sound_coreGF2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroup_sound_coreGF2

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecsPerm_eq_some_of_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecsPerm_eq_some_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecsPerm_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecsPerm_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecsPerm_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParitySpecsPerm_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_sound_coreGF2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_sound_coreGF2

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.sameSupportTwoChargeCandidateSpecs_eq_of_perm_generatedParitySpecs_two_sameSupport' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.sameSupportTwoChargeCandidateSpecs_eq_of_perm_generatedParitySpecs_two_sameSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_two_sameSupport' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_two_sameSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_eq_some_of_perm_generatedParitySpecs_two_sameSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_eq_some_of_perm_generatedParitySpecs_two_sameSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_sameSupport' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupClausesByCanonicalSupport_eq_single_of_perm_generatedParitySpecs_sameSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.parityCandidateCanonicalSupportFromBlock_eq_of_perm_generatedParitySpecs_sameSupport' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.parityCandidateCanonicalSupportFromBlock_eq_of_perm_generatedParitySpecs_sameSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_eq_some_of_perm_generatedParitySpecs_sameSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromGeneratedSpecsPerm_eq_some_of_perm_generatedParitySpecs_sameSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_eq_some_of_perm_supportCharges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_eq_some_of_perm_supportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_perm_supportCharges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_perm_supportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupTwoCharge_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupTwoCharge_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupTwoCharge_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupTwoCharge_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGeneratedParitySpecs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGeneratedParitySpecs

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGeneratedParitySpecsPerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGeneratedParitySpecsPerm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGeneratedParityChargesPerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGeneratedParityChargesPerm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_decomposition_cover_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_decomposition_cover_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverTwoChargeSameSupportGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverTwoChargeSameSupportGroup

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverTwoChargeSameSupportGroupPerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverTwoChargeSameSupportGroupPerm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSingleMergedSupportGroupTwoCharge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSingleMergedSupportGroupTwoCharge

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSingleMergedSupportGroupFromGeneratedSpecsPerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSingleMergedSupportGroupFromGeneratedSpecsPerm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSingleMergedSupportGroupFromChargesPerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSingleMergedSupportGroupFromChargesPerm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGeneratedParityChargeSearchPerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGeneratedParityChargeSearchPerm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSingleMergedSupportGroupFromChargeSearchPerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSingleMergedSupportGroupFromChargeSearchPerm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGroupWithDirectChargeFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGroupWithDirectChargeFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGroupWithDirectBlockSizeFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGroupWithDirectBlockSizeFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGroupWithDirectInferredBlockSizeFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGroupWithDirectInferredBlockSizeFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGroupWithChargeSearchFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGroupWithChargeSearchFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_recoverTwoChargeSameSupportGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_recoverTwoChargeSameSupportGroup

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_recoverTwoChargeSameSupportGroupPerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_recoverTwoChargeSameSupportGroupPerm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_recoverSameSupportGroupWithChargeSearchFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_recoverSameSupportGroupWithChargeSearchFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.sameSupportTwoChargeCandidateSpecs_twoCycle_eq_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.sameSupportTwoChargeCandidateSpecs_twoCycle_eq_generated

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCNF_clausesHaveCandidateSupportVars' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleCNF_clausesHaveCandidateSupportVars

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.sameSupportTwoChargeCandidateSpecs_eq_generated_of_perm_twoCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.sameSupportTwoChargeCandidateSpecs_eq_generated_of_perm_twoCycle

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_eq_some_of_perm_twoCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverTwoChargeSameSupportGroupPerm_eq_some_of_perm_twoCycle

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_twoCycle_eq_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_twoCycle_eq_none

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupClausesByCanonicalSupport_eq_single_of_perm_twoCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupClausesByCanonicalSupport_eq_single_of_perm_twoCycle

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_eq_none_of_perm_twoCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.inferCanonicalParityBlock_eq_none_of_perm_twoCycle

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportUnguidedDirectRecovery_eq_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportUnguidedDirectRecovery_eq_some

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportUnguidedMergedSupportRecovery_isSome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportUnguidedMergedSupportRecovery_isSome

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportUnguidedDirectRecovery_reverse_isSome_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportUnguidedDirectRecovery_reverse_isSome_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportUnguidedPermDirectRecovery_reverse_isSome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportUnguidedPermDirectRecovery_reverse_isSome

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitCanonicalSupportClauseGroupsWithTwoChargeFallback_expandedCNF_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitCanonicalSupportClauseGroupsWithTwoChargeFallback_expandedCNF_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_expandedCNF_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_expandedCNF_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitCanonicalSupportClauseGroupsWithNonexhaustiveFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitCanonicalSupportClauseGroupsWithNonexhaustiveFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitCanonicalSupportClauseGroupsWithNonexhaustiveFallback_expandedCNF_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitCanonicalSupportClauseGroupsWithNonexhaustiveFallback_expandedCNF_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback_expandedCNF_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback_expandedCNF_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback_syntacticSignals_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback_syntacticSignals_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_syntacticSignals_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_syntacticSignals_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.EnhancedExtractorCompleteOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.EnhancedExtractorCompleteOn

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.EnhancedSemanticExtractorCompleteOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.EnhancedSemanticExtractorCompleteOn

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.NonexhaustiveExtractorCompleteOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.NonexhaustiveExtractorCompleteOn

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.NonexhaustiveSemanticExtractorCompleteOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.NonexhaustiveSemanticExtractorCompleteOn

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.nonexhaustiveExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.nonexhaustiveExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitCanonicalSupportClauseGroupsWithTwoChargeFallback_append_of_residual_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitCanonicalSupportClauseGroupsWithTwoChargeFallback_append_of_residual_free

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_append_of_clauseKeysDisjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_append_of_clauseKeysDisjoint

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_append_of_disjointSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_append_of_disjointSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitCanonicalSupportClauseGroupsWithTwoChargeFallback_of_groupsRecognized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.splitCanonicalSupportClauseGroupsWithTwoChargeFallback_of_groupsRecognized

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_groupRecognition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_groupRecognition

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_of_groupAppend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_of_groupAppend

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_of_clauseKeysDisjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_of_clauseKeysDisjoint

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_of_disjointSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_append_of_disjointSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_class

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_of_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_of_class

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_of_groupAppend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_of_groupAppend

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_of_clauseKeysDisjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_of_clauseKeysDisjoint

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_of_disjointSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_append_of_disjointSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithTwoChargeFallback_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroupsWithNonexhaustiveFallback_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_singleGroupTwoChargeFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_singleGroupTwoChargeFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_singleGroupChargeSearchFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_singleGroupChargeSearchFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_singleGroupNonexhaustiveFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_singleGroupNonexhaustiveFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_of_singleGroupNonexhaustiveFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_of_singleGroupNonexhaustiveFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_perm_generatedParitySpecs_two_sameSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_perm_generatedParitySpecs_two_sameSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_exists_of_perm_generatedParitySpecs_sameSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_exists_of_perm_generatedParitySpecs_sameSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_exists_of_perm_generatedParitySpecs_sameSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.nonexhaustiveSemanticExtractorCompleteOn_exists_of_perm_generatedParitySpecs_sameSupport

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle_reversed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle_reversed

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle_of_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_twoCycle_of_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointFamily_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointFamily_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointSpecList_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedKeyDisjointSpecList_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedKeyDisjointSpecList_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCirculant12CNFFormula_of_incidentKeyFresh_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCirculant12CNFFormula_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCirculant12CNFFormula_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedKeyDisjointSpecList_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_of_generatedCanonicalKeyFreshSpecList_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_TseitinCycleCNFFormula_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_expandedCNF_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_expandedCNF_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_coreGF2_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_coreGF2_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_hasEmptyResidual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_hasEmptyResidual

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_coreEquationCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_coreEquationCount

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_residualClauseCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitter_residualClauseCount

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_expandedCNF_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_expandedCNF_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_coreGF2_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_coreGF2_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_hasEmptyResidual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_hasEmptyResidual

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_coreEquationCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_coreEquationCount

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_residualClauseCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCycleSameSupportTwoChargeFallbackSplitterReversed_residualClauseCount

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlocksCNF_perm_of_groupsRecognized' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlocksCNF_perm_of_groupsRecognized

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_canonicalFingerprintRecognizedBlocks_syntacticSignals_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_groupRecognition_syntacticSignals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_groupRecognition_syntacticSignals

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_groupRecognition_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_groupRecognition_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_groupRecognition_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_groupRecognition_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_syntacticSignals_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_groupRecognition_syntacticSignals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_groupRecognition_syntacticSignals

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_groupRecognition_syntacticSignals_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_groupRecognition_syntacticSignals_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_groupRecognition_toSyntacticOk_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_certifiedRecognizedCNF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_certifiedRecognizedCNF

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_certifiedRecognizedCNF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_certifiedRecognizedCNF

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_certifiedRecognizedCNF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_certifiedRecognizedCNF

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_certifiedRecognizedCNF_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_certifiedRecognizedCNF_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_certifiedRecognizedCNF_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_certifiedRecognizedCNF_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_certifiedRecognizedCNF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_certifiedRecognizedCNF

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_certifiedRecognizedCNF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_certifiedRecognizedCNF

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlock_perm_of_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalFingerprintRecognizedBlock_perm_of_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.ClausePermutedRecognizedBlock.toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.ClausePermutedRecognizedBlock.toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_of_singleRecognizedGroup_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_of_singleRecognizedGroup_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_of_perm_clausesForVertex_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_of_perm_clausesForVertex_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_perm_clausesForVertex_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal_of_signal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal_of_signal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_false_normal_of_signal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_false_normal_of_signal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_perm_clausesForVertex_false_normal_of_signal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_perm_clausesForVertex_false_normal_of_signal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_false_normal_of_signal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_false_normal_of_signal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal_of_signal_of_falseMiss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal_of_signal_of_falseMiss

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_true_normal_of_signal_of_falseMiss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_true_normal_of_signal_of_falseMiss

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_perm_clausesForVertex_true_normal_of_signal_of_falseMiss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_perm_clausesForVertex_true_normal_of_signal_of_falseMiss

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_true_normal_of_signal_of_falseMiss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_true_normal_of_signal_of_falseMiss

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_perm_clausesForVertex_false_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_false_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_false_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_perm_clausesForVertex_false_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_perm_clausesForVertex_false_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_false_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_false_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_perm_clausesForVertex_true_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_true_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_perm_clausesForVertex_true_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_perm_clausesForVertex_true_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_perm_clausesForVertex_true_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_true_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_perm_clausesForVertex_true_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.certifiedRecognizedCNF_of_clausePermutedRecognizedBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.certifiedRecognizedCNF_of_clausePermutedRecognizedBlock

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_clausePermutedRecognizedBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_clausePermutedRecognizedBlock

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_clausePermutedRecognizedBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_clausePermutedRecognizedBlock

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_clausePermutedRecognizedBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_clausePermutedRecognizedBlock

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_clausePermutedRecognizedBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_clausePermutedRecognizedBlock

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedBlock

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_append_keyDisjoint_perm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_append_keyDisjoint_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_append_comm_keyDisjoint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_append_comm_keyDisjoint

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_cnf_perm' does not depend on any axioms -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_cnf_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_clausePermutedRecognizedClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_clausePermutedRecognizedClass

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_clausePermutedRecognizedClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.groupsRecognized_exists_of_clausePermutedRecognizedClass

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_empty

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_clausePermutedRecognizedClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_clausePermutedRecognizedClass

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_clausePermutedRecognizedClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_clausePermutedRecognizedClass

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_clausePermutedRecognizedClass_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.extractorCompleteOn_of_clausePermutedRecognizedClass_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_clausePermutedRecognizedClass_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_clausePermutedRecognizedClass_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_empty

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_clausePermutedRecognizedClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_clausePermutedRecognizedClass

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedClass

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_clausePermutedRecognizedClass_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_clausePermutedRecognizedClass_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedClass_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_clausePermutedRecognizedClass_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_perm_clausesForVertex_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_perm_clausesForVertex_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_clausesForVertex_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedBlock_exists_clausesForVertex_normal

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_clausesForVertex_normal_via_clausePermutedRecognizedBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_clausesForVertex_normal_via_clausePermutedRecognizedBlock

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_clausesForVertex_normal_via_clausePermutedRecognizedBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_clausesForVertex_normal_via_clausePermutedRecognizedBlock

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_clausesForVertex_normal_via_clausePermutedRecognizedBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_clausesForVertex_normal_via_clausePermutedRecognizedBlock

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_generatedKeyDisjointFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_generatedKeyDisjointFamily

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_generatedKeyDisjointSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_generatedKeyDisjointSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_generatedCanonicalKeyFreshSpecList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clausePermutedRecognizedClass_of_generatedCanonicalKeyFreshSpecList

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_disjoint_appendGroupRecognition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedExtractorCompleteOn_of_disjoint_appendGroupRecognition

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_singleGroupRecognition_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_singleGroupRecognition_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_singleGroupRecognition_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.enhancedSemanticExtractorCompleteOn_of_singleGroupRecognition_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_singleGroupRecognition_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_singleGroupRecognition_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_disjoint_appendGroupRecognition_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_disjoint_appendGroupRecognition_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_disjoint_appendGroupRecognition_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_disjoint_appendGroupRecognition_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticExtractorCompleteOn_of_disjoint_appendGroupRecognition_toSyntacticOk_append

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.length_le_bind_length_of_forall_exists_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.length_le_bind_length_of_forall_exists_cons

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_length_le_cnf_length_of_vars_ne_empty' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_length_le_cnf_length_of_vars_ne_empty

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.charges_length_le_of_perm_generatedParitySpecsForSupportCharges' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.charges_length_le_of_perm_generatedParitySpecsForSupportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_componentBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_componentBound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_componentBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_componentBound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_exists_of_perm_supportCharges_componentBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_exists_of_perm_supportCharges_componentBound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_exists_class_of_perm_supportCharges_componentBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_exists_class_of_perm_supportCharges_componentBound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_exists_semanticPreservation_of_perm_supportCharges_componentBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_exists_semanticPreservation_of_perm_supportCharges_componentBound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_exists_coreTarget_gf2Equiv_of_perm_supportCharges_componentBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_exists_coreTarget_gf2Equiv_of_perm_supportCharges_componentBound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_exists_certifiedCoreTarget_gf2Equiv_of_perm_supportCharges_componentBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_exists_certifiedCoreTarget_gf2Equiv_of_perm_supportCharges_componentBound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithNonexhaustiveFallback_exists_certifiedCoreTarget_gf2Equiv_of_perm_supportCharges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithNonexhaustiveFallback_exists_certifiedCoreTarget_gf2Equiv_of_perm_supportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithNonexhaustiveFallback_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithNonexhaustiveFallback_sound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithNonexhaustiveFallback_sound_coreGF2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithNonexhaustiveFallback_sound_coreGF2

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithNonexhaustiveFallback_toSyntacticOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithNonexhaustiveFallback_toSyntacticOk

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_eq_some_of_nonexhaustive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_eq_some_of_nonexhaustive

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGroupWithNonexhaustiveFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.class_of_recoverSameSupportGroupWithNonexhaustiveFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_recoverSameSupportGroupWithNonexhaustiveFallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.semanticPreservation_of_recoverSameSupportGroupWithNonexhaustiveFallback

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_eq_map' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_eq_map

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_perm_of_charges_perm' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_perm_of_charges_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_directTargetCharges_supportSize_iff_of_perm_supportCharges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_directTargetCharges_supportSize_iff_of_perm_supportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_directTargetCharges_arityThree_iff_of_perm_supportCharges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_directTargetCharges_arityThree_iff_of_perm_supportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_directTargetCharges_arityFour_iff_of_perm_supportCharges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_directTargetCharges_arityFour_iff_of_perm_supportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_iff_forall_mem' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_iff_forall_mem

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_iff_eraseDups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_iff_eraseDups

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_iff_charge_presence' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.gf2Sat_generatedParitySpecsForSupportCharges_iff_charge_presence

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.not_gf2Sat_generatedParitySpecsForSupportCharges_of_mem_false_true' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.not_gf2Sat_generatedParitySpecsForSupportCharges_of_mem_false_true

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_cnf_length_eq_mul_of_block_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_cnf_length_eq_mul_of_block_length

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_three' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_three

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_four' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsForSupportCharges_cnf_length_of_vars_length_four

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_eq_charge_count_mul_block_length_of_perm_generatedParitySpecsForSupportCharges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_eq_charge_count_mul_block_length_of_perm_generatedParitySpecsForSupportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.charges_length_eq_target_length_div_block_length_of_perm_generatedParitySpecsForSupportCharges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.charges_length_eq_target_length_div_block_length_of_perm_generatedParitySpecsForSupportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_mod_block_length_eq_zero_of_perm_generatedParitySpecsForSupportCharges' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_mod_block_length_eq_zero_of_perm_generatedParitySpecsForSupportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_eq_charge_count_mul_four_of_perm_generatedParitySpecsForSupportCharges' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_eq_charge_count_mul_four_of_perm_generatedParitySpecsForSupportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_eq_charge_count_mul_eight_of_perm_generatedParitySpecsForSupportCharges' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_eq_charge_count_mul_eight_of_perm_generatedParitySpecsForSupportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.charges_length_eq_target_length_div_four_of_perm_generatedParitySpecsForSupportCharges' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.charges_length_eq_target_length_div_four_of_perm_generatedParitySpecsForSupportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_mod_four_eq_zero_of_perm_generatedParitySpecsForSupportCharges' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_mod_four_eq_zero_of_perm_generatedParitySpecsForSupportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.charges_length_eq_target_length_div_eight_of_perm_generatedParitySpecsForSupportCharges' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.charges_length_eq_target_length_div_eight_of_perm_generatedParitySpecsForSupportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_mod_eight_eq_zero_of_perm_generatedParitySpecsForSupportCharges' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.target_length_mod_eight_eq_zero_of_perm_generatedParitySpecsForSupportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_spec_charges_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_spec_charges_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_count_true' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_count_true

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_count_false' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_spec_charges_count_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_mem_canonicalBlockFingerprint_clausesForVertex_iff_charge' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_mem_canonicalBlockFingerprint_clausesForVertex_iff_charge

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_signal_clausesForVertex_eq_charge' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_signal_clausesForVertex_eq_charge

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_false' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.one_le_allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_true' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.one_le_allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_true

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.row_eq_replicate_false_of_canonicalClauseFingerprint_eq_allFalse' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.row_eq_replicate_false_of_canonicalClauseFingerprint_eq_allFalse

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.clause_eq_allFalse_of_mem_clausesForVertex_true_and_fingerprint_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.clause_eq_allFalse_of_mem_clausesForVertex_true_and_fingerprint_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_true_eq_one' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_count_canonicalBlockFingerprint_clausesForVertex_true_eq_one

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_forSupportCharges_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_forSupportCharges_cons

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_mem_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges_iff_true_mem' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_mem_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges_iff_true_mem

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_mem_targetFingerprint_iff_true_mem_of_perm_supportCharges' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_mem_targetFingerprint_iff_true_mem_of_perm_supportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_count_true_le_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_count_true_le_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_count_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges_eq_true_count' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_count_canonicalBlockFingerprint_generatedParitySpecsCNF_forSupportCharges_eq_true_count

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_count_true_le_targetFingerprint_of_perm_supportCharges' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_count_true_le_targetFingerprint_of_perm_supportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_count_targetFingerprint_eq_true_count_of_perm_supportCharges' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.allFalseClauseFingerprint_count_targetFingerprint_eq_true_count_of_perm_supportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalSupportChargesFromCounts_count_true' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalSupportChargesFromCounts_count_true

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalSupportChargesFromCounts_count_false' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalSupportChargesFromCounts_count_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.bool_count_false_eq_length_sub_count_true' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.bool_count_false_eq_length_sub_count_true

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalSupportChargesFromCounts_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalSupportChargesFromCounts_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_forSupportCharges_perm_of_charges_perm' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsCNF_forSupportCharges_perm_of_charges_perm

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_of_block_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_of_block_length

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_supportSize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_supportSize

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_arityThree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_arityThree

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_arityFour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.directSameSupportChargesFromTargetWithBlockSize_perm_of_perm_supportCharges_arityFour

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_arityThree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_arityThree

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_arityFour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_arityFour

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_directTargetCharges_arityThree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_directTargetCharges_arityThree

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_directTargetCharges_arityFour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_directTargetCharges_arityFour

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_of_block_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargesPerm_eq_some_of_directTargetCharges_of_block_length

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_directTargetCharges_of_block_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargesPerm_eq_some_of_directTargetCharges_of_block_length

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectBlockSizeFallback_eq_some_of_directTargetCharges_of_block_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectBlockSizeFallback_eq_some_of_directTargetCharges_of_block_length

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectInferredBlockSizeFallback_eq_some_of_directTargetCharges_supportSize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectInferredBlockSizeFallback_eq_some_of_directTargetCharges_supportSize

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectInferredBlockSizeFallback_eq_some_gf2Equiv_of_perm_supportCharges_supportSize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectInferredBlockSizeFallback_eq_some_gf2Equiv_of_perm_supportCharges_supportSize

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectChargeFallback_eq_some_of_directTargetCharges_arityThree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectChargeFallback_eq_some_of_directTargetCharges_arityThree

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectChargeFallback_eq_some_of_directTargetCharges_arityFour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithDirectChargeFallback_eq_some_of_directTargetCharges_arityFour

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_eq_some_of_directTargetCharges_arityThree_of_twoCharge_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_eq_some_of_directTargetCharges_arityThree_of_twoCharge_none

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_eq_some_of_directTargetCharges_arityFour_of_twoCharge_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_eq_some_of_directTargetCharges_arityFour_of_twoCharge_none

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_certifiedDirectArityThree_gf2Equiv_of_perm_supportCharges_of_twoCharge_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_certifiedDirectArityThree_gf2Equiv_of_perm_supportCharges_of_twoCharge_none

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_certifiedDirectArityFour_gf2Equiv_of_perm_supportCharges_of_twoCharge_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_certifiedDirectArityFour_gf2Equiv_of_perm_supportCharges_of_twoCharge_none

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_eq_some_of_directTargetCharges_supportSize_of_twoCharge_none_of_directCharge_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_eq_some_of_directTargetCharges_supportSize_of_twoCharge_none_of_directCharge_none

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_certifiedDirectInferred_gf2Equiv_of_perm_supportCharges_of_twoCharge_none_of_directCharge_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_certifiedDirectInferred_gf2Equiv_of_perm_supportCharges_of_twoCharge_none_of_directCharge_none

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_eq_nonexhaustive_of_perm_supportCharges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_eq_nonexhaustive_of_perm_supportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_eq_nonexhaustiveFallback_of_perm_supportCharges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGroupWithChargeSearchFallback_eq_nonexhaustiveFallback_of_perm_supportCharges

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_allFalseFingerprint_signals_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_allFalseFingerprint_signals_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_allFalseFingerprint_count_true' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_allFalseFingerprint_count_true

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_allFalseFingerprint_count_false' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.canonicalBlocksFromGeneratedParitySpecs_forSupportCharges_allFalseFingerprint_count_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_rhs_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_rhs_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_rhs_count_true' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_rhs_count_true

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_rhs_count_false' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsGF2_forSupportCharges_rhs_count_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_coreGF2_rhs_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_coreGF2_rhs_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_coreGF2_rhs_count_true' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_coreGF2_rhs_count_true

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_coreGF2_rhs_count_false' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_coreGF2_rhs_count_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_block_charges_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_block_charges_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_block_charges_count_true' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_block_charges_count_true

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_block_charges_count_false' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_block_charges_count_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_allFalseFingerprint_signals_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_allFalseFingerprint_signals_eq

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_allFalseFingerprint_count_true' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_allFalseFingerprint_count_true

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_allFalseFingerprint_count_false' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.generatedParitySpecsFallbackDecomposition_forSupportCharges_allFalseFingerprint_count_false

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_arityThreeExactBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_arityThreeExactBound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_arityThreeExactBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_arityThreeExactBound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_arityFourExactBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSameSupportGeneratedParityChargeSearchPerm_exists_of_perm_supportCharges_arityFourExactBound

/-- info: 'CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_arityFourExactBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.AtomicClassBridge.recoverSingleMergedSupportGroupFromChargeSearchPerm_exists_of_perm_supportCharges_arityFourExactBound

/-!
## M-A3 concrete extractor-completeness instances

The `Lean.ofReduceBool` axiom below is introduced by `native_decide`, used to
verify (over the concrete, finite Tseitin formula) that the executable
canonical-fingerprint splitter recognizes every clause group residual-free.
This is an honest, expected dependency for compiled decision procedures.
-/

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_threeCycle' depends on axioms: [propext,
 Lean.ofReduceBool,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_threeCycle

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_fourCycle' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_fourCycle

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_threeCycle' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_threeCycle

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_fourCycle' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_fourCycle

-- M-A5: uniform cycle family extractor completeness (n = 5, 6).
/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_cycle5' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_cycle5

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_cycle6' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.extractorCompleteOn_cycle6

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_cycle5' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_cycle5

/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_cycle6' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.semanticExtractorCompleteOn_cycle6

-- Uniform extractor completeness for all n >= 3. NOTE: this is a thin restatement, NOT a new
-- theorem. Its proof wraps the PRE-EXISTING general structural theorem
-- `extractorCompleteOn_TseitinCycleCNFFormula_nonDegenerate` (committed 6783d8a, 2026-06-12).
-- The general result is genuine and axiom-clean ([propext, Classical.choice, Quot.sound], no
-- native_decide); the "uniform" name only re-exposes it. See INTEGRITY-CLAIMS.md.
/-- info: 'CertifiedAffine.TseitinCNFData.ExtractorCompleteness.uniformCycleExtractorCompleteness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.ExtractorCompleteness.uniformCycleExtractorCompleteness
