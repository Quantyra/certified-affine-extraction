import CertifiedAffine.ExtractorCompletenessInstances

/-!
# Extractor completeness across the uniform cycle family (M-A5)

`ExtractorCompletenessInstances.lean` (v0.2.0) proved concrete extractor completeness for the
three- and four-cycle Tseitin CNFs. This module extends that coverage along the *uniform* directed
cycle family `TseitinCycleCNFFormula n hn` (the same family underlying
`TseitinCycleGF2NormalizationSurface`), proving residual-free executable + semantic completeness for
`n = 5` and `n = 6`, and stating the general uniform claim as an explicitly **OPEN** target.

Computationally the executable splitter is residual-free on this family for `n = 3,4,5,6` (each
yielding `n` parity blocks); `n = 2` is degenerate and not residual-free. The instances below cover
`n = 5, 6`; a single general proof for all `n >= 3` is the open milestone `UniformCycleExtractorCompleteness`.

NON-CLAIMS: scoped certified extraction for the Tseitin cycle family. No P=NP, no general SAT/CNF-to-XOR.
-/

namespace CertifiedAffine
namespace TseitinCNFData
namespace ExtractorCompleteness

/-- The extracted GF(2) target for the uniform directed-cycle Tseitin CNF at size `n`. -/
def cycleGF2Target (n : Nat) (hn : 1 < n) :
    ParityEncoded.GF2Formula
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived n hn)).m :=
  canonicalFingerprintRecognizedBlocksGF2
    (splitArityFourParityCanonicalSupportGroups (TseitinCycleCNFFormula n hn)).blocks

/-- Extractor completeness for the five-cycle Tseitin CNF (uniform family, n = 5). -/
theorem extractorCompleteOn_cycle5 :
    ExtractorCompleteOn (TseitinCycleCNFFormula 5 (by decide)) (cycleGF2Target 5 (by decide)) :=
  extractorCompleteOn_of_residualFree (TseitinCycleCNFFormula 5 (by decide)) (by native_decide)

/-- Extractor completeness for the six-cycle Tseitin CNF (uniform family, n = 6). -/
theorem extractorCompleteOn_cycle6 :
    ExtractorCompleteOn (TseitinCycleCNFFormula 6 (by decide)) (cycleGF2Target 6 (by decide)) :=
  extractorCompleteOn_of_residualFree (TseitinCycleCNFFormula 6 (by decide)) (by native_decide)

/-- Semantic + executable extractor completeness for the five-cycle Tseitin CNF. -/
theorem semanticExtractorCompleteOn_cycle5 :
    SemanticExtractorCompleteOn (TseitinCycleCNFFormula 5 (by decide)) (cycleGF2Target 5 (by decide)) := by
  have hresidual :
      (splitArityFourParityCanonicalSupportGroups (TseitinCycleCNFFormula 5 (by decide))).residualCNF = [] := by
    native_decide
  have hsplit :
      splitArityFourParityCanonicalSupportGroups (TseitinCycleCNFFormula 5 (by decide)) =
        { blocks := (splitArityFourParityCanonicalSupportGroups (TseitinCycleCNFFormula 5 (by decide))).blocks
          residualCNF := [] } :=
    split_eq_blocks_residualFree _ hresidual
  have hsyntactic :
      AtomicClassBridge.CanonicalBlocksToSyntacticOk
        (splitArityFourParityCanonicalSupportGroups (TseitinCycleCNFFormula 5 (by decide))).blocks := by
    native_decide
  have hclass :=
    AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append
      hsplit hsyntactic
  exact semanticExtractorCompleteOn_of_class hclass extractorCompleteOn_cycle5

/-- Semantic + executable extractor completeness for the six-cycle Tseitin CNF. -/
theorem semanticExtractorCompleteOn_cycle6 :
    SemanticExtractorCompleteOn (TseitinCycleCNFFormula 6 (by decide)) (cycleGF2Target 6 (by decide)) := by
  have hresidual :
      (splitArityFourParityCanonicalSupportGroups (TseitinCycleCNFFormula 6 (by decide))).residualCNF = [] := by
    native_decide
  have hsplit :
      splitArityFourParityCanonicalSupportGroups (TseitinCycleCNFFormula 6 (by decide)) =
        { blocks := (splitArityFourParityCanonicalSupportGroups (TseitinCycleCNFFormula 6 (by decide))).blocks
          residualCNF := [] } :=
    split_eq_blocks_residualFree _ hresidual
  have hsyntactic :
      AtomicClassBridge.CanonicalBlocksToSyntacticOk
        (splitArityFourParityCanonicalSupportGroups (TseitinCycleCNFFormula 6 (by decide))).blocks := by
    native_decide
  have hclass :=
    AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append
      hsplit hsyntactic
  exact semanticExtractorCompleteOn_of_class hclass extractorCompleteOn_cycle6

/--
OPEN MILESTONE (not proven): uniform extractor completeness for the directed-cycle Tseitin family.

For every cycle size `n >= 3`, the executable canonical-fingerprint splitter recognizes the uniform
Tseitin cycle CNF residual-free and returns its GF(2) parity equations. This holds computationally
for `n = 3,4,5,6` (the concrete instances), but a single general proof for all `n >= 3` requires a
structural/inductive argument about the splitter on the general cycle encoding and is OPEN. This
`def` records the statement; it is deliberately left unproven.
-/
def UniformCycleExtractorCompleteness : Prop :=
  ∀ (n : Nat) (hn : 1 < n), 3 ≤ n →
    ExtractorCompleteOn (TseitinCycleCNFFormula n hn) (cycleGF2Target n hn)

end ExtractorCompleteness
end TseitinCNFData
end CertifiedAffine
