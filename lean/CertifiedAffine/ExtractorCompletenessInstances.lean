import CertifiedAffine.ExtractorCompleteness
import CertifiedAffine.AtomicClassBridge

/-!
# Concrete Extractor-Completeness Instances

This module discharges a concrete end-to-end instance of milestone M-A3: it
exhibits genuinely-true `ExtractorCompleteOn` statements for the concrete
three-cycle and four-cycle Tseitin parity CNFs.

The scaffold lemmas in `ExtractorCompleteness.lean` reduce extractor
completeness to two facts: the support grouping returns recognized groups, and
those groups split residual-free.  Here we cash that out concretely.  For each
family `F` the GF(2) target is taken to be the *actual* extracted output
`canonicalFingerprintRecognizedBlocksGF2 (split F).blocks`, so the permutation
side of `ExtractorCompleteOn` is reflexivity.  The non-vacuous content is the
residual-free split equation `split F = { blocks := ..., residualCNF := [] }`,
which holds only because the executable extractor genuinely recognizes *every*
clause group of the family as a canonical parity block (verified by
`native_decide` over the concrete, finite formula).
-/

namespace CertifiedAffine
namespace TseitinCNFData
namespace ExtractorCompleteness

/--
Decidability of the executable `toSyntactic?` block check, recursing on the
block list exactly as `CanonicalBlocksToSyntacticOk` does.  This lets the
concrete instances discharge the syntactic-recognition premise by `decide` /
`native_decide` over the finite emitted block list.
-/
instance decidableCanonicalBlocksToSyntacticOk {m : Nat} :
    (blocks : List (CanonicalFingerprintRecognizedParityBlock m)) ->
      Decidable (AtomicClassBridge.CanonicalBlocksToSyntacticOk blocks)
  | [] => by
      unfold AtomicClassBridge.CanonicalBlocksToSyntacticOk
      exact isTrue True.intro
  | b :: blocks => by
      unfold AtomicClassBridge.CanonicalBlocksToSyntacticOk
      have : Decidable (AtomicClassBridge.CanonicalBlocksToSyntacticOk blocks) :=
        decidableCanonicalBlocksToSyntacticOk blocks
      exact inferInstanceAs (Decidable (_ ∧ _))

/--
Generic concrete instance builder: if the executable splitter leaves no
residual CNF on `f` (a decidable, finite fact), then `ExtractorCompleteOn`
holds for the actually-extracted GF(2) output.

This is non-vacuous: the conclusion's witness blocks are exactly the splitter's
output blocks, and the split equality forces `residualCNF = []`, i.e. every
canonical support group of `f` was recognized as a parity block.
-/
theorem extractorCompleteOn_of_residualFree
    {m : Nat} (f : CNFModel.CNF m)
    (hresidual : (splitArityFourParityCanonicalSupportGroups f).residualCNF = []) :
    ExtractorCompleteOn f
      (canonicalFingerprintRecognizedBlocksGF2
        (splitArityFourParityCanonicalSupportGroups f).blocks) := by
  refine Exists.intro (splitArityFourParityCanonicalSupportGroups f).blocks ?_
  refine And.intro ?_ (List.Perm.refl _)
  -- Rebuild the decomposition record from its fields; the residual field is `[]`.
  calc
    splitArityFourParityCanonicalSupportGroups f
        = { blocks := (splitArityFourParityCanonicalSupportGroups f).blocks
            residualCNF := (splitArityFourParityCanonicalSupportGroups f).residualCNF } := rfl
    _ = { blocks := (splitArityFourParityCanonicalSupportGroups f).blocks
          residualCNF := [] } := by rw [hresidual]

/-- The concrete extracted GF(2) target for the three-cycle Tseitin CNF. -/
def threeCycleGF2Target : ParityEncoded.GF2Formula threeCycleGraph.m :=
  canonicalFingerprintRecognizedBlocksGF2
    (splitArityFourParityCanonicalSupportGroups TseitinCNFFormulaThreeCycleCharge).blocks

/-- The concrete extracted GF(2) target for the four-cycle Tseitin CNF. -/
def fourCycleGF2Target : ParityEncoded.GF2Formula fourCycleGraph.m :=
  canonicalFingerprintRecognizedBlocksGF2
    (splitArityFourParityCanonicalSupportGroups TseitinCNFFormulaFourCycleCharge).blocks

/--
Concrete extractor completeness for the three-cycle Tseitin parity CNF.

The executable canonical-fingerprint splitter recognizes the whole three-cycle
Tseitin family residual-free, returning the GF(2) blocks `threeCycleGF2Target`.
-/
theorem extractorCompleteOn_threeCycle :
    ExtractorCompleteOn TseitinCNFFormulaThreeCycleCharge threeCycleGF2Target :=
  extractorCompleteOn_of_residualFree TseitinCNFFormulaThreeCycleCharge (by native_decide)

/--
Concrete extractor completeness for the four-cycle Tseitin parity CNF.

The executable canonical-fingerprint splitter recognizes the whole four-cycle
Tseitin family residual-free, returning the GF(2) blocks `fourCycleGF2Target`.
-/
theorem extractorCompleteOn_fourCycle :
    ExtractorCompleteOn TseitinCNFFormulaFourCycleCharge fourCycleGF2Target :=
  extractorCompleteOn_of_residualFree TseitinCNFFormulaFourCycleCharge (by native_decide)

/--
The residual-free split equality, packaged so that the emitted block list is
literally `(split f).blocks`.  This is the `hsplit` premise expected by the
`AtomicClassBridge` split-to-class lemmas.
-/
theorem split_eq_blocks_residualFree
    {m : Nat} (f : CNFModel.CNF m)
    (hresidual : (splitArityFourParityCanonicalSupportGroups f).residualCNF = []) :
    splitArityFourParityCanonicalSupportGroups f =
      { blocks := (splitArityFourParityCanonicalSupportGroups f).blocks
        residualCNF := [] } := by
  calc
    splitArityFourParityCanonicalSupportGroups f
        = { blocks := (splitArityFourParityCanonicalSupportGroups f).blocks
            residualCNF := (splitArityFourParityCanonicalSupportGroups f).residualCNF } := rfl
    _ = { blocks := (splitArityFourParityCanonicalSupportGroups f).blocks
          residualCNF := [] } := by rw [hresidual]

/--
Semantic + executable extractor completeness for the three-cycle Tseitin parity
CNF.  Both the per-assignment CNF/GF(2) equivalence and the residual-free
executable extraction are proven; the semantic half is obtained through the
`AtomicClassBridge` split-to-class bridge, whose syntactic-recognition premise
is discharged by the executable `toSyntactic?` check on the emitted blocks.
-/
theorem semanticExtractorCompleteOn_threeCycle :
    SemanticExtractorCompleteOn TseitinCNFFormulaThreeCycleCharge threeCycleGF2Target := by
  have hresidual :
      (splitArityFourParityCanonicalSupportGroups
        TseitinCNFFormulaThreeCycleCharge).residualCNF = [] := by native_decide
  have hsplit :
      splitArityFourParityCanonicalSupportGroups TseitinCNFFormulaThreeCycleCharge =
        { blocks :=
            (splitArityFourParityCanonicalSupportGroups
              TseitinCNFFormulaThreeCycleCharge).blocks
          residualCNF := [] } :=
    split_eq_blocks_residualFree _ hresidual
  have hsyntactic :
      AtomicClassBridge.CanonicalBlocksToSyntacticOk
        (splitArityFourParityCanonicalSupportGroups
          TseitinCNFFormulaThreeCycleCharge).blocks := by native_decide
  have hclass :
      ParityEncoded.Class threeCycleGraph.m
        TseitinCNFFormulaThreeCycleCharge threeCycleGF2Target :=
    AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append
      hsplit hsyntactic
  exact semanticExtractorCompleteOn_of_class hclass extractorCompleteOn_threeCycle

/--
Semantic + executable extractor completeness for the four-cycle Tseitin parity
CNF, by the same split-to-class bridge.
-/
theorem semanticExtractorCompleteOn_fourCycle :
    SemanticExtractorCompleteOn TseitinCNFFormulaFourCycleCharge fourCycleGF2Target := by
  have hresidual :
      (splitArityFourParityCanonicalSupportGroups
        TseitinCNFFormulaFourCycleCharge).residualCNF = [] := by native_decide
  have hsplit :
      splitArityFourParityCanonicalSupportGroups TseitinCNFFormulaFourCycleCharge =
        { blocks :=
            (splitArityFourParityCanonicalSupportGroups
              TseitinCNFFormulaFourCycleCharge).blocks
          residualCNF := [] } :=
    split_eq_blocks_residualFree _ hresidual
  have hsyntactic :
      AtomicClassBridge.CanonicalBlocksToSyntacticOk
        (splitArityFourParityCanonicalSupportGroups
          TseitinCNFFormulaFourCycleCharge).blocks := by native_decide
  have hclass :
      ParityEncoded.Class fourCycleGraph.m
        TseitinCNFFormulaFourCycleCharge fourCycleGF2Target :=
    AtomicClassBridge.class_of_splitArityFourParityCanonicalSupportGroups_toSyntacticOk_append
      hsplit hsyntactic
  exact semanticExtractorCompleteOn_of_class hclass extractorCompleteOn_fourCycle

end ExtractorCompleteness
end TseitinCNFData
end CertifiedAffine
