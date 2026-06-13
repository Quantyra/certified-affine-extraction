import CertifiedAffine.TseitinCNFData

/-!
# Canonical Extractor Frame Probe

This module is an internal executable probe for the canonical fingerprint
splitter. It tests the frame property that motivated the next theorem lane:
adding a disjoint-support CNF should not change the recognized blocks that live
on the original support, except for block ordering.

The checks are intentionally not part of `Audit.lean`; they are executable
regression tests for the older canonical extractor scaffold.
-/

namespace CertifiedAffine
namespace TseitinCNFData

namespace FrameProbe

abbrev M : Nat := 32

def mPos : 0 < M := by decide

def finMod (i : Nat) : Fin M :=
  { val := i % M, isLt := Nat.mod_lt i mPos }

def varsAt (offset : Nat) : List (Fin M) :=
  [ finMod offset
  , finMod (offset + 1)
  , finMod (offset + 2)
  , finMod (offset + 3) ]

def rotateLeft {a : Type} : List a -> List a
  | [] => []
  | x :: xs => xs ++ [x]

def variantCNF (variant : Nat) (f : CNFModel.CNF M) : CNFModel.CNF M :=
  match variant % 4 with
  | 0 => f
  | 1 => reverseClauseLiterals f
  | 2 => f.reverse
  | _ => rotateLeft (reverseClauseLiterals f)

structure BlockSpec where
  offset : Nat
  charge : Bool
  variant : Nat

def blockCNF (spec : BlockSpec) : CNFModel.CNF M :=
  variantCNF spec.variant (clausesForVertex (varsAt spec.offset) spec.charge)

def formulaCNF (specs : List BlockSpec) : CNFModel.CNF M :=
  specs.bind blockCNF

def cnfSupport (f : CNFModel.CNF M) : List Nat :=
  sortNatFingerprintAtoms
    ((f.bind (fun c => c.map (fun l => l.var.val))).eraseDups)

def blockOnSupport (support : List Nat)
    (b : CanonicalFingerprintRecognizedParityBlock M) : Bool :=
  b.spec.vars.all (fun v => support.contains v.val)

def blocksOnSupport (support : List Nat)
    (blocks : List (CanonicalFingerprintRecognizedParityBlock M)) :
    List (CanonicalFingerprintRecognizedParityBlock M) :=
  blocks.filter (blockOnSupport support)

def blockKey (b : CanonicalFingerprintRecognizedParityBlock M) : List Nat :=
  let sep0 := 4 * M + 1
  let sep1 := 4 * M + 2
  let sep2 := 4 * M + 3
  let chargeAtom := if b.spec.charge then 1 else 0
  [chargeAtom, sep0] ++
    ((sortFinByVal b.spec.vars).map (fun v => v.val)) ++
    [sep1] ++
    ((canonicalBlockFingerprint b.blockCNF).bind (fun row => row ++ [sep2]))

def sortedBlockKeys
    (blocks : List (CanonicalFingerprintRecognizedParityBlock M)) :
    List (List Nat) :=
  sortClauseFingerprints (blocks.map blockKey)

def sameBlocksUpToOrder
    (lhs rhs : List (CanonicalFingerprintRecognizedParityBlock M)) : Bool :=
  decide (sortedBlockKeys lhs = sortedBlockKeys rhs)

def extract (f : CNFModel.CNF M) :
    CanonicalFingerprintGF2Decomposition M :=
  splitArityFourParityCanonicalSupportGroups f

def frameProbeHolds (F G : CNFModel.CNF M) : Bool :=
  let left := (extract F).blocks
  let framed := (extract (F ++ G)).blocks
  sameBlocksUpToOrder (blocksOnSupport (cnfSupport F) framed) left

def extractSameBlocksUpToOrder (F G : CNFModel.CNF M) : Bool :=
  sameBlocksUpToOrder (extract F).blocks (extract G).blocks

def spec (offset : Nat) (charge : Bool) (variant : Nat) : BlockSpec :=
  { offset := offset, charge := charge, variant := variant }

def generatedCase (i : Nat) : Prod (CNFModel.CNF M) (CNFModel.CNF M) :=
  let f0 := spec 0 (decide (i % 2 = 0)) i
  let f1 := spec 8 (decide (i % 3 = 0)) (i + 1)
  let g0 := spec 4 (decide (i % 5 = 0)) (i + 2)
  let g1 := spec 12 (decide (i % 7 = 0)) (i + 3)
  let Fspecs := if i % 3 = 1 then [f0] else [f0, f1]
  let Gspecs := if i % 4 = 2 then [g0] else [g0, g1]
  (formulaCNF Fspecs, formulaCNF Gspecs)

def generatedCases : List (Prod (CNFModel.CNF M) (CNFModel.CNF M)) :=
  (List.range 32).map generatedCase

def generatedCaseResults : List Bool :=
  generatedCases.map (fun pair => frameProbeHolds pair.1 pair.2)

def generatedSuitePass : Bool :=
  generatedCaseResults.all id

theorem generatedSuitePass_eq_true : generatedSuitePass = true := by
  native_decide

/--
Positive control: the canonical splitter keeps the left blocks stable under
disjoint-support framing on this generated suite.
-/
def positiveControlSummary : Prod Nat Nat :=
  ((generatedCaseResults.filter id).length, generatedCaseResults.length)

def globalPermutationFormula (i : Nat) : CNFModel.CNF M :=
  let f0 := spec 0 (decide (i % 2 = 0)) i
  let f1 := spec 4 (decide (i % 3 = 0)) (i + 1)
  let f2 := spec 8 (decide (i % 5 = 0)) (i + 2)
  let f3 := spec 12 (decide (i % 7 = 0)) (i + 3)
  let specs :=
    match i % 4 with
    | 0 => [f0, f1, f2]
    | 1 => [f1, f0, f3]
    | 2 => [f2, f3, f0, f1]
    | _ => [f3, f1, f2]
  formulaCNF specs

def globalPermutationProbeHolds (i variant : Nat) : Bool :=
  let f := globalPermutationFormula i
  extractSameBlocksUpToOrder f (variantCNF variant f)

def globalPermutationCaseResults : List Bool :=
  (List.range 32).bind (fun i =>
    (List.range 4).map (fun variant =>
      globalPermutationProbeHolds i variant))

def globalPermutationSuitePass : Bool :=
  globalPermutationCaseResults.all id

theorem globalPermutationSuitePass_eq_true :
    globalPermutationSuitePass = true := by
  native_decide

/--
Diagnostic for the next proof gate: the current generated suite is stable under
whole-CNF clause/literal permutation, up to extracted block ordering.
-/
def globalPermutationSummary : Prod Nat Nat :=
  ((globalPermutationCaseResults.filter id).length,
    globalPermutationCaseResults.length)

/--
Generated parity blocks are deliberately collision-heavy for support-key
grouping: every clause in one block mentions the same variables.  This probe
checks that such a block really collapses to one support key.
-/
def supportKeyCollisionHolds (i : Nat) : Bool :=
  let f :=
    clausesForVertex (varsAt (4 * (i % 4)))
      (decide (i % 2 = 0))
  match f with
  | [] => false
  | c :: _ =>
      f.all (fun d =>
        decide (canonicalClauseSupportKey d = canonicalClauseSupportKey c))

/--
Collision-heavy canonicalization precondition check: even when the support key
is identical for every clause in the block, the full-content block fingerprint
is syntactically stable under deterministic clause/literal permutations.
-/
def supportCollisionCanonicalizationProbeHolds
    (i variant : Nat) : Bool :=
  let f :=
    clausesForVertex (varsAt (4 * (i % 4)))
      (decide (i % 2 = 0))
  supportKeyCollisionHolds i &&
    decide
      (canonicalBlockFingerprint (variantCNF variant f) =
        canonicalBlockFingerprint f)

def supportCollisionCanonicalizationCaseResults : List Bool :=
  (List.range 32).bind (fun i =>
    (List.range 4).map (fun variant =>
      supportCollisionCanonicalizationProbeHolds i variant))

def supportCollisionCanonicalizationSuitePass : Bool :=
  supportCollisionCanonicalizationCaseResults.all id

theorem supportCollisionCanonicalizationSuitePass_eq_true :
    supportCollisionCanonicalizationSuitePass = true := by
  native_decide

/--
Diagnostic summary for the support-collision canonicalization precondition
check.
-/
def supportCollisionCanonicalizationSummary : Prod Nat Nat :=
  ((supportCollisionCanonicalizationCaseResults.filter id).length,
    supportCollisionCanonicalizationCaseResults.length)

end FrameProbe
end TseitinCNFData
end CertifiedAffine
